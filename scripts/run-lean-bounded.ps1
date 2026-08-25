param(
    [Parameter(Mandatory = $true)]
    [string] $File,

    [Parameter(Mandatory = $true)]
    [Alias("LakeProject")]
    [string] $DependencyProject,

    [string] $LeanExecutable = "",

    [ValidateRange(1, 10)]
    [double] $MaxMemoryGiB = 8,

    [string] $LogDirectory = ""
)

$ErrorActionPreference = "Stop"

function Get-FileFingerprint([string] $Path) {
    $item = Get-Item -LiteralPath $Path
    return [ordered]@{
        bytes = [int64] $item.Length
        sha256 = (Get-FileHash -LiteralPath $item.FullName -Algorithm SHA256).Hash
    }
}

function Test-FingerprintEqual($Left, $Right) {
    return $Left.bytes -eq $Right.bytes -and $Left.sha256 -eq $Right.sha256
}

function Get-NormalizedToolchain([string] $Path) {
    return (Get-Content -LiteralPath $Path -Raw).Trim()
}

function Get-MathlibPin([string] $ManifestPath) {
    $manifest = Get-Content -LiteralPath $ManifestPath -Raw | ConvertFrom-Json
    $matches = @($manifest.packages | Where-Object { $_.name -eq "mathlib" })
    if ($matches.Count -ne 1) {
        throw "Expected exactly one mathlib package in $ManifestPath; found $($matches.Count)."
    }
    $mathlib = $matches[0]
    return [ordered]@{
        url = [string] $mathlib.url
        input_rev = [string] $mathlib.inputRev
        resolved_rev = [string] $mathlib.rev
    }
}

function Test-MathlibPinEqual($Left, $Right) {
    return $Left.url -eq $Right.url -and
        $Left.input_rev -eq $Right.input_rev -and
        $Left.resolved_rev -eq $Right.resolved_rev
}

function Get-PortableRelativePath([string] $BasePath, [string] $TargetPath) {
    return [IO.Path]::GetRelativePath($BasePath, $TargetPath).Replace('\', '/')
}

function Get-ProcessTreeSnapshot([int] $RootProcessId) {
    $rows = @(Get-CimInstance Win32_Process | Select-Object ProcessId, ParentProcessId)
    $depths = [Collections.Generic.Dictionary[int, int]]::new()
    $depths[$RootProcessId] = 0
    $changed = $true
    while ($changed) {
        $changed = $false
        foreach ($row in $rows) {
            $parentId = [int] $row.ParentProcessId
            $processId = [int] $row.ProcessId
            if ($depths.ContainsKey($parentId) -and -not $depths.ContainsKey($processId)) {
                $depths[$processId] = $depths[$parentId] + 1
                $changed = $true
            }
        }
    }
    return @($depths.GetEnumerator() | ForEach-Object {
        [pscustomobject]@{
            ProcessId = [int] $_.Key
            Depth = [int] $_.Value
        }
    })
}

function Stop-CapturedProcessTree([object[]] $Snapshot, [int] $RootProcessId) {
    $descendants = @($Snapshot | Where-Object { $_.ProcessId -ne $RootProcessId } |
        Sort-Object Depth -Descending)
    foreach ($node in $descendants) {
        Stop-Process -Id $node.ProcessId -Force -ErrorAction SilentlyContinue
    }
    Stop-Process -Id $RootProcessId -Force -ErrorAction SilentlyContinue
}

$sourceRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot "..")).Path
$runnerPath = (Resolve-Path -LiteralPath $PSCommandPath).Path
$resolvedFile = (Resolve-Path -LiteralPath $File).Path
$resolvedDependencyProject = (Resolve-Path -LiteralPath $DependencyProject).Path

$repositoryToolchainPath = (Resolve-Path -LiteralPath (Join-Path $sourceRoot "lean-toolchain")).Path
$repositoryManifestPath = (Resolve-Path -LiteralPath (Join-Path $sourceRoot "lake-manifest.json")).Path
$dependencyToolchainPath = (Resolve-Path -LiteralPath (Join-Path $resolvedDependencyProject "lean-toolchain")).Path
$dependencyManifestPath = (Resolve-Path -LiteralPath (Join-Path $resolvedDependencyProject "lake-manifest.json")).Path

$repositoryToolchainValue = Get-NormalizedToolchain $repositoryToolchainPath
$dependencyToolchainValue = Get-NormalizedToolchain $dependencyToolchainPath
$toolchainsMatch = $repositoryToolchainValue -eq $dependencyToolchainValue
if (-not $toolchainsMatch) {
    throw "Repository and dependency-project toolchains do not match after normalization."
}

$repositoryMathlibPin = Get-MathlibPin $repositoryManifestPath
$dependencyMathlibPin = Get-MathlibPin $dependencyManifestPath
$mathlibPinsMatch = Test-MathlibPinEqual $repositoryMathlibPin $dependencyMathlibPin
if (-not $mathlibPinsMatch) {
    throw "Repository and dependency-project Mathlib pins do not match."
}

if ([string]::IsNullOrWhiteSpace($LeanExecutable)) {
    $toolchainDirectory = $repositoryToolchainValue.Replace("/", "--").Replace(":", "---")
    $LeanExecutable = Join-Path $env:USERPROFILE ".elan\toolchains\$toolchainDirectory\bin\lean.exe"
}
$resolvedLeanExecutable = (Resolve-Path -LiteralPath $LeanExecutable).Path
$toolchainRoot = (Resolve-Path -LiteralPath (Join-Path (Split-Path $resolvedLeanExecutable) "..")).Path

$leanPathEntries = [Collections.Generic.List[string]]::new()
$leanPathEntries.Add($sourceRoot)

$packagesRoot = Join-Path $resolvedDependencyProject ".lake\packages"
if (-not (Test-Path -LiteralPath $packagesRoot -PathType Container)) {
    throw "Dependency package cache not found: $packagesRoot"
}
foreach ($package in Get-ChildItem -LiteralPath $packagesRoot -Directory | Sort-Object Name) {
    $packageLeanLib = Join-Path $package.FullName ".lake\build\lib\lean"
    if (Test-Path -LiteralPath $packageLeanLib -PathType Container) {
        $leanPathEntries.Add((Resolve-Path -LiteralPath $packageLeanLib).Path)
    }
}

$mathlibLeanLib = Join-Path $packagesRoot "mathlib\.lake\build\lib\lean"
if (-not (Test-Path -LiteralPath $mathlibLeanLib -PathType Container)) {
    throw "Prebuilt Mathlib Lean library not found: $mathlibLeanLib"
}

$projectLeanLib = Join-Path $resolvedDependencyProject ".lake\build\lib\lean"
if (Test-Path -LiteralPath $projectLeanLib -PathType Container) {
    $leanPathEntries.Add((Resolve-Path -LiteralPath $projectLeanLib).Path)
}

$toolchainLeanLib = Join-Path $toolchainRoot "lib\lean"
$leanPathEntries.Add((Resolve-Path -LiteralPath $toolchainLeanLib).Path)
$uniqueLeanPathEntries = @($leanPathEntries | Select-Object -Unique)
$exactLeanPath = $uniqueLeanPathEntries -join [IO.Path]::PathSeparator

$workspaceLockDirectory = Join-Path $sourceRoot "artifacts\build"
New-Item -ItemType Directory -Force -Path $workspaceLockDirectory | Out-Null
$workspaceBuildLockPath = Join-Path $workspaceLockDirectory ".lean-build.lock"
try {
    $workspaceBuildLockStream = [IO.File]::Open(
        $workspaceBuildLockPath, [IO.FileMode]::OpenOrCreate,
        [IO.FileAccess]::ReadWrite, [IO.FileShare]::None)
} catch {
    throw "Another Lean of the Mathematical Commons build holds $workspaceBuildLockPath. " +
        "Do not overlap RAM-bounded builds."
}

$leanVersion = (& $resolvedLeanExecutable --version 2>&1 | Out-String).Trim()

$expectedLeanVersion = $null
if ($repositoryToolchainValue -match ':v(?<version>[0-9]+(?:\.[0-9]+)+)$') {
    $expectedLeanVersion = $Matches.version
}
$reportedLeanVersion = $null
if ($leanVersion -match 'Lean \(version (?<version>[^,]+),') {
    $reportedLeanVersion = $Matches.version
}
$leanVersionMatchesToolchain = $null -eq $expectedLeanVersion -or
    $expectedLeanVersion -eq $reportedLeanVersion
if (-not $leanVersionMatchesToolchain) {
    throw "Resolved Lean reports version $reportedLeanVersion; toolchain requests $expectedLeanVersion."
}

if ([string]::IsNullOrWhiteSpace($LogDirectory)) {
    $LogDirectory = Join-Path $sourceRoot "artifacts\build"
}
New-Item -ItemType Directory -Force -Path $LogDirectory | Out-Null
$resolvedLogDirectory = (Resolve-Path -LiteralPath $LogDirectory).Path

$runId = "{0}-{1}" -f (Get-Date -Format "yyyyMMddTHHmmssfffffff"),
    ([Guid]::NewGuid().ToString("N").Substring(0, 8))
$baseName = [IO.Path]::GetFileNameWithoutExtension($resolvedFile)
$stdoutPath = Join-Path $resolvedLogDirectory "$baseName-$runId.stdout.txt"
$stderrPath = Join-Path $resolvedLogDirectory "$baseName-$runId.stderr.txt"
$receiptPath = Join-Path $resolvedLogDirectory "$baseName-$runId.receipt.json"
$limitBytes = [int64] ($MaxMemoryGiB * 1GB)
$sampleIntervalMilliseconds = 200

$sourceBefore = Get-FileFingerprint $resolvedFile
$runnerBefore = Get-FileFingerprint $runnerPath
$leanExecutableBefore = Get-FileFingerprint $resolvedLeanExecutable
$repositoryToolchainBefore = Get-FileFingerprint $repositoryToolchainPath
$dependencyToolchainBefore = Get-FileFingerprint $dependencyToolchainPath
$repositoryManifestBefore = Get-FileFingerprint $repositoryManifestPath
$dependencyManifestBefore = Get-FileFingerprint $dependencyManifestPath

$process = $null
$processStarted = $false
$processCompleted = $false
$processExitCode = $null
$stdoutFileStream = $null
$stderrFileStream = $null
$stdoutCopyTask = $null
$stderrCopyTask = $null
$memoryExceeded = $false
$peakBytes = 0L
$lastProcessTreeSnapshot = @()
$terminatedProcessIds = [Collections.Generic.List[int]]::new()
$runnerErrors = [Collections.Generic.List[string]]::new()
$terminationReason = "not_started"
$startedAt = Get-Date

try {
    $stdoutFileStream = [IO.File]::Open(
        $stdoutPath, [IO.FileMode]::Create, [IO.FileAccess]::Write, [IO.FileShare]::Read)
    $stderrFileStream = [IO.File]::Open(
        $stderrPath, [IO.FileMode]::Create, [IO.FileAccess]::Write, [IO.FileShare]::Read)

    $startInfo = [Diagnostics.ProcessStartInfo]::new()
    $startInfo.FileName = $resolvedLeanExecutable
    $startInfo.WorkingDirectory = $sourceRoot
    $startInfo.UseShellExecute = $false
    $startInfo.CreateNoWindow = $true
    $startInfo.RedirectStandardOutput = $true
    $startInfo.RedirectStandardError = $true
    [void] $startInfo.ArgumentList.Add($resolvedFile)
    $startInfo.Environment["LEAN_NUM_THREADS"] = "1"
    $startInfo.Environment["LEAN_PATH"] = $exactLeanPath

    $process = [Diagnostics.Process]::new()
    $process.StartInfo = $startInfo
    if (-not $process.Start()) {
        throw "Failed to start Lean process."
    }
    $processStarted = $true
    $terminationReason = "running"
    $stdoutCopyTask = $process.StandardOutput.BaseStream.CopyToAsync($stdoutFileStream)
    $stderrCopyTask = $process.StandardError.BaseStream.CopyToAsync($stderrFileStream)

    while (-not $process.HasExited) {
        $process.Refresh()
        if (-not $process.HasExited) {
            $snapshot = @(Get-ProcessTreeSnapshot $process.Id)
            $lastProcessTreeSnapshot = $snapshot
            $workingSet = 0L
            foreach ($node in $snapshot) {
                $live = Get-Process -Id $node.ProcessId -ErrorAction SilentlyContinue
                if ($null -ne $live) {
                    $workingSet += [int64] $live.WorkingSet64
                }
            }
            if ($workingSet -gt $peakBytes) {
                $peakBytes = $workingSet
            }
            if ($workingSet -gt $limitBytes) {
                $memoryExceeded = $true
                $terminationReason = "memory_limit_exceeded"
                foreach ($node in $snapshot) {
                    if (-not $terminatedProcessIds.Contains([int] $node.ProcessId)) {
                        $terminatedProcessIds.Add([int] $node.ProcessId)
                    }
                }
                Stop-CapturedProcessTree $snapshot $process.Id
                break
            }
        }
        Start-Sleep -Milliseconds $sampleIntervalMilliseconds
    }
    $process.WaitForExit()
    $processExitCode = $process.ExitCode
    $processCompleted = $true
    if (-not $memoryExceeded) {
        $terminationReason = "process_exited"
    }
} catch {
    $runnerErrors.Add($_.Exception.ToString())
    if (-not $memoryExceeded) {
        $terminationReason = "runner_exception"
    }
} finally {
    if ($processStarted -and -not $processCompleted -and -not $process.HasExited) {
        $cleanupSnapshot = @()
        try {
            $cleanupSnapshot = @(Get-ProcessTreeSnapshot $process.Id)
        } catch {
            $runnerErrors.Add("Process-tree capture failure during cleanup: $($_.Exception)")
            $cleanupSnapshot = @($lastProcessTreeSnapshot)
        }
        if ($cleanupSnapshot.Count -eq 0) {
            $cleanupSnapshot = @([pscustomobject]@{ ProcessId = $process.Id; Depth = 0 })
        }
        try {
            foreach ($node in $cleanupSnapshot) {
                if (-not $terminatedProcessIds.Contains([int] $node.ProcessId)) {
                    $terminatedProcessIds.Add([int] $node.ProcessId)
                }
            }
            Stop-CapturedProcessTree $cleanupSnapshot $process.Id
            $process.WaitForExit()
            $processExitCode = $process.ExitCode
            $processCompleted = $true
        } catch {
            $runnerErrors.Add("Cleanup failure: $($_.Exception)")
        }
    }

    foreach ($copyTask in @($stdoutCopyTask, $stderrCopyTask)) {
        if ($null -ne $copyTask) {
            try {
                [void] $copyTask.GetAwaiter().GetResult()
            } catch {
                $runnerErrors.Add("Log-copy failure: $($_.Exception)")
            }
        }
    }
    foreach ($stream in @($stdoutFileStream, $stderrFileStream)) {
        if ($null -ne $stream) {
            try {
                $stream.Flush()
                $stream.Dispose()
            } catch {
                $runnerErrors.Add("Log-stream cleanup failure: $($_.Exception)")
            }
        }
    }
    if ($null -ne $process) {
        $process.Dispose()
    }
    if ($null -ne $workspaceBuildLockStream) {
        $workspaceBuildLockStream.Dispose()
    }
}

$finishedAt = Get-Date
$sourceAfter = Get-FileFingerprint $resolvedFile
$runnerAfter = Get-FileFingerprint $runnerPath
$leanExecutableAfter = Get-FileFingerprint $resolvedLeanExecutable
$repositoryToolchainAfter = Get-FileFingerprint $repositoryToolchainPath
$dependencyToolchainAfter = Get-FileFingerprint $dependencyToolchainPath
$repositoryManifestAfter = Get-FileFingerprint $repositoryManifestPath
$dependencyManifestAfter = Get-FileFingerprint $dependencyManifestPath
$stdoutFingerprint = Get-FileFingerprint $stdoutPath
$stderrFingerprint = Get-FileFingerprint $stderrPath

$sourceChanged = -not (Test-FingerprintEqual $sourceBefore $sourceAfter)
$environmentChanged = -not (
    (Test-FingerprintEqual $runnerBefore $runnerAfter) -and
    (Test-FingerprintEqual $leanExecutableBefore $leanExecutableAfter) -and
    (Test-FingerprintEqual $repositoryToolchainBefore $repositoryToolchainAfter) -and
    (Test-FingerprintEqual $dependencyToolchainBefore $dependencyToolchainAfter) -and
    (Test-FingerprintEqual $repositoryManifestBefore $repositoryManifestAfter) -and
    (Test-FingerprintEqual $dependencyManifestBefore $dependencyManifestAfter)
)

if ($memoryExceeded) {
    $exitCode = 137
} elseif ($runnerErrors.Count -gt 0) {
    $exitCode = 70
} elseif ($sourceChanged) {
    $exitCode = 86
} elseif ($environmentChanged) {
    $exitCode = 87
} else {
    $exitCode = $processExitCode
}

$receipt = [ordered]@{
    schema = "lean-mathematical-commons/build-receipt/1.2"
    run_id = $runId
    source = [ordered]@{
        path_absolute = $resolvedFile
        path_relative_to_repository = Get-PortableRelativePath $sourceRoot $resolvedFile
        before = $sourceBefore
        after = $sourceAfter
        changed_during_build = $sourceChanged
    }
    runner = [ordered]@{
        path_absolute = $runnerPath
        path_relative_to_repository = Get-PortableRelativePath $sourceRoot $runnerPath
        before = $runnerBefore
        after = $runnerAfter
    }
    lean = [ordered]@{
        executable_path = $resolvedLeanExecutable
        executable_before = $leanExecutableBefore
        executable_after = $leanExecutableAfter
        version_output = $leanVersion
        expected_version_from_toolchain = $expectedLeanVersion
        reported_version = $reportedLeanVersion
        version_matches_toolchain = $leanVersionMatchesToolchain
        direct_invocation = $true
        argument_list = @($resolvedFile)
        working_directory = $sourceRoot
        lean_num_threads = 1
        lean_path = $uniqueLeanPathEntries
    }
    toolchains = [ordered]@{
        normalized_values_match = $toolchainsMatch
        repository = [ordered]@{
            path = $repositoryToolchainPath
            normalized_value = $repositoryToolchainValue
            before = $repositoryToolchainBefore
            after = $repositoryToolchainAfter
        }
        dependency_project = [ordered]@{
            path = $dependencyToolchainPath
            normalized_value = $dependencyToolchainValue
            before = $dependencyToolchainBefore
            after = $dependencyToolchainAfter
        }
    }
    manifests = [ordered]@{
        mathlib_pins_match = $mathlibPinsMatch
        repository = [ordered]@{
            path = $repositoryManifestPath
            before = $repositoryManifestBefore
            after = $repositoryManifestAfter
            mathlib = $repositoryMathlibPin
        }
        dependency_project = [ordered]@{
            path = $dependencyManifestPath
            before = $dependencyManifestBefore
            after = $dependencyManifestAfter
            mathlib = $dependencyMathlibPin
        }
    }
    dependency_project = $resolvedDependencyProject
    platform = [ordered]@{
        os_description = [Runtime.InteropServices.RuntimeInformation]::OSDescription
        os_architecture = [Runtime.InteropServices.RuntimeInformation]::OSArchitecture.ToString()
        process_architecture = [Runtime.InteropServices.RuntimeInformation]::ProcessArchitecture.ToString()
        framework = [Runtime.InteropServices.RuntimeInformation]::FrameworkDescription
        powershell_version = $PSVersionTable.PSVersion.ToString()
        powershell_edition = $PSVersionTable.PSEdition
    }
    watcher = [ordered]@{
        enforcement = "best_effort_sampled_process_tree_working_set"
        hard_limit = $false
        limitation = "Transient memory peaks between samples are possible; this is not a Windows Job Object hard ceiling."
        scope = "Lean root process and descendants captured from parent-process relationships"
        kill_policy = "On abnormal termination, stop only captured descendants (deepest first), then the captured root"
        sample_interval_milliseconds = $sampleIntervalMilliseconds
        max_memory_gib = $MaxMemoryGiB
        limit_bytes = $limitBytes
        observed_process_tree_peak_bytes = $peakBytes
        memory_exceeded = $memoryExceeded
        terminated_process_ids = @($terminatedProcessIds)
    }
    workspace_build_lock = [ordered]@{
        path = $workspaceBuildLockPath
        exclusive = $true
        purpose = "Prevent concurrent Lean builds in this workspace"
    }
    environment_changed_during_build = $environmentChanged
    process_started = $processStarted
    process_completed = $processCompleted
    process_exit_code = $processExitCode
    termination_reason = $terminationReason
    runner_errors = @($runnerErrors)
    started_at = $startedAt.ToString("o")
    finished_at = $finishedAt.ToString("o")
    exit_code = $exitCode
    logs = [ordered]@{
        stdout = [ordered]@{
            path_absolute = $stdoutPath
            path_relative_to_repository = Get-PortableRelativePath $sourceRoot $stdoutPath
            fingerprint = $stdoutFingerprint
        }
        stderr = [ordered]@{
            path_absolute = $stderrPath
            path_relative_to_repository = Get-PortableRelativePath $sourceRoot $stderrPath
            fingerprint = $stderrFingerprint
        }
    }
}
$receiptJson = $receipt | ConvertTo-Json -Depth 10
$receiptJson | Set-Content -LiteralPath $receiptPath -Encoding utf8

Get-Content -LiteralPath $stdoutPath
Get-Content -LiteralPath $stderrPath
$receiptJson
exit $exitCode
