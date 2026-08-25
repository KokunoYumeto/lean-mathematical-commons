param(
    [Parameter(Mandatory = $true)]
    [string[]] $Files,

    [Parameter(Mandatory = $true)]
    [Alias("LakeProject")]
    [string] $DependencyProject,

    [string] $LeanExecutable = "",

    [ValidateRange(1, 10)]
    [double] $MaxMemoryGiB = 8,

    [string] $CacheDirectory = "",

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

function Get-MathlibPin([string] $ManifestPath) {
    $manifest = Get-Content -LiteralPath $ManifestPath -Raw | ConvertFrom-Json
    $matches = @($manifest.packages | Where-Object { $_.name -eq "mathlib" })
    if ($matches.Count -ne 1) {
        throw "Expected exactly one Mathlib package in $ManifestPath; found $($matches.Count)."
    }
    return [ordered]@{
        url = [string] $matches[0].url
        input_rev = [string] $matches[0].inputRev
        resolved_rev = [string] $matches[0].rev
    }
}

function Test-MathlibPinEqual($Left, $Right) {
    return $Left.url -eq $Right.url -and
        $Left.input_rev -eq $Right.input_rev -and
        $Left.resolved_rev -eq $Right.resolved_rev
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

function Get-ProcessTreeWorkingSet([object[]] $Snapshot) {
    [int64] $total = 0
    foreach ($node in $Snapshot) {
        try {
            $process = Get-Process -Id $node.ProcessId -ErrorAction Stop
            $total += [int64] $process.WorkingSet64
        } catch {
            # A process may exit between the CIM snapshot and this sample.
        }
    }
    return $total
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
$resolvedDependencyProject = (Resolve-Path -LiteralPath $DependencyProject).Path
$repositoryToolchainPath = (Resolve-Path -LiteralPath (Join-Path $sourceRoot "lean-toolchain")).Path
$repositoryManifestPath = (Resolve-Path -LiteralPath (Join-Path $sourceRoot "lake-manifest.json")).Path
$dependencyToolchainPath = (Resolve-Path -LiteralPath (Join-Path $resolvedDependencyProject "lean-toolchain")).Path
$dependencyManifestPath = (Resolve-Path -LiteralPath (Join-Path $resolvedDependencyProject "lake-manifest.json")).Path

$repositoryToolchainValue = (Get-Content -LiteralPath $repositoryToolchainPath -Raw).Trim()
$dependencyToolchainValue = (Get-Content -LiteralPath $dependencyToolchainPath -Raw).Trim()
if ($repositoryToolchainValue -ne $dependencyToolchainValue) {
    throw "Repository and dependency-project toolchains do not match after normalization."
}

$repositoryMathlibPin = Get-MathlibPin $repositoryManifestPath
$dependencyMathlibPin = Get-MathlibPin $dependencyManifestPath
if (-not (Test-MathlibPinEqual $repositoryMathlibPin $dependencyMathlibPin)) {
    throw "Repository and dependency-project Mathlib pins do not match."
}

if ([string]::IsNullOrWhiteSpace($LeanExecutable)) {
    $toolchainDirectory = $repositoryToolchainValue.Replace("/", "--").Replace(":", "---")
    $LeanExecutable = Join-Path $env:USERPROFILE ".elan\toolchains\$toolchainDirectory\bin\lean.exe"
}
$resolvedLeanExecutable = (Resolve-Path -LiteralPath $LeanExecutable).Path
$toolchainRoot = (Resolve-Path -LiteralPath (Join-Path (Split-Path $resolvedLeanExecutable) "..")).Path
$leanVersion = (& $resolvedLeanExecutable --version 2>&1 | Out-String).Trim()

$batchId = "{0}-{1}" -f (Get-Date -Format "yyyyMMddTHHmmssfffffff"),
    ([Guid]::NewGuid().ToString("N").Substring(0, 8))
if ([string]::IsNullOrWhiteSpace($CacheDirectory)) {
    $CacheDirectory = Join-Path $sourceRoot "artifacts\build\local-olean\$batchId"
}
if ([string]::IsNullOrWhiteSpace($LogDirectory)) {
    $LogDirectory = Join-Path $sourceRoot "artifacts\build"
}
New-Item -ItemType Directory -Force -Path $CacheDirectory, $LogDirectory | Out-Null
$resolvedCacheDirectory = (Resolve-Path -LiteralPath $CacheDirectory).Path
$resolvedLogDirectory = (Resolve-Path -LiteralPath $LogDirectory).Path

$resolvedFiles = [Collections.Generic.List[object]]::new()
foreach ($file in $Files) {
    $resolvedFile = (Resolve-Path -LiteralPath $file).Path
    $relativePath = [IO.Path]::GetRelativePath($sourceRoot, $resolvedFile)
    if ([IO.Path]::IsPathRooted($relativePath) -or
        $relativePath -eq ".." -or $relativePath.StartsWith("..$([IO.Path]::DirectorySeparatorChar)")) {
        throw "Lean source is outside the repository: $resolvedFile"
    }
    if (-not $relativePath.EndsWith(".lean", [StringComparison]::OrdinalIgnoreCase)) {
        throw "Expected a .lean source: $resolvedFile"
    }
    $modulePath = $relativePath.Substring(0, $relativePath.Length - 5)
    $moduleName = $modulePath.Replace('\', '.')
    $outputPath = Join-Path $resolvedCacheDirectory ($modulePath + ".olean")
    $outputParent = Split-Path -Parent $outputPath
    New-Item -ItemType Directory -Force -Path $outputParent | Out-Null
    $resolvedFiles.Add([pscustomobject]@{
        source = $resolvedFile
        source_relative = $relativePath.Replace('\', '/')
        module = $moduleName
        output = $outputPath
    })
}

$leanPathEntries = [Collections.Generic.List[string]]::new()
$leanPathEntries.Add($resolvedCacheDirectory)
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
$projectLeanLib = Join-Path $resolvedDependencyProject ".lake\build\lib\lean"
if (Test-Path -LiteralPath $projectLeanLib -PathType Container) {
    $leanPathEntries.Add((Resolve-Path -LiteralPath $projectLeanLib).Path)
}
$leanPathEntries.Add((Resolve-Path -LiteralPath (Join-Path $toolchainRoot "lib\lean")).Path)
$exactLeanPath = (@($leanPathEntries | Select-Object -Unique) -join [IO.Path]::PathSeparator)

$lockDirectory = Join-Path $sourceRoot "artifacts\build"
New-Item -ItemType Directory -Force -Path $lockDirectory | Out-Null
$lockPath = Join-Path $lockDirectory ".lean-build.lock"
try {
    $lockStream = [IO.File]::Open(
        $lockPath, [IO.FileMode]::OpenOrCreate,
        [IO.FileAccess]::ReadWrite, [IO.FileShare]::None)
} catch {
    throw "Another Lean build holds $lockPath. Do not overlap RAM-bounded builds."
}

$limitBytes = [int64] ($MaxMemoryGiB * 1GB)
$sampleIntervalMilliseconds = 200
$summaries = [Collections.Generic.List[object]]::new()

try {
    foreach ($entry in $resolvedFiles) {
        $runId = "{0}-{1}" -f (Get-Date -Format "yyyyMMddTHHmmssfffffff"),
            ([Guid]::NewGuid().ToString("N").Substring(0, 8))
        $safeModuleName = $entry.module.Replace('.', '-')
        $stdoutPath = Join-Path $resolvedLogDirectory "$safeModuleName-$runId.module.stdout.txt"
        $stderrPath = Join-Path $resolvedLogDirectory "$safeModuleName-$runId.module.stderr.txt"
        $receiptPath = Join-Path $resolvedLogDirectory "$safeModuleName-$runId.module.receipt.json"

        $sourceBefore = Get-FileFingerprint $entry.source
        $runnerBefore = Get-FileFingerprint $runnerPath
        $leanBefore = Get-FileFingerprint $resolvedLeanExecutable
        $repoToolchainBefore = Get-FileFingerprint $repositoryToolchainPath
        $dependencyToolchainBefore = Get-FileFingerprint $dependencyToolchainPath
        $repoManifestBefore = Get-FileFingerprint $repositoryManifestPath
        $dependencyManifestBefore = Get-FileFingerprint $dependencyManifestPath
        $startedAt = Get-Date

        $startInfo = [Diagnostics.ProcessStartInfo]::new()
        $startInfo.FileName = $resolvedLeanExecutable
        $startInfo.WorkingDirectory = $sourceRoot
        $startInfo.UseShellExecute = $false
        $startInfo.CreateNoWindow = $true
        $startInfo.RedirectStandardOutput = $true
        $startInfo.RedirectStandardError = $true
        [void] $startInfo.ArgumentList.Add("-o")
        [void] $startInfo.ArgumentList.Add($entry.output)
        [void] $startInfo.ArgumentList.Add($entry.source)
        $startInfo.Environment["LEAN_NUM_THREADS"] = "1"
        $startInfo.Environment["LEAN_PATH"] = $exactLeanPath

        $process = [Diagnostics.Process]::new()
        $process.StartInfo = $startInfo
        if (-not $process.Start()) {
            throw "Failed to start Lean for $($entry.module)."
        }
        $stdoutTask = $process.StandardOutput.ReadToEndAsync()
        $stderrTask = $process.StandardError.ReadToEndAsync()
        [int64] $peakBytes = 0
        $memoryExceeded = $false
        $lastSnapshot = @()

        while (-not $process.WaitForExit($sampleIntervalMilliseconds)) {
            $lastSnapshot = @(Get-ProcessTreeSnapshot $process.Id)
            $workingSet = Get-ProcessTreeWorkingSet $lastSnapshot
            if ($workingSet -gt $peakBytes) {
                $peakBytes = $workingSet
            }
            if ($workingSet -gt $limitBytes) {
                $memoryExceeded = $true
                Stop-CapturedProcessTree $lastSnapshot $process.Id
                break
            }
        }
        $process.WaitForExit()
        $exitCode = if ($memoryExceeded) { 137 } else { $process.ExitCode }
        $stdout = $stdoutTask.GetAwaiter().GetResult()
        $stderr = $stderrTask.GetAwaiter().GetResult()
        Set-Content -LiteralPath $stdoutPath -Value $stdout -NoNewline -Encoding utf8
        Set-Content -LiteralPath $stderrPath -Value $stderr -NoNewline -Encoding utf8
        $finishedAt = Get-Date

        $sourceAfter = Get-FileFingerprint $entry.source
        $runnerAfter = Get-FileFingerprint $runnerPath
        $leanAfter = Get-FileFingerprint $resolvedLeanExecutable
        $repoToolchainAfter = Get-FileFingerprint $repositoryToolchainPath
        $dependencyToolchainAfter = Get-FileFingerprint $dependencyToolchainPath
        $repoManifestAfter = Get-FileFingerprint $repositoryManifestPath
        $dependencyManifestAfter = Get-FileFingerprint $dependencyManifestPath
        $outputFingerprint = $null
        if (Test-Path -LiteralPath $entry.output -PathType Leaf) {
            $outputFingerprint = Get-FileFingerprint $entry.output
        }

        $environmentChanged = -not (
            (Test-FingerprintEqual $runnerBefore $runnerAfter) -and
            (Test-FingerprintEqual $leanBefore $leanAfter) -and
            (Test-FingerprintEqual $repoToolchainBefore $repoToolchainAfter) -and
            (Test-FingerprintEqual $dependencyToolchainBefore $dependencyToolchainAfter) -and
            (Test-FingerprintEqual $repoManifestBefore $repoManifestAfter) -and
            (Test-FingerprintEqual $dependencyManifestBefore $dependencyManifestAfter))

        $receipt = [ordered]@{
            schema = "lean-mathematical-commons/module-build-receipt/1.0"
            batch_id = $batchId
            run_id = $runId
            module = $entry.module
            source = [ordered]@{
                path_absolute = $entry.source
                path_relative_to_repository = $entry.source_relative
                before = $sourceBefore
                after = $sourceAfter
                changed_during_build = -not (Test-FingerprintEqual $sourceBefore $sourceAfter)
            }
            output = [ordered]@{
                path_absolute = $entry.output
                path_relative_to_cache = [IO.Path]::GetRelativePath($resolvedCacheDirectory, $entry.output).Replace('\', '/')
                fingerprint = $outputFingerprint
            }
            runner = [ordered]@{ path_absolute = $runnerPath; before = $runnerBefore; after = $runnerAfter }
            lean = [ordered]@{
                executable_path = $resolvedLeanExecutable
                version_output = $leanVersion
                direct_invocation = $true
                argument_list = @("-o", $entry.output, $entry.source)
                lean_num_threads = 1
                lean_path = @($leanPathEntries | Select-Object -Unique)
            }
            toolchains = [ordered]@{
                normalized_values_match = $true
                repository = $repositoryToolchainValue
                dependency_project = $dependencyToolchainValue
            }
            manifests = [ordered]@{
                mathlib_pins_match = $true
                repository_mathlib = $repositoryMathlibPin
                dependency_mathlib = $dependencyMathlibPin
            }
            watcher = [ordered]@{
                enforcement = "best_effort_sampled_process_tree_working_set"
                hard_limit = $false
                sample_interval_milliseconds = $sampleIntervalMilliseconds
                max_memory_gib = $MaxMemoryGiB
                limit_bytes = $limitBytes
                observed_process_tree_peak_bytes = $peakBytes
                memory_exceeded = $memoryExceeded
                kill_policy = "Stop only the captured Lean process tree on limit breach."
            }
            workspace_build_lock = [ordered]@{ path = $lockPath; exclusive = $true }
            environment_changed_during_build = $environmentChanged
            started_at = $startedAt.ToString("o")
            finished_at = $finishedAt.ToString("o")
            exit_code = $exitCode
            logs = [ordered]@{
                stdout = [ordered]@{ path_absolute = $stdoutPath; fingerprint = Get-FileFingerprint $stdoutPath }
                stderr = [ordered]@{ path_absolute = $stderrPath; fingerprint = Get-FileFingerprint $stderrPath }
            }
        }
        $receipt | ConvertTo-Json -Depth 12 | Set-Content -LiteralPath $receiptPath -Encoding utf8
        $summaries.Add([pscustomobject]@{
            module = $entry.module
            exit_code = $exitCode
            peak_bytes = $peakBytes
            output = $entry.output
            receipt = $receiptPath
        })
        Write-Output ("[{0}] exit={1} peak={2} receipt={3}" -f
            $entry.module, $exitCode, $peakBytes, $receiptPath)

        if ($exitCode -ne 0 -or $null -eq $outputFingerprint -or
            $receipt.source.changed_during_build -or $environmentChanged) {
            throw "Bounded module build failed integrity checks for $($entry.module)."
        }
    }
} finally {
    if ($null -ne $lockStream) {
        $lockStream.Dispose()
    }
}

[ordered]@{
    schema = "lean-mathematical-commons/module-build-batch/1.0"
    batch_id = $batchId
    cache_directory = $resolvedCacheDirectory
    modules = $summaries
} | ConvertTo-Json -Depth 8
