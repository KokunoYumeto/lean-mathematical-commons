param(
    [Parameter(Mandatory = $true)]
    [string] $ProjectDirectory,

    [Parameter(Mandatory = $true)]
    [string[]] $LakeArguments,

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
        [pscustomobject]@{ ProcessId = [int] $_.Key; Depth = [int] $_.Value }
    })
}

function Stop-CapturedProcessTree([object[]] $Snapshot, [int] $RootProcessId) {
    foreach ($node in @($Snapshot | Where-Object { $_.ProcessId -ne $RootProcessId } |
            Sort-Object Depth -Descending)) {
        Stop-Process -Id $node.ProcessId -Force -ErrorAction SilentlyContinue
    }
    Stop-Process -Id $RootProcessId -Force -ErrorAction SilentlyContinue
}

$sourceRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot "..")).Path
$runnerPath = (Resolve-Path -LiteralPath $PSCommandPath).Path
$projectRoot = (Resolve-Path -LiteralPath $ProjectDirectory).Path
$toolchainPath = (Resolve-Path -LiteralPath (Join-Path $projectRoot "lean-toolchain")).Path
$manifestPath = (Resolve-Path -LiteralPath (Join-Path $projectRoot "lake-manifest.json")).Path
$lakefileCandidates = @(@("lakefile.toml", "lakefile.lean") | ForEach-Object {
    Join-Path $projectRoot $_
} | Where-Object { Test-Path -LiteralPath $_ -PathType Leaf })
if ($lakefileCandidates.Count -ne 1) {
    throw "Expected exactly one Lake configuration file in $projectRoot."
}
$lakefilePath = (Resolve-Path -LiteralPath $lakefileCandidates[0]).Path

$toolchainValue = (Get-Content -LiteralPath $toolchainPath -Raw).Trim()
$toolchainDirectory = $toolchainValue.Replace("/", "--").Replace(":", "---")
$lakeExecutable = (Resolve-Path -LiteralPath (Join-Path $env:USERPROFILE ".elan\toolchains\$toolchainDirectory\bin\lake.exe")).Path

if ([string]::IsNullOrWhiteSpace($LogDirectory)) {
    $LogDirectory = Join-Path $sourceRoot "artifacts\dependency-cache\logs"
}
New-Item -ItemType Directory -Force -Path $LogDirectory | Out-Null
$resolvedLogDirectory = (Resolve-Path -LiteralPath $LogDirectory).Path

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

$runId = "{0}-{1}" -f (Get-Date -Format "yyyyMMddTHHmmssfffffff"),
    ([Guid]::NewGuid().ToString("N").Substring(0, 8))
$stdoutPath = Join-Path $resolvedLogDirectory "lake-$runId.stdout.txt"
$stderrPath = Join-Path $resolvedLogDirectory "lake-$runId.stderr.txt"
$receiptPath = Join-Path $resolvedLogDirectory "lake-$runId.receipt.json"
$limitBytes = [int64] ($MaxMemoryGiB * 1GB)
$sampleIntervalMilliseconds = 200

$runnerBefore = Get-FileFingerprint $runnerPath
$toolchainBefore = Get-FileFingerprint $toolchainPath
$manifestBefore = Get-FileFingerprint $manifestPath
$lakefileBefore = Get-FileFingerprint $lakefilePath
$lakeBefore = Get-FileFingerprint $lakeExecutable
$startedAt = Get-Date
$process = $null
$peakBytes = 0L
$memoryExceeded = $false
$lastSnapshot = @()
$runnerError = $null
$processExitCode = $null

try {
    $startInfo = [Diagnostics.ProcessStartInfo]::new()
    $startInfo.FileName = $lakeExecutable
    $startInfo.WorkingDirectory = $projectRoot
    $startInfo.UseShellExecute = $false
    $startInfo.CreateNoWindow = $true
    $startInfo.RedirectStandardOutput = $true
    $startInfo.RedirectStandardError = $true
    foreach ($argument in $LakeArguments) {
        [void] $startInfo.ArgumentList.Add($argument)
    }
    $startInfo.Environment["LEAN_NUM_THREADS"] = "1"
    $startInfo.Environment["LAKE_JOBS"] = "1"

    $process = [Diagnostics.Process]::new()
    $process.StartInfo = $startInfo
    if (-not $process.Start()) {
        throw "Failed to start Lake."
    }
    $stdoutTask = $process.StandardOutput.ReadToEndAsync()
    $stderrTask = $process.StandardError.ReadToEndAsync()

    while (-not $process.WaitForExit($sampleIntervalMilliseconds)) {
        $lastSnapshot = @(Get-ProcessTreeSnapshot $process.Id)
        $workingSet = 0L
        foreach ($node in $lastSnapshot) {
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
            Stop-CapturedProcessTree $lastSnapshot $process.Id
            break
        }
    }
    $process.WaitForExit()
    $processExitCode = $process.ExitCode
    $stdout = $stdoutTask.GetAwaiter().GetResult()
    $stderr = $stderrTask.GetAwaiter().GetResult()
    Set-Content -LiteralPath $stdoutPath -Value $stdout -NoNewline -Encoding utf8
    Set-Content -LiteralPath $stderrPath -Value $stderr -NoNewline -Encoding utf8
} catch {
    $runnerError = $_.Exception.ToString()
    if ($null -ne $process -and -not $process.HasExited) {
        $cleanupSnapshot = @(Get-ProcessTreeSnapshot $process.Id)
        if ($cleanupSnapshot.Count -eq 0) {
            $cleanupSnapshot = @([pscustomobject]@{ ProcessId = $process.Id; Depth = 0 })
        }
        Stop-CapturedProcessTree $cleanupSnapshot $process.Id
    }
    if (-not (Test-Path -LiteralPath $stdoutPath)) {
        Set-Content -LiteralPath $stdoutPath -Value "" -NoNewline -Encoding utf8
    }
    if (-not (Test-Path -LiteralPath $stderrPath)) {
        Set-Content -LiteralPath $stderrPath -Value "" -NoNewline -Encoding utf8
    }
} finally {
    if ($null -ne $process) {
        $process.Dispose()
    }
    if ($null -ne $lockStream) {
        $lockStream.Dispose()
    }
}

$finishedAt = Get-Date
$runnerAfter = Get-FileFingerprint $runnerPath
$toolchainAfter = Get-FileFingerprint $toolchainPath
$manifestAfter = Get-FileFingerprint $manifestPath
$lakefileAfter = Get-FileFingerprint $lakefilePath
$lakeAfter = Get-FileFingerprint $lakeExecutable
$environmentChanged = -not (
    (Test-FingerprintEqual $runnerBefore $runnerAfter) -and
    (Test-FingerprintEqual $toolchainBefore $toolchainAfter) -and
    (Test-FingerprintEqual $manifestBefore $manifestAfter) -and
    (Test-FingerprintEqual $lakefileBefore $lakefileAfter) -and
    (Test-FingerprintEqual $lakeBefore $lakeAfter))

$exitCode = if ($memoryExceeded) { 137 } elseif ($null -ne $runnerError) { 70 } elseif ($environmentChanged) { 87 } else { $processExitCode }
$receipt = [ordered]@{
    schema = "lean-mathematical-commons/lake-process-receipt/1.0"
    run_id = $runId
    project_directory = $projectRoot
    command = [ordered]@{
        executable = $lakeExecutable
        arguments = @($LakeArguments)
        lean_num_threads = 1
        lake_jobs = 1
    }
    inputs = [ordered]@{
        runner = [ordered]@{ path = $runnerPath; before = $runnerBefore; after = $runnerAfter }
        toolchain = [ordered]@{ path = $toolchainPath; value = $toolchainValue; before = $toolchainBefore; after = $toolchainAfter }
        manifest = [ordered]@{ path = $manifestPath; before = $manifestBefore; after = $manifestAfter }
        lakefile = [ordered]@{ path = $lakefilePath; before = $lakefileBefore; after = $lakefileAfter }
        lake = [ordered]@{ path = $lakeExecutable; before = $lakeBefore; after = $lakeAfter }
    }
    watcher = [ordered]@{
        enforcement = "best_effort_sampled_process_tree_working_set"
        hard_limit = $false
        sample_interval_milliseconds = $sampleIntervalMilliseconds
        max_memory_gib = $MaxMemoryGiB
        limit_bytes = $limitBytes
        observed_process_tree_peak_bytes = $peakBytes
        memory_exceeded = $memoryExceeded
        kill_policy = "Stop only the captured Lake process tree on limit breach."
    }
    workspace_build_lock = [ordered]@{ path = $lockPath; exclusive = $true }
    environment_changed_during_run = $environmentChanged
    process_exit_code = $processExitCode
    runner_error = $runnerError
    started_at = $startedAt.ToString("o")
    finished_at = $finishedAt.ToString("o")
    exit_code = $exitCode
    logs = [ordered]@{
        stdout = [ordered]@{ path = $stdoutPath; fingerprint = Get-FileFingerprint $stdoutPath }
        stderr = [ordered]@{ path = $stderrPath; fingerprint = Get-FileFingerprint $stderrPath }
    }
}
$receipt | ConvertTo-Json -Depth 10 | Set-Content -LiteralPath $receiptPath -Encoding utf8

Get-Content -LiteralPath $stdoutPath
Get-Content -LiteralPath $stderrPath
$receipt | ConvertTo-Json -Depth 10
exit $exitCode
