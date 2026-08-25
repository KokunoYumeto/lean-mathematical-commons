param(
    [Parameter(Mandatory = $true)]
    [string] $ReleaseDirectory
)

$ErrorActionPreference = "Stop"

function Assert-Release([bool] $Condition, [string] $Message) {
    if (-not $Condition) {
        throw "Release verification failed: $Message"
    }
}

function Get-Fingerprint([string] $Path) {
    $item = Get-Item -LiteralPath $Path
    return [pscustomobject]@{
        bytes = [int64] $item.Length
        sha256 = (Get-FileHash -LiteralPath $item.FullName -Algorithm SHA256).Hash
    }
}

function Test-Fingerprint($Actual, $Expected) {
    return $Actual.bytes -eq [int64] $Expected.bytes -and
        $Actual.sha256 -eq [string] $Expected.sha256
}

function Resolve-RepositoryFile([string] $RepositoryRoot, [string] $RelativePath) {
    $candidate = [IO.Path]::GetFullPath((Join-Path $RepositoryRoot $RelativePath))
    $rootWithSeparator = $RepositoryRoot.TrimEnd('\', '/') + [IO.Path]::DirectorySeparatorChar
    Assert-Release ($candidate.StartsWith($rootWithSeparator, [StringComparison]::OrdinalIgnoreCase)) `
        "Receipt path escapes the repository: $RelativePath"
    return $candidate
}

$releaseRoot = (Resolve-Path -LiteralPath $ReleaseDirectory).Path
$repositoryRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot "..")).Path
$checksumsPath = Join-Path $releaseRoot "SHA256SUMS.csv"
$metadataPath = Join-Path $releaseRoot "release-metadata.json"

Assert-Release (Test-Path -LiteralPath $checksumsPath -PathType Leaf) "Missing SHA256SUMS.csv."
Assert-Release (Test-Path -LiteralPath $metadataPath -PathType Leaf) "Missing release-metadata.json."

$checksumRows = @(Import-Csv -LiteralPath $checksumsPath)
Assert-Release ($checksumRows.Count -gt 0) "Checksum manifest is empty."
$listedPaths = [Collections.Generic.HashSet[string]]::new([StringComparer]::OrdinalIgnoreCase)
foreach ($row in $checksumRows) {
    Assert-Release (-not [string]::IsNullOrWhiteSpace($row.path)) "Checksum row has no path."
    Assert-Release ($listedPaths.Add([string] $row.path)) "Duplicate checksum path: $($row.path)."
    Assert-Release ([IO.Path]::GetFileName($row.path) -eq $row.path) `
        "Release checksum paths must be flat filenames: $($row.path)."
    $file = Join-Path $releaseRoot $row.path
    Assert-Release (Test-Path -LiteralPath $file -PathType Leaf) "Missing checksummed file: $($row.path)."
    $actual = Get-Fingerprint $file
    Assert-Release (Test-Fingerprint $actual $row) "Checksum or size mismatch: $($row.path)."
}

$releaseFiles = @(Get-ChildItem -LiteralPath $releaseRoot -File |
    Where-Object { $_.Name -ne "SHA256SUMS.csv" })
foreach ($file in $releaseFiles) {
    Assert-Release ($listedPaths.Contains($file.Name)) "Unlisted release file: $($file.Name)."
}

$metadata = Get-Content -LiteralPath $metadataPath -Raw | ConvertFrom-Json
Assert-Release ($metadata.schema -eq "lean-mathematical-commons/release-candidate/1.0") `
    "Unexpected release metadata schema."
Assert-Release ($metadata.status -eq "local_candidate_not_published") `
    "This verifier expects an unpublished local candidate."
Assert-Release ($metadata.publication.new_doi_claimed -eq $false) `
    "Metadata must not claim an unpublished DOI."
Assert-Release ($metadata.lean_toolchain -eq "leanprover/lean4:v4.31.0") `
    "Unexpected Lean toolchain."

$allowedAxioms = [Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
foreach ($axiom in @("propext", "Classical.choice", "Quot.sound")) {
    [void] $allowedAxioms.Add($axiom)
}

$verifiedReceipts = [Collections.Generic.List[object]]::new()
foreach ($module in @($metadata.modules)) {
    $receiptName = [string] $module.receipt
    Assert-Release ($listedPaths.Contains($receiptName)) "Receipt is not checksummed: $receiptName."
    $receiptPath = Join-Path $releaseRoot $receiptName
    $receipt = Get-Content -LiteralPath $receiptPath -Raw | ConvertFrom-Json

    Assert-Release ($receipt.schema -eq "lean-mathematical-commons/build-receipt/1.2") `
        "Unexpected receipt schema in $receiptName."
    Assert-Release ($receipt.exit_code -eq 0 -and $receipt.process_exit_code -eq 0) `
        "Nonzero build exit in $receiptName."
    Assert-Release ($receipt.process_started -and $receipt.process_completed) `
        "Incomplete process lifecycle in $receiptName."
    Assert-Release ($receipt.termination_reason -eq "process_exited") `
        "Abnormal termination in $receiptName."
    Assert-Release (@($receipt.runner_errors).Count -eq 0) "Runner errors in $receiptName."
    Assert-Release (-not $receipt.source.changed_during_build) "Source changed in $receiptName."
    Assert-Release (-not $receipt.environment_changed_during_build) `
        "Build identities changed in $receiptName."
    Assert-Release ($receipt.lean.direct_invocation -and $receipt.lean.lean_num_threads -eq 1) `
        "Build was not a direct one-thread Lean invocation in $receiptName."
    Assert-Release ($receipt.lean.version_matches_toolchain) `
        "Lean version mismatch in $receiptName."
    Assert-Release ($receipt.toolchains.normalized_values_match) `
        "Toolchain mismatch in $receiptName."
    Assert-Release ($receipt.manifests.mathlib_pins_match) `
        "Mathlib pin mismatch in $receiptName."
    Assert-Release ($receipt.manifests.repository.mathlib.resolved_rev -eq
        $metadata.mathlib_resolved_revision) "Wrong Mathlib revision in $receiptName."
    Assert-Release ($receipt.watcher.max_memory_gib -eq 8.0) `
        "Expected the normal 8 GiB limit in $receiptName."
    Assert-Release (-not $receipt.watcher.memory_exceeded) "Memory limit exceeded in $receiptName."
    Assert-Release ([int64] $receipt.watcher.observed_process_tree_peak_bytes -le
        [int64] $receipt.watcher.limit_bytes) "Recorded peak exceeds limit in $receiptName."
    Assert-Release ($receipt.workspace_build_lock.exclusive) `
        "Exclusive workspace build lock not recorded in $receiptName."

    Assert-Release (Test-Fingerprint $receipt.source.before $receipt.source.after) `
        "Receipt source fingerprints differ in $receiptName."
    Assert-Release (Test-Fingerprint $receipt.runner.before $receipt.runner.after) `
        "Receipt runner fingerprints differ in $receiptName."
    Assert-Release (Test-Fingerprint $receipt.lean.executable_before `
        $receipt.lean.executable_after) "Lean executable changed in $receiptName."

    $sourcePath = Resolve-RepositoryFile $repositoryRoot `
        ([string] $receipt.source.path_relative_to_repository)
    Assert-Release (Test-Path -LiteralPath $sourcePath -PathType Leaf) `
        "Current source is missing for $receiptName."
    $currentSource = Get-Fingerprint $sourcePath
    Assert-Release (Test-Fingerprint $currentSource $receipt.source.before) `
        "Current source no longer matches $receiptName."
    Assert-Release ($module.path -eq $receipt.source.path_relative_to_repository) `
        "Release metadata source path differs from $receiptName."
    Assert-Release ($module.source_sha256 -eq $receipt.source.before.sha256) `
        "Release metadata source hash differs from $receiptName."
    Assert-Release ([int64] $module.observed_process_tree_peak_bytes -eq
        [int64] $receipt.watcher.observed_process_tree_peak_bytes) `
        "Release metadata peak differs from $receiptName."

    $runnerPath = Resolve-RepositoryFile $repositoryRoot `
        ([string] $receipt.runner.path_relative_to_repository)
    Assert-Release (Test-Fingerprint (Get-Fingerprint $runnerPath) $receipt.runner.before) `
        "Current checker no longer matches $receiptName."

    foreach ($streamName in @("stdout", "stderr")) {
        $stream = $receipt.logs.$streamName
        $copyName = [IO.Path]::GetFileName([string] $stream.path_absolute)
        Assert-Release ($listedPaths.Contains($copyName)) `
            "Promoted $streamName is not checksummed for $receiptName."
        $copyPath = Join-Path $releaseRoot $copyName
        Assert-Release (Test-Fingerprint (Get-Fingerprint $copyPath) $stream.fingerprint) `
            "Promoted $streamName differs from $receiptName."
    }

    $stderrName = [IO.Path]::GetFileName([string] $receipt.logs.stderr.path_absolute)
    Assert-Release ((Get-Item -LiteralPath (Join-Path $releaseRoot $stderrName)).Length -eq 0) `
        "Expected empty stderr for $receiptName."
    $stdoutName = [IO.Path]::GetFileName([string] $receipt.logs.stdout.path_absolute)
    $stdout = Get-Content -LiteralPath (Join-Path $releaseRoot $stdoutName) -Raw
    Assert-Release ($stdout -notmatch '\bsorryAx\b') "sorryAx occurs in $receiptName output."
    $axiomBlocks = [regex]::Matches($stdout, '(?s)depends on axioms:\s*\[(.*?)\]')
    Assert-Release ($axiomBlocks.Count -gt 0) "No #print axioms evidence in $receiptName."
    foreach ($block in $axiomBlocks) {
        $names = @($block.Groups[1].Value -split ',' |
            ForEach-Object { $_.Trim() } | Where-Object { $_ -ne '' })
        foreach ($name in $names) {
            Assert-Release ($allowedAxioms.Contains($name)) `
                "Unexpected axiom '$name' in $receiptName."
        }
    }

    $verifiedReceipts.Add([pscustomobject]@{
        receipt = $receiptName
        source = $receipt.source.path_relative_to_repository
        source_sha256 = $receipt.source.before.sha256
        peak_bytes = [int64] $receipt.watcher.observed_process_tree_peak_bytes
        axiom_reports = $axiomBlocks.Count
    })
}

$result = [ordered]@{
    schema = "lean-mathematical-commons/release-verification/1.0"
    release_id = $metadata.release_id
    release_directory = $releaseRoot
    checksummed_files = $checksumRows.Count
    receipts_verified = $verifiedReceipts.Count
    mathlib_resolved_revision = $metadata.mathlib_resolved_revision
    receipts = @($verifiedReceipts)
    status = "verified"
}
$result | ConvertTo-Json -Depth 6
