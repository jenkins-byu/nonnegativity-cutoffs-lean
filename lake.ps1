param(
  [Parameter(ValueFromRemainingArguments = $true)]
  [string[]] $LakeArguments
)

$ErrorActionPreference = "Stop"

$projectRoot = $PSScriptRoot
$elanHome = Join-Path $projectRoot ".elan"
$lake = Join-Path $elanHome "bin\lake.exe"

if (-not (Test-Path -LiteralPath $lake)) {
  throw "Project-local Lake was not found. Run .\setup.ps1 first."
}

if ($LakeArguments.Count -eq 0) {
  $LakeArguments = @("build")
}

$env:ELAN_HOME = $elanHome

# This setting is process-local. It is needed in sandboxed environments where Git observes the
# downloaded Lake packages as belonging to a different host identity.
$env:GIT_CONFIG_COUNT = "1"
$env:GIT_CONFIG_KEY_0 = "safe.directory"
$env:GIT_CONFIG_VALUE_0 = "*"

& $lake @LakeArguments
if ($LASTEXITCODE -ne 0) {
  throw "Lake failed with exit code $LASTEXITCODE."
}
