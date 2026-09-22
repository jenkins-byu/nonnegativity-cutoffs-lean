$ErrorActionPreference = "Stop"

$projectRoot = $PSScriptRoot
$elanHome = Join-Path $projectRoot ".elan"
$elan = Join-Path $elanHome "bin\elan.exe"
$tools = Join-Path $projectRoot "tools"
$archive = Join-Path $tools "elan.zip"
$installerDirectory = Join-Path $tools "elan"
$installer = Join-Path $installerDirectory "elan-init.exe"
$toolchain = (Get-Content -Raw -LiteralPath (Join-Path $projectRoot "lean-toolchain")).Trim()

$env:ELAN_HOME = $elanHome

if (-not (Test-Path -LiteralPath $elan)) {
  New-Item -ItemType Directory -Force -Path $tools | Out-Null
  Invoke-WebRequest `
    -Uri "https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-pc-windows-msvc.zip" `
    -OutFile $archive
  Expand-Archive -LiteralPath $archive -DestinationPath $installerDirectory -Force
  & $installer -y --no-modify-path --default-toolchain $toolchain
  if ($LASTEXITCODE -ne 0) { throw "Elan installation failed with exit code $LASTEXITCODE." }
} else {
  $installedToolchains = @(& $elan toolchain list)
  if ($toolchain -notin $installedToolchains) {
    & $elan toolchain install $toolchain
    if ($LASTEXITCODE -ne 0) {
      throw "Toolchain installation failed with exit code $LASTEXITCODE."
    }
  }
}

& (Join-Path $projectRoot "lake.ps1") update
& (Join-Path $projectRoot "lake.ps1") exe cache get
