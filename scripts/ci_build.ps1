# Windows equivalent of scripts/ci_build.sh (PowerShell / Git Bash without LF scripts).
$ErrorActionPreference = 'Stop'
Set-Location (Join-Path $PSScriptRoot '..')

lake update
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
lake build LeanYo
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
lake build LeanYo.Examples
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
lake build LeanYoTests
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
Write-Host 'LeanYoTests: pass'
