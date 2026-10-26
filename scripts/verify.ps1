$ErrorActionPreference = 'Stop'
$env:LEAN_NUM_THREADS = '1'
Set-Location (Join-Path $PSScriptRoot '..')

$py = if (Get-Command python -ErrorAction SilentlyContinue) { 'python' } else { 'py' }

Write-Host '== lake build ==' -ForegroundColor Cyan
lake build
if ($LASTEXITCODE -ne 0) { exit 1 }

$checks = @(
    'check_no_forbidden.py',
    'check_dependencies.py',
    'check_coverage.py',
    'check_docstring_verbatim.py',
    'check_import_dag.py',
    'check_sorry.py',
    'check_axioms.py',
    'check_zones.py'
)

foreach ($c in $checks) {
    Write-Host "== $c ==" -ForegroundColor Cyan
    & $py "scripts/$c"
    if ($LASTEXITCODE -ne 0) { exit 1 }
}

Write-Host '== generation checks ==' -ForegroundColor Cyan
& $py 'scripts/tex_extract.py' --check
if ($LASTEXITCODE -ne 0) { exit 1 }
& $py 'scripts/gen_lean.py' --check
if ($LASTEXITCODE -ne 0) { exit 1 }

Write-Host 'all checks passed' -ForegroundColor Green
