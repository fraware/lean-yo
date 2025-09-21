@echo off
REM LeanYo Setup Testing Script for Windows
REM This script tests all the installation and usage workflows

echo 🧪 LeanYo Setup Testing Script (Windows)
echo ==========================================

set "failed_tests=0"

echo Testing Makefile targets...
make help >nul 2>&1
if %errorlevel% equ 0 (
    echo ✅ make help works
) else (
    echo ❌ make help failed
    set /a "failed_tests+=1"
)

make version >nul 2>&1
if %errorlevel% equ 0 (
    echo ✅ make version works
) else (
    echo ❌ make version failed
    set /a "failed_tests+=1"
)

echo.
echo Testing local build...
where lake >nul 2>&1
if %errorlevel% equ 0 (
    echo ✅ Lake found
    lake build >nul 2>&1
    if %errorlevel% equ 0 (
        echo ✅ lake build works
    ) else (
        echo ❌ lake build failed
        set /a "failed_tests+=1"
    )
) else (
    echo ⚠ Lake not found - skipping local build test
)

echo.
echo Testing production scripts...
if exist "scripts\production_test.py" (
    echo ✅ Production test script found
) else (
    echo ⚠ Production test script not found
)

if exist "scripts\validate_lemmas.py" (
    echo ✅ Lemma validation script found
) else (
    echo ⚠ Lemma validation script not found
)

echo.
echo Testing documentation...
if exist "README.md" (
    echo ✅ README.md found
) else (
    echo ❌ README.md not found
    set /a "failed_tests+=1"
)

if exist "docs" (
    echo ✅ docs\ directory found
) else (
    echo ⚠ docs\ directory not found
)

echo.
echo Testing CI workflows...
if exist ".github\workflows\ci.yml" (
    echo ✅ CI workflow found
) else (
    echo ❌ CI workflow not found
    set /a "failed_tests+=1"
)

if exist ".github\workflows\release.yml" (
    echo ✅ Release workflow found
) else (
    echo ❌ Release workflow not found
    set /a "failed_tests+=1"
)

echo.
echo Testing Docker (may fail if image not built)...
docker run --rm ghcr.io/fraware/lean-yo:latest --help >nul 2>&1
if %errorlevel% equ 0 (
    echo ✅ Docker help command works
    docker run --rm ghcr.io/fraware/lean-yo:latest --version >nul 2>&1
    if %errorlevel% equ 0 (
        echo ✅ Docker version command works
    ) else (
        echo ⚠ Docker version command failed
    )
) else (
    echo ⚠ Docker tests failed (image may not be built yet)
)

echo.
echo ==========================================
if %failed_tests% equ 0 (
    echo 🎉 All critical tests passed!
    echo.
    echo Next steps:
    echo 1. Build Docker image: make docker-build
    echo 2. Test full workflow: make ci
    echo 3. Create a release: git tag v1.0.0 ^&^& git push --tags
    exit /b 0
) else (
    echo ❌ %failed_tests% test(s) failed
    echo.
    echo Please fix the issues above before proceeding.
    exit /b 1
)
