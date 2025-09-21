#!/bin/bash

# LeanYo Setup Testing Script
# This script tests all the installation and usage workflows

set -e

echo "🧪 LeanYo Setup Testing Script"
echo "=============================="

# Colors for output
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m' # No Color

# Test functions
test_docker_help() {
    echo -e "${YELLOW}Testing Docker help command...${NC}"
    if docker run --rm ghcr.io/fraware/lean-yo:latest --help >/dev/null 2>&1; then
        echo -e "${GREEN}✅ Docker help command works${NC}"
        return 0
    else
        echo -e "${RED}❌ Docker help command failed${NC}"
        return 1
    fi
}

test_docker_version() {
    echo -e "${YELLOW}Testing Docker version command...${NC}"
    if docker run --rm ghcr.io/fraware/lean-yo:latest --version >/dev/null 2>&1; then
        echo -e "${GREEN}✅ Docker version command works${NC}"
        return 0
    else
        echo -e "${RED}❌ Docker version command failed${NC}"
        return 1
    fi
}

test_makefile_targets() {
    echo -e "${YELLOW}Testing Makefile targets...${NC}"
    
    # Test help target
    if make help >/dev/null 2>&1; then
        echo -e "${GREEN}✅ make help works${NC}"
    else
        echo -e "${RED}❌ make help failed${NC}"
        return 1
    fi
    
    # Test check-deps target
    if make check-deps >/dev/null 2>&1; then
        echo -e "${GREEN}✅ make check-deps works${NC}"
    else
        echo -e "${YELLOW}⚠ make check-deps has warnings (this is normal)${NC}"
    fi
    
    # Test version target
    if make version >/dev/null 2>&1; then
        echo -e "${GREEN}✅ make version works${NC}"
    else
        echo -e "${RED}❌ make version failed${NC}"
        return 1
    fi
    
    return 0
}

test_local_build() {
    echo -e "${YELLOW}Testing local build...${NC}"
    
    if command -v lake >/dev/null 2>&1; then
        echo -e "${GREEN}✅ Lake found${NC}"
        
        # Test lake build
        if lake build >/dev/null 2>&1; then
            echo -e "${GREEN}✅ lake build works${NC}"
            return 0
        else
            echo -e "${RED}❌ lake build failed${NC}"
            return 1
        fi
    else
        echo -e "${YELLOW}⚠ Lake not found - skipping local build test${NC}"
        return 0
    fi
}

test_production_scripts() {
    echo -e "${YELLOW}Testing production scripts...${NC}"
    
    if [ -f "scripts/production_test.py" ]; then
        echo -e "${GREEN}✅ Production test script found${NC}"
    else
        echo -e "${YELLOW}⚠ Production test script not found${NC}"
    fi
    
    if [ -f "scripts/validate_lemmas.py" ]; then
        echo -e "${GREEN}✅ Lemma validation script found${NC}"
    else
        echo -e "${YELLOW}⚠ Lemma validation script not found${NC}"
    fi
    
    return 0
}

test_documentation() {
    echo -e "${YELLOW}Testing documentation...${NC}"
    
    if [ -f "README.md" ]; then
        echo -e "${GREEN}✅ README.md found${NC}"
    else
        echo -e "${RED}❌ README.md not found${NC}"
        return 1
    fi
    
    if [ -d "docs" ]; then
        echo -e "${GREEN}✅ docs/ directory found${NC}"
    else
        echo -e "${YELLOW}⚠ docs/ directory not found${NC}"
    fi
    
    return 0
}

test_ci_workflows() {
    echo -e "${YELLOW}Testing CI workflows...${NC}"
    
    if [ -f ".github/workflows/ci.yml" ]; then
        echo -e "${GREEN}✅ CI workflow found${NC}"
    else
        echo -e "${RED}❌ CI workflow not found${NC}"
        return 1
    fi
    
    if [ -f ".github/workflows/release.yml" ]; then
        echo -e "${GREEN}✅ Release workflow found${NC}"
    else
        echo -e "${RED}❌ Release workflow not found${NC}"
        return 1
    fi
    
    return 0
}

# Main test execution
main() {
    echo -e "${YELLOW}Running comprehensive setup tests...${NC}"
    echo ""
    
    local failed_tests=0
    
    # Run all tests
    test_makefile_targets || ((failed_tests++))
    echo ""
    
    test_local_build || ((failed_tests++))
    echo ""
    
    test_production_scripts || ((failed_tests++))
    echo ""
    
    test_documentation || ((failed_tests++))
    echo ""
    
    test_ci_workflows || ((failed_tests++))
    echo ""
    
    # Docker tests (may fail if image not built yet)
    echo -e "${YELLOW}Testing Docker (may fail if image not built)...${NC}"
    if test_docker_help && test_docker_version; then
        echo -e "${GREEN}✅ Docker tests passed${NC}"
    else
        echo -e "${YELLOW}⚠ Docker tests failed (image may not be built yet)${NC}"
    fi
    echo ""
    
    # Summary
    echo "=============================="
    if [ $failed_tests -eq 0 ]; then
        echo -e "${GREEN}🎉 All critical tests passed!${NC}"
        echo ""
        echo "Next steps:"
        echo "1. Build Docker image: make docker-build"
        echo "2. Test full workflow: make ci"
        echo "3. Create a release: git tag v1.0.0 && git push --tags"
        exit 0
    else
        echo -e "${RED}❌ $failed_tests test(s) failed${NC}"
        echo ""
        echo "Please fix the issues above before proceeding."
        exit 1
    fi
}

# Check if running from correct directory
if [ ! -f "lakefile.lean" ]; then
    echo -e "${RED}Error: Please run this script from the lean-yo project root${NC}"
    exit 1
fi

main "$@"
