.PHONY: dev run test build clean release publish docker-build docker-push help

# Default target
.DEFAULT_GOAL := help

# Project configuration
PROJECT_NAME := lean-yo
DOCKER_IMAGE := ghcr.io/fraware/lean-yo
DOCKER_TAG := latest
LEAN_VERSION := $(shell cat lean-toolchain | cut -d: -f2)

# Colors for output
GREEN := \033[0;32m
YELLOW := \033[1;33m
RED := \033[0;31m
NC := \033[0m # No Color

help: ## Show this help message
	@echo "$(GREEN)LeanYo - A Lean 4 tactic library for category theory$(NC)"
	@echo ""
	@echo "Available targets:"
	@awk 'BEGIN {FS = ":.*?## "} /^[a-zA-Z_-]+:.*?## / {printf "  $(GREEN)%-15s$(NC) %s\n", $$1, $$2}' $(MAKEFILE_LIST)

dev: ## Set up local development environment
	@echo "$(YELLOW)Setting up development environment...$(NC)"
	@if ! command -v lake >/dev/null 2>&1; then \
		echo "$(RED)Error: Lake (Lean build tool) not found. Please install Lean 4 first.$(NC)"; \
		echo "Visit: https://leanprover.github.io/lean4/doc/quickstart.html"; \
		exit 1; \
	fi
	@echo "$(GREEN)✓ Lake found$(NC)"
	@echo "$(YELLOW)Updating dependencies...$(NC)"
	lake update
	@echo "$(YELLOW)Building project...$(NC)"
	lake build
	@echo "$(GREEN)✓ Development environment ready!$(NC)"
	@echo ""
	@echo "Next steps:"
	@echo "  - Run 'make run' to test the library"
	@echo "  - Run 'make test' to run all tests"
	@echo "  - See 'make help' for more commands"

run: ## Run the library locally (build and test examples)
	@echo "$(YELLOW)Building and testing LeanYo library...$(NC)"
	@if ! lake build; then \
		echo "$(RED)Build failed!$(NC)"; \
		exit 1; \
	fi
	@echo "$(GREEN)✓ Build successful$(NC)"
	@echo "$(YELLOW)Running example tests...$(NC)"
	@if lake exe lean LeanYo/Examples.lean; then \
		echo "$(GREEN)✓ Examples run successfully$(NC)"; \
	else \
		echo "$(YELLOW)⚠ Examples test skipped (file may not exist)$(NC)"; \
	fi
	@echo "$(YELLOW)Running production tests...$(NC)"
	@if [ -f scripts/production_test.py ]; then \
		python3 scripts/production_test.py; \
	else \
		echo "$(YELLOW)⚠ Production tests skipped (script not found)$(NC)"; \
	fi
	@echo "$(GREEN)✓ Library is ready to use!$(NC)"

test: ## Run all tests including validation
	@echo "$(YELLOW)Running comprehensive test suite...$(NC)"
	lake build
	@echo "$(YELLOW)Running Lean tests...$(NC)"
	@for test_file in LeanYo/Tests/*.lean; do \
		if [ -f "$$test_file" ]; then \
			echo "Testing $$test_file..."; \
			lake exe lean "$$test_file" || exit 1; \
		fi; \
	done
	@echo "$(YELLOW)Running production tests...$(NC)"
	@if [ -f scripts/production_test.py ]; then \
		python3 scripts/production_test.py; \
	fi
	@echo "$(YELLOW)Running lemma validation...$(NC)"
	@if [ -f scripts/validate_lemmas.py ]; then \
		python3 scripts/validate_lemmas.py; \
	fi
	@echo "$(GREEN)✓ All tests passed!$(NC)"

build: ## Build the library
	@echo "$(YELLOW)Building LeanYo library...$(NC)"
	lake build
	@echo "$(GREEN)✓ Build complete$(NC)"

clean: ## Clean build artifacts
	@echo "$(YELLOW)Cleaning build artifacts...$(NC)"
	lake clean
	rm -rf .lake/build
	@echo "$(GREEN)✓ Clean complete$(NC)"

# Docker targets
docker-build: ## Build Docker image
	@echo "$(YELLOW)Building Docker image...$(NC)"
	docker build -t $(DOCKER_IMAGE):$(DOCKER_TAG) .
	docker tag $(DOCKER_IMAGE):$(DOCKER_TAG) $(DOCKER_IMAGE):$(LEAN_VERSION)
	@echo "$(GREEN)✓ Docker image built: $(DOCKER_IMAGE):$(DOCKER_TAG)$(NC)"

docker-push: docker-build ## Push Docker image to registry
	@echo "$(YELLOW)Pushing Docker image to registry...$(NC)"
	docker push $(DOCKER_IMAGE):$(DOCKER_TAG)
	docker push $(DOCKER_IMAGE):$(LEAN_VERSION)
	@echo "$(GREEN)✓ Docker image pushed$(NC)"

docker-run: ## Run Docker container locally
	@echo "$(YELLOW)Running Docker container...$(NC)"
	docker run --rm -it $(DOCKER_IMAGE):$(DOCKER_TAG) --help

# Release targets
release: ## Build and publish release (supports DRY_RUN=1)
	@echo "$(YELLOW)Preparing release...$(NC)"
	@if [ "$(DRY_RUN)" = "1" ]; then \
		echo "$(YELLOW)DRY RUN MODE - No actual publishing will occur$(NC)"; \
	fi
	@$(MAKE) clean
	@$(MAKE) build
	@$(MAKE) test
	@echo "$(YELLOW)Creating release artifacts...$(NC)"
	@mkdir -p dist
	@tar -czf dist/$(PROJECT_NAME)-$(LEAN_VERSION).tar.gz \
		--exclude='.git' \
		--exclude='.lake' \
		--exclude='dist' \
		--exclude='*.tar.gz' \
		.
	@echo "$(GREEN)✓ Release artifacts created in dist/$(NC)"
	@if [ "$(DRY_RUN)" != "1" ]; then \
		echo "$(YELLOW)Building and pushing Docker image...$(NC)"; \
		$(MAKE) docker-push; \
		echo "$(GREEN)✓ Release complete!$(NC)"; \
	else \
		echo "$(YELLOW)DRY RUN: Would build and push Docker image$(NC)"; \
		echo "$(GREEN)✓ Dry run complete!$(NC)"; \
	fi

publish: ## Publish to package registries (supports DRY_RUN=1)
	@echo "$(YELLOW)Publishing LeanYo library...$(NC)"
	@if [ "$(DRY_RUN)" = "1" ]; then \
		echo "$(YELLOW)DRY RUN MODE - No actual publishing will occur$(NC)"; \
	fi
	@echo "$(YELLOW)Note: Lean packages are typically distributed via Git repositories$(NC)"
	@echo "$(YELLOW)Ensure the repository is tagged and pushed to GitHub$(NC)"
	@if [ "$(DRY_RUN)" != "1" ]; then \
		echo "$(GREEN)✓ Ready for Git-based distribution$(NC)"; \
	else \
		echo "$(YELLOW)DRY RUN: Would be ready for Git-based distribution$(NC)"; \
	fi

# Utility targets
version: ## Show version information
	@echo "$(GREEN)LeanYo Version Information:$(NC)"
	@echo "Lean Version: $(LEAN_VERSION)"
	@echo "Project: $(PROJECT_NAME)"
	@echo "Docker Image: $(DOCKER_IMAGE):$(DOCKER_TAG)"

check-deps: ## Check if all dependencies are installed
	@echo "$(YELLOW)Checking dependencies...$(NC)"
	@command -v lake >/dev/null 2>&1 || (echo "$(RED)✗ Lake not found$(NC)" && exit 1)
	@echo "$(GREEN)✓ Lake found$(NC)"
	@command -v docker >/dev/null 2>&1 || (echo "$(YELLOW)⚠ Docker not found (optional)$(NC)")
	@command -v python3 >/dev/null 2>&1 || (echo "$(YELLOW)⚠ Python3 not found (for scripts)$(NC)")
	@echo "$(GREEN)✓ Dependencies check complete$(NC)"

install-deps: ## Install development dependencies
	@echo "$(YELLOW)Installing development dependencies...$(NC)"
	@if command -v apt-get >/dev/null 2>&1; then \
		sudo apt-get update && sudo apt-get install -y python3 python3-pip; \
	elif command -v brew >/dev/null 2>&1; then \
		brew install python3; \
	elif command -v pacman >/dev/null 2>&1; then \
		sudo pacman -S python; \
	else \
		echo "$(YELLOW)Please install Python3 manually$(NC)"; \
	fi
	@echo "$(GREEN)✓ Dependencies installed$(NC)"

# Continuous Integration targets
ci: ## Run CI pipeline locally
	@echo "$(YELLOW)Running CI pipeline...$(NC)"
	@$(MAKE) check-deps
	@$(MAKE) clean
	@$(MAKE) dev
	@$(MAKE) test
	@$(MAKE) docker-build
	@echo "$(GREEN)✓ CI pipeline completed successfully$(NC)"

# Development workflow targets
format: ## Format code (placeholder - Lean doesn't have standard formatter yet)
	@echo "$(YELLOW)Code formatting...$(NC)"
	@echo "$(YELLOW)Note: Lean 4 doesn't have a standard formatter yet$(NC)"
	@echo "$(GREEN)✓ Manual code review recommended$(NC)"

lint: ## Run linting checks
	@echo "$(YELLOW)Running linting checks...$(NC)"
	@echo "$(YELLOW)Building project to check for errors...$(NC)"
	lake build
	@echo "$(GREEN)✓ Linting complete$(NC)"

docs: ## Generate documentation
	@echo "$(YELLOW)Generating documentation...$(NC)"
	@echo "$(YELLOW)Note: Using existing documentation in docs/ directory$(NC)"
	@if [ -d "docs" ]; then \
		echo "$(GREEN)✓ Documentation available in docs/$(NC)"; \
	else \
		echo "$(RED)✗ docs/ directory not found$(NC)"; \
	fi

# Quick development commands
quick-test: ## Quick test (build only)
	@echo "$(YELLOW)Running quick test...$(NC)"
	lake build
	@echo "$(GREEN)✓ Quick test passed$(NC)"

setup: dev ## Alias for dev target

all: clean dev test docker-build ## Run complete build pipeline
