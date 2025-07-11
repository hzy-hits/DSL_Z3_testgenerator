.PHONY: help install install-dev test test-cov lint format clean build upload docs run-example

# Default target
.DEFAULT_GOAL := help

# Python interpreter
PYTHON := python3
PIP := $(PYTHON) -m pip

# Project variables
PROJECT_NAME := dsl-test-generator
PACKAGE_NAME := src
TEST_PATH := tests

help: ## Show this help message
	@echo "DSL Test Generator - Available Commands"
	@echo "======================================"
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | awk 'BEGIN {FS = ":.*?## "}; {printf "\033[36m%-20s\033[0m %s\n", $$1, $$2}'

install: ## Install production dependencies
	$(PIP) install -r requirements.txt

install-dev: ## Install development dependencies
	$(PIP) install -r requirements-dev.txt
	pre-commit install

test: ## Run tests
	$(PYTHON) -m pytest $(TEST_PATH) -v

test-cov: ## Run tests with coverage
	$(PYTHON) -m pytest $(TEST_PATH) -v --cov=$(PACKAGE_NAME) --cov-report=html --cov-report=term-missing

test-quick: ## Run quick tests (no slow tests)
	$(PYTHON) -m pytest $(TEST_PATH) -v -m "not slow"

lint: ## Run linters (flake8, mypy, pylint)
	@echo "Running flake8..."
	$(PYTHON) -m flake8 $(PACKAGE_NAME) $(TEST_PATH)
	@echo "Running mypy..."
	$(PYTHON) -m mypy $(PACKAGE_NAME)
	@echo "Running pylint..."
	$(PYTHON) -m pylint $(PACKAGE_NAME)

format: ## Format code with black and isort
	@echo "Running isort..."
	$(PYTHON) -m isort $(PACKAGE_NAME) $(TEST_PATH) main.py
	@echo "Running black..."
	$(PYTHON) -m black $(PACKAGE_NAME) $(TEST_PATH) main.py

format-check: ## Check code formatting without changes
	$(PYTHON) -m isort --check-only $(PACKAGE_NAME) $(TEST_PATH) main.py
	$(PYTHON) -m black --check $(PACKAGE_NAME) $(TEST_PATH) main.py

security: ## Run security checks with bandit and safety
	@echo "Running bandit..."
	$(PYTHON) -m bandit -r $(PACKAGE_NAME) -ll
	@echo "Running safety check..."
	$(PYTHON) -m safety check

clean: ## Clean build artifacts and cache files
	rm -rf build/
	rm -rf dist/
	rm -rf *.egg-info
	rm -rf .coverage
	rm -rf htmlcov/
	rm -rf .pytest_cache/
	rm -rf .mypy_cache/
	rm -rf .tox/
	find . -type d -name __pycache__ -exec rm -rf {} +
	find . -type f -name '*.pyc' -delete
	find . -type f -name '*.pyo' -delete

clean-outputs: ## Clean generated test outputs
	rm -rf outputs/
	rm -rf test_outputs/

build: clean ## Build distribution packages
	$(PYTHON) -m build

upload-test: ## Upload to TestPyPI
	$(PYTHON) -m twine upload --repository testpypi dist/*

upload: ## Upload to PyPI
	$(PYTHON) -m twine upload dist/*

docs: ## Build documentation
	cd docs && $(MAKE) clean && $(MAKE) html
	@echo "Documentation built in docs/_build/html/"

docs-serve: docs ## Build and serve documentation
	cd docs/_build/html && $(PYTHON) -m http.server

run-example: ## Run example test generation
	$(PYTHON) main.py generate examples/intermediate/shopping_cart.yaml --report

run-batch: ## Run batch test generation
	$(PYTHON) main.py generate --batch examples/

validate-example: ## Validate example test output
	$(PYTHON) main.py generate examples/intermediate/shopping_cart.yaml -o temp_output.json
	$(PYTHON) main.py evaluate temp_output.json
	rm -f temp_output.json

check-all: format-check lint security test ## Run all checks (format, lint, security, test)

dev-setup: install-dev ## Complete development environment setup
	@echo "Development environment ready!"
	@echo "Run 'make help' to see available commands."

bump-version: ## Bump version (usage: make bump-version VERSION=8.1.0)
	@if [ -z "$(VERSION)" ]; then \
		echo "Error: VERSION not specified. Usage: make bump-version VERSION=8.1.0"; \
		exit 1; \
	fi
	@echo "Bumping version to $(VERSION)..."
	@sed -i '' 's/__version__ = ".*"/__version__ = "$(VERSION)"/' src/__init__.py
	@sed -i '' 's/version = ".*"/version = "$(VERSION)"/' pyproject.toml
	@sed -i '' 's/version = ".*"/version = "$(VERSION)"/' setup.py
	@echo "Version bumped to $(VERSION)"

pre-commit: ## Run pre-commit hooks on all files
	pre-commit run --all-files

tox: ## Run tests in multiple Python environments
	tox