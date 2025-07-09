# Contributing to DSL Test Generator

Thank you for your interest in contributing to the DSL Test Generator! This document provides guidelines and instructions for contributing.

## Table of Contents

1. [Code of Conduct](#code-of-conduct)
2. [Getting Started](#getting-started)
3. [Development Process](#development-process)
4. [Code Style](#code-style)
5. [Testing](#testing)
6. [Documentation](#documentation)
7. [Pull Request Process](#pull-request-process)

## Code of Conduct

- Be respectful and inclusive
- Welcome newcomers and help them get started
- Focus on constructive criticism
- Respect differing viewpoints and experiences

## Getting Started

### 1. Fork and Clone

```bash
# Fork the repository on GitHub
# Then clone your fork
git clone https://github.com/YOUR-USERNAME/dsl-test-generator.git
cd dsl-test-generator
git remote add upstream https://github.com/ORIGINAL/dsl-test-generator.git
```

### 2. Set Up Development Environment

```bash
# Create virtual environment
python -m venv venv-dev
source venv-dev/bin/activate  # Windows: venv-dev\Scripts\activate

# Install in development mode
pip install -e ".[dev]"

# Install pre-commit hooks (optional)
pip install pre-commit
pre-commit install
```

### 3. Create a Branch

```bash
# Update main branch
git checkout main
git pull upstream main

# Create feature branch
git checkout -b feature/your-feature-name
# or
git checkout -b fix/issue-description
```

## Development Process

### 1. Make Your Changes

- Write clean, readable code
- Follow the existing code style
- Add comments for complex logic
- Update tests as needed

### 2. Test Your Changes

```bash
# Run all tests
pytest

# Run specific test
pytest tests/test_parser.py

# Run with coverage
pytest --cov=dsl_test_generator

# Check code style
black --check src tests
ruff check src tests
mypy src
```

### 3. Update Documentation

- Update docstrings for new functions/classes
- Update README.md if adding features
- Add to API_REFERENCE.md for new APIs
- Update CHANGELOG.md (unreleased section)

## Code Style

### Python Style Guide

We follow PEP 8 with these preferences:

```python
# Imports
import os
import sys
from typing import Dict, List, Optional

from third_party import module

from ..types import DSLModel
from .utils import helper


# Class definitions
class MyClass:
    """Brief description.
    
    Longer description if needed.
    
    Args:
        param1: Description
        param2: Description
    """
    
    def __init__(self, param1: str, param2: Optional[int] = None):
        self.param1 = param1
        self.param2 = param2


# Function definitions
def process_data(input_data: Dict[str, Any]) -> List[str]:
    """Process input data and return results.
    
    Args:
        input_data: Dictionary containing...
        
    Returns:
        List of processed strings
        
    Raises:
        ValueError: If input_data is invalid
    """
    if not input_data:
        raise ValueError("Input data cannot be empty")
    
    # Process data
    results = []
    for key, value in input_data.items():
        # Comment explaining complex logic
        processed = f"{key}: {value}"
        results.append(processed)
    
    return results
```

### Formatting Tools

```bash
# Format code automatically
black src tests

# Check linting
ruff check src tests

# Type checking
mypy src
```

## Testing

### Test Structure

```
tests/
├── unit/           # Unit tests for individual components
├── integration/    # Integration tests
├── fixtures/       # Test data and fixtures
└── conftest.py    # Pytest configuration
```

### Writing Tests

```python
# tests/unit/test_my_module.py
import pytest
from dsl_test_generator.my_module import MyClass


class TestMyClass:
    """Test cases for MyClass."""
    
    def test_initialization(self):
        """Test MyClass initialization."""
        obj = MyClass("test", 42)
        assert obj.param1 == "test"
        assert obj.param2 == 42
    
    def test_invalid_input(self):
        """Test handling of invalid input."""
        with pytest.raises(ValueError, match="cannot be empty"):
            MyClass("", None)
    
    @pytest.mark.parametrize("input_val,expected", [
        ("test1", "result1"),
        ("test2", "result2"),
    ])
    def test_processing(self, input_val, expected):
        """Test data processing with various inputs."""
        obj = MyClass(input_val)
        assert obj.process() == expected
```

### Test Guidelines

1. Write tests for new features
2. Ensure existing tests pass
3. Aim for >80% code coverage
4. Use descriptive test names
5. Test edge cases and errors

## Documentation

### Docstring Format

Use Google-style docstrings:

```python
def function(param1: str, param2: int = 0) -> bool:
    """Brief description of function.
    
    Longer description providing more detail about what
    the function does and any important notes.
    
    Args:
        param1: Description of param1
        param2: Description of param2. Defaults to 0.
        
    Returns:
        Description of return value
        
    Raises:
        ValueError: When param1 is empty
        TypeError: When param2 is not an integer
        
    Example:
        >>> function("test", 42)
        True
    """
```

### Documentation Updates

When adding features, update:

1. **README.md**: If changing main functionality
2. **API_REFERENCE.md**: For new public APIs
3. **DSL_REFERENCE.md**: For DSL syntax changes
4. **CHANGELOG.md**: Add to "Unreleased" section
5. **Examples**: Add example files if appropriate

## Pull Request Process

### 1. Before Submitting

- [ ] All tests pass (`pytest`)
- [ ] Code is formatted (`black src tests`)
- [ ] No linting errors (`ruff check src tests`)
- [ ] Type hints added (`mypy src`)
- [ ] Documentation updated
- [ ] CHANGELOG.md updated

### 2. PR Description Template

```markdown
## Description
Brief description of changes

## Type of Change
- [ ] Bug fix
- [ ] New feature
- [ ] Breaking change
- [ ] Documentation update

## Testing
- [ ] Unit tests pass
- [ ] Integration tests pass
- [ ] Manual testing completed

## Checklist
- [ ] Code follows style guidelines
- [ ] Self-review completed
- [ ] Documentation updated
- [ ] Tests added/updated
```

### 3. Review Process

1. Submit PR against `main` branch
2. Ensure CI passes
3. Respond to review feedback
4. Squash commits if requested
5. PR will be merged by maintainers

## Issue Guidelines

### Bug Reports

Include:
- Python version
- OS information
- Steps to reproduce
- Expected vs actual behavior
- Error messages/stack traces

### Feature Requests

Include:
- Use case description
- Proposed solution
- Alternative solutions considered
- Impact on existing functionality

## Release Process

1. Update version in `pyproject.toml`
2. Update CHANGELOG.md
3. Create release PR
4. Tag release after merge
5. Publish to PyPI (maintainers only)

## Getting Help

- Check existing issues and PRs
- Read documentation thoroughly
- Ask in discussions/issues
- Be patient and respectful

## Recognition

Contributors will be recognized in:
- CHANGELOG.md
- GitHub contributors page
- Release notes

Thank you for contributing! 🎉