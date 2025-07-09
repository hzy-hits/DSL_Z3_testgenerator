# DSL Test Generator - Complete Setup Guide

This guide will walk you through setting up the DSL Test Generator on a new machine from scratch.

## Table of Contents

1. [System Requirements](#system-requirements)
2. [Installation Methods](#installation-methods)
3. [Project Setup](#project-setup)
4. [Verification](#verification)
5. [Your First Test Generation](#your-first-test-generation)
6. [Troubleshooting](#troubleshooting)
7. [Development Setup](#development-setup)

## System Requirements

### Minimum Requirements

- **Operating System**: macOS, Linux, or Windows 10+
- **Python**: 3.8 or higher
- **Memory**: 4GB RAM (8GB recommended for large models)
- **Disk Space**: 500MB for dependencies

### Required Software

1. **Python 3.8+**
   ```bash
   # Check Python version
   python --version  # Should show 3.8 or higher
   ```

2. **Git** (for cloning the repository)
   ```bash
   # Check Git installation
   git --version
   ```

## Installation Methods

### Method 1: Using UV (Recommended)

UV is a fast Python package installer that handles dependencies automatically.

#### Step 1: Install UV

**macOS/Linux:**
```bash
curl -LsSf https://astral.sh/uv/install.sh | sh
```

**Windows (PowerShell):**
```powershell
irm https://astral.sh/uv/install.ps1 | iex
```

**Alternative (using pip):**
```bash
pip install uv
```

#### Step 2: Clone the Repository

```bash
git clone https://github.com/your-repo/dsl-test-generator.git
cd dsl-test-generator
```

#### Step 3: Run with UV

UV automatically manages dependencies:

```bash
# Generate test cases
uv run ./dsl2test.py demo/examples/hotel_booking_system.yaml

# With output file
uv run ./dsl2test.py demo/examples/insurance_claim_system.yaml -o output/tests.json
```

### Method 2: Using Pip with Virtual Environment

#### Step 1: Clone the Repository

```bash
git clone https://github.com/your-repo/dsl-test-generator.git
cd dsl-test-generator
```

#### Step 2: Create Virtual Environment

**macOS/Linux:**
```bash
python -m venv venv
source venv/bin/activate
```

**Windows:**
```bash
python -m venv venv
venv\Scripts\activate
```

#### Step 3: Install Dependencies

```bash
# Install the package in editable mode
pip install -e .

# Or install specific dependencies
pip install z3-solver pyyaml
```

#### Step 4: Verify Installation

```bash
# Test the CLI tool
python dsl2test.py --help
```

### Method 3: Direct Installation

For quick testing without cloning:

```bash
# Install required packages globally (not recommended for production)
pip install z3-solver pyyaml

# Download and run the tool
wget https://raw.githubusercontent.com/your-repo/dsl-test-generator/main/dsl2test.py
python dsl2test.py your-dsl-file.yaml
```

## Project Setup

### Directory Structure

After setup, your project should look like this:

```
dsl-test-generator/
├── dsl2test.py          # Main CLI tool
├── src/                 # Source code
│   └── dsl_test_generator/
│       ├── core/        # Core engine
│       ├── parsers/     # DSL parsers
│       ├── generators/  # Test generators
│       ├── types/       # Type system
│       └── validators/  # Business logic validators
├── demo/               # Demo files
│   ├── examples/       # Example DSL files
│   ├── outputs/        # Example outputs
│   └── analysis/       # Analysis docs
├── examples/           # More examples
├── docs/              # Documentation
├── output/            # Generated test outputs
└── debug/             # Debug scripts
```

### Configuration

#### Create Configuration File (Optional)

Create `config.json` for custom settings:

```json
{
  "test_generation": {
    "validate_business_logic": true,
    "decimal_precision": 2,
    "negative_test_integer_extension": 1,
    "max_test_cases_per_type": 50
  },
  "solver": {
    "timeout": 10000,
    "random_seed": 42
  }
}
```

## Verification

### Step 1: Verify Python Installation

```bash
python --version
# Expected: Python 3.8.x or higher
```

### Step 2: Verify Z3 Installation

```python
python -c "import z3; print(f'Z3 version: {z3.get_version_string()}')"
# Expected: Z3 version: 4.x.x.x
```

### Step 3: Run Test Generation

```bash
# Using UV
uv run ./dsl2test.py demo/examples/hotel_booking_system.yaml -v

# Using pip installation
python dsl2test.py demo/examples/hotel_booking_system.yaml -v
```

Expected output:
```
Parsing DSL file: demo/examples/hotel_booking_system.yaml
Generating test cases for domain: Hotel Booking System
Optimizing test cases (before: XX tests)
Optimization complete (after: YY tests)
Generation complete:
  Total tests: YY
  Coverage: 100%
```

## Your First Test Generation

### Step 1: Create a Simple DSL File

Create `my_first_dsl.yaml`:

```yaml
domain: My First System

entities:
  - name: User
    attributes:
      - name: age
        type: integer
        min: 0
        max: 120
        description: User age in years
      
      - name: account_type
        type: integer
        min: 1
        max: 3
        enum_values: [1, 2, 3]
        description: Account type (1=Basic, 2=Premium, 3=VIP)
      
      - name: balance
        type: real
        min: 0.0
        max: 1000000.0
        description: Account balance

constraints:
  - user_age >= 18  # Must be adult
  - user_balance >= 0  # No negative balance

rules:
  - name: VIP Benefits
    condition: user_account_type == 3
    implies: user_balance >= 10000
    description: VIP accounts require minimum balance
```

### Step 2: Generate Test Cases

```bash
# Generate and display tests
python dsl2test.py my_first_dsl.yaml

# Save to file
python dsl2test.py my_first_dsl.yaml -o my_tests.json

# Use compact format
python dsl2test.py my_first_dsl.yaml --format compact
```

### Step 3: Review Generated Tests

The output will include:
- Boundary tests (min/max values)
- Equivalence tests (representative values)
- Negative tests (invalid values)
- Rule coverage tests

## Troubleshooting

### Common Issues and Solutions

#### 1. Python Not Found

**Error:** `python: command not found`

**Solution:**
```bash
# Try python3 instead
python3 --version

# Or add Python to PATH
export PATH="/usr/local/bin/python3:$PATH"
```

#### 2. Z3 Installation Failed

**Error:** `No module named 'z3'`

**Solution:**
```bash
# Install with specific version
pip install z3-solver==4.12.0

# Or use system package manager (macOS)
brew install z3
```

#### 3. Permission Denied

**Error:** `Permission denied: './dsl2test.py'`

**Solution:**
```bash
# Make the script executable
chmod +x dsl2test.py
```

#### 4. Module Import Errors

**Error:** `ModuleNotFoundError: No module named 'dsl_test_generator'`

**Solution:**
```bash
# Install in development mode
pip install -e .

# Or add to PYTHONPATH
export PYTHONPATH="${PYTHONPATH}:$(pwd)/src"
```

#### 5. YAML Parse Errors

**Error:** `yaml.scanner.ScannerError`

**Solution:**
- Check YAML syntax (proper indentation)
- Ensure all strings with special characters are quoted
- Validate YAML at: https://www.yamllint.com/

### Platform-Specific Issues

#### macOS
```bash
# If using Homebrew Python
brew install python@3.11
brew link python@3.11

# Install Command Line Tools if needed
xcode-select --install
```

#### Windows
```powershell
# Use Python Launcher
py -3 dsl2test.py my_dsl.yaml

# Fix long path issues
reg add HKLM\SYSTEM\CurrentControlSet\Control\FileSystem /v LongPathsEnabled /t REG_DWORD /d 1
```

#### Linux
```bash
# Install Python development headers
sudo apt-get install python3-dev  # Debian/Ubuntu
sudo yum install python3-devel     # RHEL/CentOS

# Install pip if missing
sudo apt-get install python3-pip
```

## Development Setup

For contributing to the project:

### Step 1: Fork and Clone

```bash
# Fork the repository on GitHub, then:
git clone https://github.com/YOUR-USERNAME/dsl-test-generator.git
cd dsl-test-generator
git remote add upstream https://github.com/ORIGINAL-OWNER/dsl-test-generator.git
```

### Step 2: Development Environment

```bash
# Create development virtual environment
python -m venv venv-dev
source venv-dev/bin/activate  # or venv-dev\Scripts\activate on Windows

# Install in development mode with all extras
pip install -e ".[dev]"
```

### Step 3: Install Development Tools

```bash
# Testing tools
pip install pytest pytest-cov

# Code quality tools
pip install black ruff mypy

# Documentation tools
pip install sphinx sphinx-rtd-theme
```

### Step 4: Run Tests

```bash
# Run all tests
pytest

# Run with coverage
pytest --cov=dsl_test_generator

# Run specific test
pytest tests/test_parser.py::test_parse_valid_dsl
```

### Step 5: Code Quality Checks

```bash
# Format code
black src tests

# Lint code
ruff check src tests

# Type checking
mypy src
```

### Step 6: Create a Branch for Your Feature

```bash
git checkout -b feature/your-feature-name
# Make your changes
git add .
git commit -m "Add your feature"
git push origin feature/your-feature-name
```

## Quick Reference

### CLI Commands

```bash
# Basic usage
./dsl2test.py input.yaml

# With output file
./dsl2test.py input.yaml -o output.json

# Compact format
./dsl2test.py input.yaml --format compact

# Verbose mode
./dsl2test.py input.yaml -v

# No optimization
./dsl2test.py input.yaml --no-optimize

# With configuration
./dsl2test.py input.yaml --config my_config.json
```

### Python API

```python
from dsl_test_generator import DSLParser, DSLEngine, DSLEngineConfig

# Parse DSL
parser = DSLParser()
model = parser.parse_file("my_dsl.yaml")

# Configure engine
config = DSLEngineConfig()
config.test_generation.validate_business_logic = True

# Generate tests
engine = DSLEngine(config)
test_cases = engine.generate_tests(model)

# Process results
for test in test_cases:
    print(f"Test: {test['name']}")
    print(f"Type: {test['type']}")
    print(f"Expected: {test['expected']}")
    print(f"Data: {test['values']}")
```

## Next Steps

1. Read the [User Guide](USER_GUIDE.md) for detailed usage instructions
2. Check [DSL Reference](docs/DSL_REFERENCE.md) for DSL syntax
3. See [API Reference](docs/API_REFERENCE.md) for programming interface
4. Explore [examples/](examples/) directory for more DSL examples

## Getting Help

- **Documentation**: Check the [docs/](docs/) directory
- **Issues**: Report bugs at https://github.com/your-repo/dsl-test-generator/issues
- **Examples**: See [demo/examples/](demo/examples/) for working examples

---

Happy Testing! 🚀