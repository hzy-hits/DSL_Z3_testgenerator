# DSL Test Generator - User Guide

## Overview

The DSL Test Generator is a powerful tool that converts business requirement specifications written in a Domain Specific Language (DSL) into comprehensive test cases using the Z3 SMT solver. It automatically generates boundary tests, equivalence tests, negative tests, and rule coverage tests to ensure 100% test coverage.

## Quick Start

### Installation

1. **Prerequisites**
   - Python 3.8 or higher
   - macOS, Linux, or Windows

2. **Install with uv (Recommended)**
   ```bash
   # Install uv if you haven't already
   curl -LsSf https://astral.sh/uv/install.sh | sh
   
   # Clone the repository
   git clone <repository-url>
   cd test_generate
   
   # Run with uv (automatically handles dependencies)
   uv run ./dsl2test.py <your-dsl-file.yaml>
   ```

3. **Install with pip (Alternative)**
   ```bash
   # Create virtual environment
   python -m venv .venv
   source .venv/bin/activate  # On Windows: .venv\Scripts\activate
   
   # Install dependencies
   pip install z3-solver pyyaml
   ```

### Basic Usage

```bash
# Generate test cases and print to console
./dsl2test.py demo/hotel_booking_system.yaml

# Save test cases to a file
./dsl2test.py demo/hotel_booking_system.yaml -o tests.json

# Use compact format (less verbose)
./dsl2test.py demo/insurance_claim_system.yaml --format compact

# Enable verbose output
./dsl2test.py my_dsl.yaml -v

# Disable test optimization
./dsl2test.py my_dsl.yaml --no-optimize
```

## Command Line Options

| Option | Description |
|--------|-------------|
| `dsl_file` | Path to the DSL file (required) |
| `-o, --output` | Output file path (default: stdout) |
| `-f, --format` | Output format: `full` or `compact` (default: full) |
| `--no-optimize` | Disable test case deduplication |
| `-v, --verbose` | Enable verbose output |

## Output Formats

### Full Format
Includes comprehensive statistics and detailed test information:
```json
{
  "summary": {
    "total_tests": 85,
    "positive_tests": 42,
    "negative_tests": 43,
    "coverage_rate": "100%",
    "test_distribution": {
      "boundary": 12,
      "equivalence": 6,
      "rule_coverage": 17,
      "negative": 43,
      "edge_case": 2
    }
  },
  "test_suites": {
    "boundary": [...],
    "negative": [...],
    ...
  }
}
```

### Compact Format
Simplified output with just the test cases:
```json
{
  "total": 85,
  "test_cases": [
    {
      "name": "boundary_age_min",
      "type": "boundary",
      "expected": "pass",
      "data": {
        "age": 18,
        "member_level": "Regular",
        ...
      }
    },
    ...
  ]
}
```

## Test Types Generated

### 1. Boundary Tests
Tests at the minimum and maximum valid values for numeric attributes.

### 2. Equivalence Tests
Tests for each valid value in enumerated types.

### 3. Rule Coverage Tests
Tests that ensure each business rule is activated and tested.

### 4. Negative Tests
Tests with invalid values to ensure proper error handling:
- Values below minimum
- Values above maximum
- Invalid enum values
- Rule violation scenarios

### 5. Edge Case Tests
Complex scenarios combining multiple conditions.

## Example Domains

### Hotel Booking System
```bash
./dsl2test.py demo/hotel_booking_system.yaml -o hotel_tests.json
```

Generates tests for:
- Customer age validation (18-100)
- Member levels (Regular, Silver, Gold)
- Room types (Standard, Deluxe, Suite)
- Discount rules
- Peak season constraints

### Insurance Claim System
```bash
./dsl2test.py demo/insurance_claim_system.yaml -o insurance_tests.json
```

Generates tests for:
- Policy types (Health, Auto, Home, Life)
- Claim validation
- Fraud detection
- Deductible application
- Premium payment verification

## Integration with Test Frameworks

The generated JSON can be easily integrated with various test frameworks:

### Python (pytest)
```python
import json
import pytest

with open('tests.json') as f:
    test_data = json.load(f)

@pytest.mark.parametrize("test_case", test_data['test_cases'])
def test_business_rules(test_case):
    # Your test implementation
    assert execute_test(test_case['data']) == test_case['expected']
```

### JavaScript (Jest)
```javascript
const testData = require('./tests.json');

describe('Business Rules', () => {
  testData.test_cases.forEach(testCase => {
    it(testCase.name, () => {
      const result = executeTest(testCase.data);
      expect(result).toBe(testCase.expected);
    });
  });
});
```

## Performance Optimization

The tool automatically optimizes test cases by:
1. **Deduplication**: Removes redundant test cases
2. **Merging**: Combines similar tests with different descriptions
3. **Smart Generation**: Generates minimal set for 100% coverage

To see the optimization in action:
```bash
./dsl2test.py my_dsl.yaml -v
# Output: Optimizing test cases (before: 95 tests)
#         Optimization complete (after: 88 tests)
```

## Troubleshooting

### Common Issues

1. **Module not found error**
   ```bash
   # Use uv to automatically manage dependencies
   uv run ./dsl2test.py my_dsl.yaml
   ```

2. **DSL parsing errors**
   - Ensure YAML syntax is correct
   - Check that all required fields have `name` attribute
   - Validate constraint expressions

3. **No test cases generated**
   - Verify DSL has valid entities and attributes
   - Check that constraints are not contradictory

### Debug Mode
Use verbose mode to see detailed processing:
```bash
./dsl2test.py my_dsl.yaml -v
```

## Best Practices

1. **Start Simple**: Begin with basic entities and add complexity gradually
2. **Use Descriptive Names**: Clear attribute and rule names improve test readability
3. **Define Clear Constraints**: Explicit min/max values help generate better tests
4. **Include Test Requirements**: Guide test generation with specific requirements
5. **Review Generated Tests**: Verify the tests match your business logic

## Advanced Usage

### Configuration

The DSL Test Generator supports configuration files and environment variables to customize its behavior:

#### Using Configuration File

Create a `dsl_config.json` file:

```json
{
  "test_generation": {
    "validate_business_logic": true,
    "decimal_precision": 2,
    "negative_test_integer_extension": 2,
    "max_test_cases_per_type": 50
  },
  "solver": {
    "timeout": 10000,
    "random_seed": 42
  }
}
```

Then use it with:
```bash
./dsl2test.py my_dsl.yaml --config dsl_config.json
```

#### Programmatic Configuration

When using the Python API:

```python
from dsl_test_generator import DSLParser, DSLEngine, DSLEngineConfig

# Create custom configuration
config = DSLEngineConfig()
config.test_generation.validate_business_logic = True
config.test_generation.decimal_precision = 2
config.solver.timeout = 10000  # 10 seconds

# Parse and generate tests
parser = DSLParser()
model = parser.parse_file("my_dsl.yaml")

engine = DSLEngine(config)
test_cases = engine.generate_tests(model)
```

#### Configuration Options

**Test Generation Options:**
- `validate_business_logic`: Enable/disable business logic validation (default: True)
- `decimal_precision`: Number of decimal places for real numbers (default: 6)
- `negative_test_integer_extension`: How far beyond bounds to test (default: 1)
- `max_test_cases_per_type`: Maximum tests per type (default: 100)

**Solver Options:**
- `timeout`: Z3 solver timeout in milliseconds (default: 5000)
- `random_seed`: For reproducible test generation (default: None)

### Custom Test Requirements

You can specify custom test generation strategies in your DSL:

```yaml
test_requirements:
  - name: Critical Path Tests
    type: combinatorial
    combinations: 3
    focus: [payment_method, shipping_type, customer_type]
    description: Test critical business combinations
```

### Continuous Integration

Integrate into CI/CD pipeline:
```bash
# GitHub Actions example
- name: Generate Test Cases
  run: |
    uv run ./dsl2test.py requirements.yaml -o test_cases.json
    echo "Generated $(jq '.total' test_cases.json) test cases"
```

## Support

For issues, feature requests, or contributions:
- GitHub Issues: [Report issues](https://github.com/anthropics/claude-code/issues)
- Documentation: See DSL_GUIDE.md for DSL syntax
- Examples: Check the `demo/` directory

## License

This tool is part of the DSL Test Generator project. See LICENSE for details.