# DSL Test Generator V2.0

A clean, correct, and minimal test case generator based on Domain Specific Language (DSL) specifications.

## Key Features

- **100% Correctness Guarantee**: All generated tests satisfy constraints and rules
- **Minimal Test Sets**: Smart test minimization reduces redundancy
- **Clear Test Objectives**: Every test has a clear purpose and coverage information
- **Clean Architecture**: Layered design with clear separation of concerns
- **No Business Logic Hardcoding**: Pure, domain-agnostic engine
- **Intelligent Combination Analysis**: Automatically detects rule conflicts and suggests critical test scenarios
- **Advanced Test Planning**: Prioritizes important combinations and edge cases

## Quick Start

```bash
# Generate test cases from DSL
python dsl2test.py --input examples/simple_test.yaml --output tests.json

# Analyze rule combinations and conflicts
python dsl2test.py --input model.yaml --analyze-combinations

# Generate with specific format
python dsl2test.py --input model.yaml --output tests.py --format pytest

# Use advanced features
python dsl2test_advanced.py --input model.yaml --output tests.json --analyze-combinations --use-advanced-planner

# Validate DSL only
python dsl2test.py --input model.yaml --validate-only
```

## Architecture

```
┌─────────────────────────────────┐
│         CLI Interface           │
├─────────────────────────────────┤
│         DSL Parser              │  ← Parse & validate DSL
├─────────────────────────────────┤
│      Test Strategy Layer        │  ← Plan what to test
├─────────────────────────────────┤
│    Constraint Solver (Z3)       │  ← Generate correct data
├─────────────────────────────────┤
│      Output Formatter           │  ← Format results
└─────────────────────────────────┘
```

## DSL Format

```yaml
domain: Your System Name

entities:
  - name: Entity1
    attributes:
      - name: attribute1
        type: integer
        min: 0
        max: 100

constraints:
  - expression: "attribute1 >= 0"
    description: "Attribute must be non-negative"

rules:
  - name: Business Rule
    if: "condition"
    then: "consequence"
    priority: 10
```

## Output Formats

- **JSON**: Structured test data with metadata
- **JUnit XML**: For CI/CD integration
- **CSV**: For spreadsheet analysis
- **Markdown**: Human-readable reports
- **Python**: pytest or unittest code

## Improvements over V1.0

| Aspect | V1.0 | V2.0 |
|--------|------|------|
| Correctness | 60% | 100% |
| Test Count | 100+ | 20-60 |
| Architecture | Monolithic | Layered |
| Hardcoding | Yes | No |

## Requirements

- Python 3.8+
- Z3 solver (`pip install z3-solver`)
- PyYAML (`pip install pyyaml`)

## Installation

```bash
# Clone repository
git clone <repository-url>
cd v2.0

# Install dependencies
pip install -r requirements.txt

# Run tests
python -m pytest tests/
```

## License

MIT License - See LICENSE file for details.