# DSL Test Generator - Project Overview

## 🎯 Purpose

The DSL Test Generator is a sophisticated tool that automatically generates comprehensive test cases from Domain-Specific Language (DSL) specifications. It uses the Z3 SMT solver to ensure mathematical correctness and generates tests that achieve 100% coverage without manual intervention.

## 🏗️ Architecture

### Core Components

```
┌─────────────────┐     ┌──────────────┐     ┌──────────────┐
│   DSL Parser    │────▶│  DSL Model   │────▶│  DSL Engine  │
│  (YAML → Model) │     │  (Entities,  │     │  (Test Gen)  │
└─────────────────┘     │ Constraints) │     └──────────────┘
                        └──────────────┘              │
                                                      ▼
┌─────────────────┐     ┌──────────────┐     ┌──────────────┐
│ Business Logic  │────▶│ Test Cases   │◀────│  Z3 Solver   │
│   Validator     │     │   (JSON)     │     │ (Constraint) │
└─────────────────┘     └──────────────┘     └──────────────┘
```

### Key Modules

1. **Parser Layer** (`src/dsl_test_generator/parsers/`)
   - `dsl_parser.py`: Main DSL parser
   - `yaml_parser.py`: YAML utilities

2. **Type System** (`src/dsl_test_generator/types/`)
   - `models.py`: Core data models (Entity, Attribute, Constraint, Rule)
   - `validators.py`: Type validation logic

3. **Core Engine** (`src/dsl_test_generator/core/`)
   - `engine.py`: Main orchestrator
   - `enhanced_engine.py`: Advanced features
   - `z3_solver.py`: Z3 SMT solver interface
   - `constraint_translator.py`: DSL to Z3 translation

4. **Test Generators** (`src/dsl_test_generator/generators/`)
   - `test_generator.py`: Base generator
   - `smart_test_generator.py`: Intelligent test generation
   - `collection_generator.py`: Array/Set testing
   - `domain_aware_test_generator.py`: Domain-specific logic

5. **Validators** (`src/dsl_test_generator/validators/`)
   - `business_logic_validator.py`: Ensures realistic test data

6. **Configuration** (`src/dsl_test_generator/config.py`)
   - Centralized configuration system
   - Eliminates hardcoded values

## 📁 Project Structure

```
dsl-test-generator/
├── dsl2test.py              # CLI entry point
├── SETUP_GUIDE.md           # Installation guide
├── README.md                # Project introduction
├── CHANGELOG.md             # Version history
├── pyproject.toml           # Package configuration
├── .gitignore              # Git ignore rules
│
├── src/dsl_test_generator/  # Main package
│   ├── __init__.py
│   ├── config.py           # Configuration system
│   ├── core/               # Core functionality
│   ├── parsers/            # DSL parsing
│   ├── generators/         # Test generation
│   ├── types/              # Type system
│   └── validators/         # Validation logic
│
├── demo/                   # Demonstrations
│   ├── examples/           # Example DSL files
│   ├── outputs/            # Generated outputs
│   └── analysis/           # Analysis documents
│
├── examples/               # Additional examples
├── docs/                   # Documentation
├── tests/                  # Test suite
├── output/                 # Generated test outputs
└── debug/                  # Debug utilities
```

## 🔄 Workflow

### 1. DSL Definition

Users write YAML files defining their system:

```yaml
domain: E-commerce System

entities:
  - name: Order
    attributes:
      - name: total
        type: real
        min: 0.01
        max: 999999.99

constraints:
  - order_total > 0

rules:
  - name: Free Shipping
    condition: order_total >= 100
    implies: shipping_cost == 0
```

### 2. Parsing

The DSL parser converts YAML to internal model representation:
- Validates syntax
- Checks references
- Builds type information

### 3. Test Generation

The engine generates multiple test types:
- **Boundary Tests**: Min/max values
- **Equivalence Tests**: Representative values
- **Negative Tests**: Invalid inputs
- **Rule Coverage**: Activate/deactivate rules
- **Combination Tests**: Multi-attribute scenarios

### 4. Constraint Solving

Z3 solver ensures all generated tests:
- Satisfy constraints
- Are mathematically valid
- Cover edge cases

### 5. Business Logic Validation

Optional validation ensures:
- Cross-entity constraints are met
- Test data is realistic
- Business rules are followed

### 6. Output

Tests are output as JSON with full metadata:
```json
{
  "name": "boundary_age_min",
  "type": "boundary",
  "expected": "pass",
  "values": {
    "age": 18,
    "member_level": 2
  }
}
```

## 🌟 Key Features

### 1. Type System
- **Scalar Types**: integer, real, boolean, string
- **Collection Types**: array[T], set[T]
- **Constraints**: min/max, enum, pattern

### 2. Test Strategies
- **Boundary Value Analysis**: Test limits
- **Equivalence Partitioning**: Test categories
- **Negative Testing**: Test failures
- **Combinatorial Testing**: Test interactions

### 3. Configuration System
- Adjustable precision
- Customizable limits
- Solver settings
- Validation options

### 4. Language Support
- **Keywords**: English only
- **Values**: Any language (including Chinese)
- **Comments**: Any language

## 💡 Use Cases

1. **API Testing**: Generate test cases for REST APIs
2. **Form Validation**: Test input validation logic
3. **Business Rules**: Verify complex business logic
4. **Database Constraints**: Test data integrity rules
5. **Configuration Testing**: Validate system configurations

## 🔧 Extensibility

The modular design allows easy extension:

1. **New Test Types**: Add generators to `generators/`
2. **New Constraints**: Extend `constraint_translator.py`
3. **New Validators**: Add to `validators/`
4. **Custom Output**: Modify output formatting

## 📊 Performance

- **Small Models** (<10 entities): <1 second
- **Medium Models** (10-50 entities): 1-5 seconds
- **Large Models** (50+ entities): 5-30 seconds

Performance depends on:
- Constraint complexity
- Number of rules
- Z3 solver configuration

## 🚀 Getting Started

1. **Install**: Follow [SETUP_GUIDE.md](SETUP_GUIDE.md)
2. **Learn DSL**: Read [docs/DSL_REFERENCE.md](docs/DSL_REFERENCE.md)
3. **Try Examples**: Run files in `demo/examples/`
4. **Write DSL**: Create your own specifications
5. **Generate Tests**: Use `dsl2test.py`

## 🤝 Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines on:
- Code style
- Testing requirements
- Pull request process
- Issue reporting

## 📝 License

MIT License - see [LICENSE](LICENSE) for details.

## 🙏 Acknowledgments

- **Z3 Theorem Prover**: Microsoft Research
- **Python Community**: Modern packaging tools
- **Contributors**: All who have helped improve this project