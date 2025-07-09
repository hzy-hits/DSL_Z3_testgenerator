# DSL Test Generator

A sophisticated test case generator that transforms Domain-Specific Language (DSL) specifications into comprehensive test suites using the Z3 SMT solver. Automatically generates boundary tests, equivalence tests, negative tests, and achieves 100% test coverage without manual supplementation.

## 🚀 Features

- **100% Automatic Test Coverage**: No manual test case supplementation needed
- **Enhanced Type System**: Support for arrays and sets in addition to scalar types
- **Z3 SMT Solver Integration**: Automatic constraint solving and test generation
- **Comprehensive Test Coverage**: Boundary, equivalence, negative, and combinatorial tests
- **Collection Testing**: Specialized tests for arrays and sets
- **Business Logic Validation**: Ensures generated test data follows real-world constraints
- **Flexible Configuration**: Customize engine behavior without modifying code
- **Modern Python Packaging**: Uses `pyproject.toml` and follows best practices
- **CLI Tool**: Easy-to-use command-line interface (`dsl2test.py`)

## 📦 Quick Start

For detailed installation instructions, see the [Setup Guide](SETUP_GUIDE.md).

### Using uv (recommended)

```bash
# Install uv
curl -LsSf https://astral.sh/uv/install.sh | sh

# Clone and run
git clone https://github.com/your-repo/dsl-test-generator.git
cd dsl-test-generator
uv run ./dsl2test.py demo/examples/hotel_booking_system.yaml
```

### Using pip

```bash
# Create virtual environment
python -m venv venv
source venv/bin/activate  # On Windows: venv\Scripts\activate

# Install package
pip install -e .

# Run tool
python dsl2test.py demo/examples/hotel_booking_system.yaml
```

## 🎯 Quick Start

### Using the CLI Tool (Recommended)

The easiest way to generate test cases is using the `dsl2test.py` CLI tool:

```bash
# Generate test cases to stdout
./dsl2test.py demo/hotel_booking_system.yaml

# Save to a file
./dsl2test.py demo/hotel_booking_system.yaml -o tests.json

# Use compact format
./dsl2test.py demo/insurance_claim_system.yaml --format compact

# With verbose output
./dsl2test.py my_dsl.yaml -v

# Using uv (handles dependencies automatically)
uv run ./dsl2test.py my_dsl.yaml -o tests.json
```

### 1. Define your DSL

Create a YAML file describing your system:

```yaml
domain: User Authentication

entities:
  - name: User
    attributes:
      - name: age
        type: integer
        min: 0
        max: 150
      - name: roles
        type: set[string]
        min_size: 1
        max_size: 5
      - name: login_history
        type: array[integer]  # Unix timestamps
        max_size: 100

constraints:
  - user_age >= 18
  - size(user_roles) >= 1

rules:
  - name: Admin requires strong auth
    condition: "admin" in user_roles
    implies: size(user_login_history) >= 10
```

### 2. Generate test cases

```bash
# Using the CLI
dsl-generate examples/auth_system.yaml -o test_cases.json

# Using Python
from dsl_test_generator import DSLParser, DSLEngine

parser = DSLParser()
model = parser.parse_file("examples/auth_system.yaml")

engine = DSLEngine()
test_cases = engine.generate_tests(model)
```

## 📚 DSL Syntax

### Supported Types

- **Scalar Types**: `integer`, `real`, `boolean`, `string`
- **Collection Types**: `array[T]`, `set[T]` where T is a scalar type

### Entities and Attributes

```yaml
entities:
  - name: EntityName
    attributes:
      - name: scalar_attr
        type: integer
        min: 0
        max: 100
      - name: array_attr
        type: array[real]
        min_size: 0
        max_size: 50
      - name: set_attr
        type: set[string]
        min_size: 1
```

### Constraints

```yaml
constraints:
  # Scalar constraints
  - variable >= value
  - variable1 + variable2 <= 100
  
  # Collection constraints
  - size(array_var) >= 1
  - element in set_var
  - set1 subset set2
```

### Rules

```yaml
rules:
  - name: Business Rule
    condition: triggering_condition
    implies: resulting_constraint
```

### Test Requirements

```yaml
test_requirements:
  - name: Boundary Tests
    type: boundary
    focus: [var1, var2]
    
  - name: Collection Tests
    type: collection
    collection_tests: [empty, single, multiple, boundary]
```

## 🧪 Test Types

1. **Boundary Tests**: Test minimum and maximum values
2. **Equivalence Tests**: Test representative values from equivalence classes
3. **Negative Tests**: Test constraint violations
4. **Collection Tests**: Test empty, single, multiple elements, and boundaries
5. **Combinatorial Tests**: Test combinations of values
6. **Rule Coverage**: Test rule activation and deactivation

## ⚠️ Known Issues and Best Practices

### Test Generation with Focus Parameter

When using `test_requirements` with the `focus` parameter, be aware that:

1. **Issue**: The focus parameter uses simple attribute names (e.g., `age`), but may not generate expected tests if attributes are in different entities.

2. **Best Practices**:
   - **Option 1**: Don't use the `focus` parameter - let the system test all attributes
   - **Option 2**: Use a single entity design to avoid cross-entity references
   - **Option 3**: Don't specify `test_requirements` at all - use the default test generation strategy

### Example - Recommended Approach

```yaml
# ✅ GOOD: Single entity design
domain: Hotel Booking System

entities:
  - name: Booking
    attributes:
      - name: customer_age
        type: integer
        min: 18
        max: 100
      - name: member_level
        type: integer
        min: 1
        max: 3
        enum_values: [1, 2, 3]  # Adding enum values helps generate more tests

constraints:
  - booking_customer_age >= 18
  - booking_member_level >= 1 and booking_member_level <= 3

# Don't specify test_requirements - use default strategy
# This will generate boundary tests, rule coverage tests, etc. automatically
```

### Example - What to Avoid

```yaml
# ❌ AVOID: Multiple entities with focus on simple names
domain: Hotel System

entities:
  - name: Customer
    attributes:
      - name: age
        type: integer
  - name: Booking
    attributes:
      - name: days
        type: integer

test_requirements:
  - name: Age tests
    type: boundary
    focus: [age]  # This might not work as expected
```

## 📁 Project Structure

```
dsl-test-generator/
├── src/
│   └── dsl_test_generator/
│       ├── __init__.py
│       ├── cli.py              # Command-line interface
│       ├── core/               # Core engine and solver
│       │   ├── engine.py
│       │   ├── z3_solver.py
│       │   └── constraint_translator.py
│       ├── types/              # Type system and models
│       │   ├── models.py
│       │   └── validators.py
│       ├── parsers/            # DSL parsers
│       │   └── dsl_parser.py
│       └── generators/         # Test generators
│           ├── test_generator.py
│           └── collection_generator.py
├── examples/                   # Example DSL files
├── tests/                      # Test suite
├── docs/                       # Documentation
└── pyproject.toml             # Project configuration
```

## 🔧 Development

### Setting up development environment

```bash
# Clone the repository
git clone <repo-url>
cd dsl-test-generator

# Create virtual environment
python -m venv venv
source venv/bin/activate

# Install in development mode with dev dependencies
pip install -e ".[dev]"

# Run tests
pytest

# Format code
black src tests
ruff check src tests

# Type checking
mypy src
```

### Running tests

```bash
# Run all tests
pytest

# Run with coverage
pytest --cov

# Run specific test file
pytest tests/test_parser.py
```

## 📋 Examples

### E-commerce Shopping Cart

See `examples/shopping_cart.yaml` for a complete example with:
- Array of product IDs
- Set of discount codes
- Complex business rules

### Permission System

See `examples/permission_system.yaml` for RBAC with:
- Set-based role management
- Permission inheritance
- State-dependent constraints

### Running Examples

```bash
# Generate tests for shopping cart
dsl-generate examples/shopping_cart.yaml -o cart_tests.json

# Generate tests for permission system
dsl-generate examples/permission_system.yaml -f yaml -o perm_tests.yaml
```

## 🤝 Contributing

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Add tests
5. Submit a pull request

## 📄 License

MIT License - see LICENSE file for details

## ⚙️ Configuration

The DSL Test Generator now supports flexible configuration to customize its behavior:

```python
from dsl_test_generator import DSLEngine, DSLEngineConfig

# Create custom configuration
config = DSLEngineConfig()
config.test_generation.validate_business_logic = True
config.test_generation.decimal_precision = 2
config.solver.timeout = 10000  # 10 seconds

# Use with engine
engine = DSLEngine(config)
```

See `docs/API_REFERENCE.md` for detailed configuration options.

## 📚 Documentation

- `README.md` - This file
- `USER_GUIDE.md` - Comprehensive user guide for the CLI tool
- `DSL_GUIDE.md` - DSL writing guide with Z3 solver considerations
- `docs/DSL_REFERENCE.md` - Complete DSL syntax reference
- `docs/API_REFERENCE.md` - Python API reference and examples
- `docs/Chinese_Support.md` - Chinese language support guide
- `MIGRATION_GUIDE.md` - Migration from old structure

## 🌐 Language Support

The DSL Test Generator supports Chinese values while requiring English keywords:

```yaml
# English keywords, Chinese values
domain: 学生管理系统

entities:
  - name: Student
    attributes:
      - name: status
        type: string
        enum: ["在读", "休学", "毕业"]
        description: 学生状态

rules:
  - name: 在读学生限制
    condition: student_status == "在读"
    implies: student_course_count >= 1
```

See `docs/Chinese_Support.md` for detailed guidelines.

## 🙏 Acknowledgments

- Z3 Theorem Prover by Microsoft Research
- The Python packaging community for modern tools