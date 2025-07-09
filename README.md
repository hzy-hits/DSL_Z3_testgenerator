# DSL Test Generator

A sophisticated test case generator that transforms Domain-Specific Language (DSL) specifications into comprehensive test suites using the Z3 SMT solver.

> **Important**: This repository contains two versions:
> - **V1.0** (current directory): Original version with full features but some design limitations
> - **[V2.0](v2.0/)**: Refactored version with 100% correctness guarantee and better performance

## 🚀 Which Version to Use?

### Use V2.0 if you need:
- **100% correctness guarantee** - All generated tests satisfy constraints
- **Minimal test sets** - Typically 50-70% fewer tests
- **Clear test objectives** - Each test has explicit purpose
- **Clean architecture** - No business logic hardcoding

### Use V1.0 if you need:
- **Backward compatibility** - Existing integrations
- **More test generation strategies** - Multiple generators available
- **Stable API** - Well-tested in production

## 📦 Quick Start

### For V2.0 (Recommended)
```bash
cd v2.0
python dsl2test.py --input examples/simple_test.yaml --output tests.json
```

### For V1.0
```bash
# Using uv (recommended)
uv run ./dsl2test.py demo/examples/hotel_booking_system.yaml

# Using pip
pip install -e .
python dsl2test.py demo/examples/hotel_booking_system.yaml
```

## 🎯 Features Comparison

| Feature | V1.0 | V2.0 |
|---------|------|------|
| Correctness | ~60% | 100% |
| Test Count | 50-100+ | 20-60 |
| Architecture | Monolithic | Layered |
| Business Logic | Some hardcoding | Pure engine |
| Output Formats | JSON | JSON, JUnit, CSV, Markdown, Python |

## 📚 DSL Syntax

Both versions support the same DSL syntax:

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

### Supported Types
- **Scalar Types**: `integer`, `real`, `boolean`, `string`
- **Collection Types**: `array[T]`, `set[T]` where T is a scalar type

## 📁 Project Structure

```
dsl-test-generator/
├── v2.0/                      # Version 2.0 (refactored)
│   ├── src/                   # Clean layered architecture
│   ├── examples/              # Example DSL files
│   └── dsl2test.py           # CLI tool
├── src/                       # Version 1.0 (original)
│   └── dsl_test_generator/
├── demo/                      # Demo files and examples
├── examples/                  # V1.0 examples
├── docs/                      # Documentation
└── README.md                  # This file
```

## 🔧 Development

### V2.0 Development
```bash
cd v2.0
# No installation needed, uses system Python with Z3
python dsl2test.py --help
```

### V1.0 Development
```bash
# Create virtual environment
python -m venv venv
source venv/bin/activate

# Install in development mode
pip install -e ".[dev]"

# Run tests
pytest
```

## 📋 Examples

Example DSL files are provided in:
- **V2.0**: `v2.0/examples/`
- **V1.0**: `examples/` and `demo/examples/`

### Running Examples

```bash
# V2.0
cd v2.0
python dsl2test.py --input examples/simple_test.yaml --output output.json

# V1.0
python dsl2test.py examples/shopping_cart.yaml -o cart_tests.json
```

## 📚 Documentation

### General Documentation
- `README.md` - This file
- `DSL_GUIDE.md` - DSL writing guide
- `docs/DSL_REFERENCE.md` - Complete DSL syntax reference

### V1.0 Specific
- `USER_GUIDE.md` - V1.0 CLI user guide
- `docs/API_REFERENCE.md` - V1.0 Python API reference
- `SETUP_GUIDE.md` - V1.0 installation guide
- `MIGRATION_GUIDE.md` - Migration from old structure

### V2.0 Specific
- `v2.0/README.md` - V2.0 overview
- `v2.0/docs/v2_improvements.md` - Detailed improvements
- `redesign/` - Architecture design documents

## 🌐 Language Support

Both versions support Chinese values with English keywords:

```yaml
domain: 学生管理系统

entities:
  - name: Student
    attributes:
      - name: status
        type: string
        enum: ["在读", "休学", "毕业"]

rules:
  - name: 在读学生限制
    condition: student_status == "在读"
    implies: student_course_count >= 1
```

## 🤝 Contributing

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Add tests
5. Submit a pull request

## 📄 License

MIT License - see LICENSE file for details

## 🙏 Acknowledgments

- Z3 Theorem Prover by Microsoft Research
- The Python packaging community for modern tools