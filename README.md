# DSL Test Generator v9.0 - Fully Generic Edition

A domain-agnostic, intelligent test generator that automatically creates comprehensive test cases from YAML specifications. Built with semantic intelligence and generic constraint handling, it works seamlessly across any business domain without requiring domain-specific code.

[English](README.md) | [中文](README_zh.md)

## 🚀 Revolutionary Features

### Complete Domain Independence
- **Zero Domain-Specific Code**: Works with any business domain out of the box
- **Semantic Intelligence**: Automatically understands attribute meanings from naming patterns
- **Universal Constraint Handling**: Intelligently processes any constraint expression
- **Cross-Entity Business Rules**: Handles complex rules spanning multiple entities

### Intelligent Test Generation
- **Smart Value Generation**: Context-aware test data based on semantic understanding
- **Automatic Constraint Satisfaction**: Ensures all generated data respects defined constraints
- **Comprehensive Coverage**: Functional, boundary, constraint, business rule, and scenario tests
- **State Machine Support**: Full workflow and state transition testing

## 📊 Proven Results

- **47 tests** generated for cleaning dispatch system
- **37 tests** generated for banking system
- **100% constraint coverage** achieved automatically
- **Zero code changes** needed between different domains

## 🎯 Quick Start

### Installation

Using uv (recommended):
```bash
uv venv
source .venv/bin/activate  # Linux/macOS
uv pip install -e .
```

Or using pip:
```bash
pip install pyyaml z3-solver colorama tabulate
```

### Generate Tests for Any Domain

```bash
# Generate tests for cleaning dispatch system
python generate_extended.py examples/cleaning_dispatch.yaml -o dispatch_tests.json

# Generate tests for banking system
python generate_extended.py examples/bank_account.yaml -o banking_tests.json

# Generate tests for e-commerce system
python generate_extended.py examples/intermediate/shopping_cart.yaml -o shopping_tests.json

# Enable verbose output
python generate_extended.py your_domain.yaml -o your_tests.json -v
```

## 📝 DSL Format

Define your domain in simple YAML:

```yaml
domain: Your Business Domain

entities:
  - name: YourEntity
    attributes:
      - name: some_id
        type: integer
        min: 1
        max: 999999
        
      - name: some_status
        type: integer
        enum_values: [1, 2, 3, 4]
        
      - name: some_amount
        type: real
        min: 0.0
        max: 10000.0

constraints:
  - expression: some_amount >= 0
    description: Amount must be non-negative
    
rules:
  - name: Business Rule Name
    condition: some_status == 1
    action: some_amount > 100
    description: When status is 1, amount must exceed 100

state_machines:
  - name: EntityWorkflow
    entity: YourEntity
    state_attribute: some_status
    states:
      - name: Initial
        value: 1
    transitions:
      - name: Progress
        from: Initial
        to: Next
        condition: some_amount > 0
```

## 🧠 How It Works

### 1. Semantic Analysis
The generator analyzes attribute names to understand their meaning:
- `*_distance` → Distance values (respects geographic constraints)
- `*_time`, `*_hours` → Time-related values
- `*_count`, `*_number` → Counting values
- `*_status`, `*_type` → Enumeration values
- `*_amount`, `*_price` → Monetary values

### 2. Intelligent Constraint Processing
- Automatically extracts constraints from DSL
- Generates tests that satisfy constraints
- Creates boundary value tests
- Produces constraint violation tests

### 3. Business Rule Understanding
- Parses complex business rules
- Handles cross-entity relationships
- Generates rule trigger/non-trigger tests

## 📁 Project Structure

```
dsl-test-generator/
├── generate_extended.py          # Main test generator
├── examples/                     # Example DSL files
│   ├── cleaning_dispatch.yaml    # Cleaning service example
│   ├── bank_account.yaml         # Banking system example
│   └── intermediate/             # More examples
├── src/
│   └── generators/
│       └── v8/
│           ├── generic_constraint_test_strategy.py  # Generic strategy
│           └── semantic_value_generator.py          # Semantic generator
└── docs/                         # Documentation
```

## 🔧 Advanced Usage

### Analyze Generated Tests

```python
# Create analysis script
python analyze_tests.py generated_tests.json
```

### Batch Processing

```bash
# Process multiple DSL files
for file in examples/*.yaml; do
    python generate_extended.py "$file" -o "outputs/$(basename $file .yaml).json"
done
```

## 📈 Test Coverage Analysis

The generator provides comprehensive coverage metrics:
- **State Coverage**: All defined states tested
- **Transition Coverage**: All state transitions verified
- **Rule Coverage**: All business rules validated
- **Constraint Coverage**: All constraints tested

## 🤝 Contributing

1. Fork the repository
2. Create your feature branch (`git checkout -b feature/AmazingFeature`)
3. Commit your changes (`git commit -m 'Add AmazingFeature'`)
4. Push to the branch (`git push origin feature/AmazingFeature`)
5. Open a Pull Request

## 📄 License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## 🐛 Issue Reporting

If you encounter any issues:
1. Check [TROUBLESHOOTING.md](docs/TROUBLESHOOTING.md)
2. Submit an issue on [GitHub Issues](https://github.com/yourusername/dsl-test-generator/issues)
3. Include your DSL file and error message

## 🎉 Success Stories

- **Cleaning Dispatch System**: 47 comprehensive tests covering all business rules
- **Banking System**: 37 tests with full constraint coverage
- **E-commerce Platform**: Complete shopping cart workflow testing
- **Permission System**: Role-based access control validation

---

**DSL Test Generator v9.0** - Write once, test anywhere. No domain knowledge required.