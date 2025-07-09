# DSL Test Generator - Project Overview

## 🎯 Purpose

The DSL Test Generator is a sophisticated tool that automatically generates comprehensive test cases from Domain-Specific Language (DSL) specifications. It uses the Z3 SMT solver to ensure mathematical correctness and generates tests that achieve high coverage without manual intervention.

## 📌 Version Information

This repository contains two versions:

### V1.0 (Original)
- **Location**: Root directory (`src/dsl_test_generator/`)
- **Features**: Full feature set, multiple generators, stable API
- **Best for**: Existing integrations, backward compatibility
- **Architecture**: Monolithic with some coupled components

### V2.0 (Refactored)
- **Location**: `v2.0/` directory
- **Features**: 100% correctness guarantee, minimal test sets, clean architecture
- **Best for**: New projects, correctness-critical applications
- **Architecture**: Clean layered design with separation of concerns

## 🏗️ Architecture

### V1.0 Architecture
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

### V2.0 Architecture
```
┌────────────────────────────────────────┐
│            CLI Interface               │
├────────────────────────────────────────┤
│            DSL Parser                  │  ← Parse & validate
├────────────────────────────────────────┤
│         Test Strategy Layer            │  ← Plan what to test
├────────────────────────────────────────┤
│      Constraint Solver (Z3)            │  ← Generate correct data
├────────────────────────────────────────┤
│         Output Formatter               │  ← Multiple formats
└────────────────────────────────────────┘
```

## 📁 Project Structure

```
dsl-test-generator/
├── v2.0/                    # Version 2.0 (Refactored)
│   ├── src/
│   │   ├── core/           # Core models and generator
│   │   ├── layers/         # Parser, solver, expression parser
│   │   ├── strategies/     # Test planning strategies
│   │   └── utils/          # Output formatting
│   ├── examples/           # V2.0 example DSL files
│   ├── output/            # Generated test outputs
│   └── dsl2test.py        # V2.0 CLI tool
│
├── src/dsl_test_generator/  # Version 1.0 (Original)
│   ├── parsers/            # DSL parsing
│   ├── types/              # Type system
│   ├── core/               # Core engine and solver
│   ├── generators/         # Test generators
│   ├── validators/         # Business logic validation
│   └── config.py           # Configuration
│
├── demo/                   # Demo files and examples
│   └── examples/          # Example DSL specifications
├── examples/              # V1.0 examples
├── docs/                  # Documentation
├── tests/                 # Test suite
├── archive/               # Archived old outputs
└── redesign/              # V2.0 design documents
```

## 🚀 Features

### Common Features (Both Versions)
- YAML-based DSL for test specification
- Z3 SMT solver integration
- Support for complex constraints and rules
- Multiple test types (boundary, equivalence, negative)
- Collection types (arrays, sets)

### V1.0 Specific Features
- Multiple test generators (smart, enhanced, domain-aware)
- Business logic validator with domain knowledge
- Extensive configuration options
- Python API for integration

### V2.0 Specific Features
- 100% correctness guarantee
- Minimal test set generation (50-70% reduction)
- Clear test objectives and coverage information
- Multiple output formats (JSON, JUnit, CSV, Markdown, Python)
- Clean architecture without business logic hardcoding

## 📊 Performance Comparison

| Metric | V1.0 | V2.0 |
|--------|------|------|
| Test Count | 50-115 | 20-60 |
| Correctness | ~60% | 100% |
| Generation Time | 10-30s | 2-5s |
| Memory Usage | High | Low |

## 🛠️ Technology Stack

- **Language**: Python 3.8+
- **Constraint Solver**: Z3 SMT Solver
- **Parser**: PyYAML
- **Testing**: pytest
- **Packaging**: pyproject.toml (V1.0), standalone (V2.0)

## 📝 DSL Example

```yaml
domain: Hotel Booking System

entities:
  - name: Customer
    attributes:
      - name: age
        type: integer
        min: 18
        max: 120

  - name: Booking
    attributes:
      - name: discount
        type: integer
        min: 0
        max: 50

constraints:
  - customer_age >= 18
  - booking_discount <= 50

rules:
  - name: Senior Discount
    if: customer_age >= 65
    then: booking_discount >= 10
```

## 🔄 Migration Guide

### From V1.0 to V2.0
1. DSL files remain compatible
2. CLI interface is similar but simplified
3. Output format can be converted between versions
4. API integration requires rewriting (V2.0 has no Python API yet)

### Key Differences
- V2.0 doesn't support custom test requirements
- V2.0 generates fewer but more meaningful tests
- V2.0 guarantees correctness for all tests

## 🤝 Contributing

1. Choose the version to contribute to
2. Follow the architecture patterns of that version
3. Add tests for new features
4. Update documentation
5. Submit pull request

## 📄 License

MIT License - see LICENSE file for details