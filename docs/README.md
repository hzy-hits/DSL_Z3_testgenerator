# DSL Test Generator Documentation

Welcome to the DSL Test Generator documentation. This directory contains detailed guides and references for using and understanding the system.

## 📚 Documentation Index

### Getting Started
- [**Setup Guide**](../SETUP_GUIDE.md) - Complete installation and setup instructions for new environments
- [**User Guide**](../USER_GUIDE.md) - Comprehensive guide for using the CLI tool
- [**Project Overview**](../PROJECT_OVERVIEW.md) - Architecture and design overview

### Reference Documentation
- [**DSL Reference**](DSL_REFERENCE.md) - Complete DSL syntax and features
- [**API Reference**](API_REFERENCE.md) - Python API documentation and examples
- [**Configuration Guide**](../USER_GUIDE.md#configuration) - How to configure the engine

### Guides
- [**DSL Writing Guide**](../DSL_GUIDE.md) - Best practices for writing DSL files
- [**Troubleshooting**](TROUBLESHOOTING.md) - Common issues and solutions
- [**Migration Guide**](../MIGRATION_GUIDE.md) - Upgrading between versions

### Language Support
- [**Chinese Support**](Chinese_Support.md) - Using Chinese values in DSL
- [**中文需求转DSL指南**](中文需求转DSL指南.md) - Converting Chinese requirements to DSL

### Development
- [**Changelog**](../CHANGELOG.md) - Version history and changes
- [**Contributing**](../CONTRIBUTING.md) - Guidelines for contributors

## 🚀 Quick Links

### For Users
1. Start with the [Setup Guide](../SETUP_GUIDE.md)
2. Learn DSL syntax in [DSL Reference](DSL_REFERENCE.md)
3. See examples in `demo/examples/` and `examples/`

### For Developers
1. Read the [API Reference](API_REFERENCE.md)
2. Understand the [Project Overview](../PROJECT_OVERVIEW.md)
3. Set up development environment per [Setup Guide](../SETUP_GUIDE.md#development-setup)

## 📖 Documentation Structure

```
docs/
├── README.md              # This file
├── DSL_REFERENCE.md       # DSL syntax reference
├── API_REFERENCE.md       # Python API reference
├── TROUBLESHOOTING.md     # Problem solving guide
├── Chinese_Support.md     # Chinese language guide
└── 中文需求转DSL指南.md     # Chinese requirements guide

Project Root/
├── SETUP_GUIDE.md         # Installation guide
├── USER_GUIDE.md          # User manual
├── DSL_GUIDE.md          # DSL writing guide
├── PROJECT_OVERVIEW.md    # Architecture overview
├── MIGRATION_GUIDE.md     # Version migration
├── CHANGELOG.md          # Version history
└── README.md             # Project introduction
```

## 💡 Common Tasks

### Generate Test Cases
```bash
./dsl2test.py my_dsl.yaml -o tests.json
```

### Use Custom Configuration
```python
from dsl_test_generator import DSLEngine, DSLEngineConfig

config = DSLEngineConfig()
config.test_generation.validate_business_logic = True
engine = DSLEngine(config)
```

### Write Your First DSL
See [DSL Reference](DSL_REFERENCE.md) and examples in `demo/examples/`

## 🆘 Getting Help

1. Check [Troubleshooting](TROUBLESHOOTING.md) for common issues
2. Review examples in `demo/examples/` and `examples/`
3. Read the [API Reference](API_REFERENCE.md) for programming details
4. Report issues on GitHub

---

*Last updated: Version 0.3.0*