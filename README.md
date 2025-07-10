# DSL Test Generator v3.0

🚀 **企业级 DSL 驱动的自动化测试生成工具**

[![Version](https://img.shields.io/badge/version-3.0-blue.svg)](https://github.com/yourusername/dsl-test-generator)
[![Python](https://img.shields.io/badge/python-3.8+-green.svg)](https://www.python.org/)
[![License](https://img.shields.io/badge/license-MIT-purple.svg)](LICENSE)

> **重要更新**: 现已发布 V3.0 版本！
> - **V3.0** (推荐): 高级特性版本，支持模板测试、时间约束、性能优化
> - **V2.0**: 统一架构版本，100% 约束满足保证
> - **V1.0**: 原始版本，基础 Z3 求解功能

## 🚀 版本选择指南

### 使用 V3.0 如果你需要:
- **测试模板系统** - 内置安全、性能、边界测试模板
- **高级约束支持** - 时间约束、条件约束、自定义函数
- **性能优化** - 缓存机制、批量生成
- **配置驱动** - 灵活的测试生成策略
- **智能值生成** - 业务感知的真实数据

### 使用 V2.0 如果你需要:
- **100% 正确性保证** - 所有测试满足约束
- **统一架构** - 整合 Z3 求解和代码生成
- **Optional 字段支持** - 灵活的字段定义
- **智能去重** - 高效的测试集

### 使用 V1.0 如果你需要:
- **向后兼容** - 现有集成
- **基础功能** - 简单的约束求解

## 📦 快速开始

### V3.0 (推荐)
```bash
# 基础用法
python main.py examples/intermediate/user_account_system.yaml

# 使用配置文件
python main.py examples/advanced/advanced_ecommerce.yaml -c configs/test_config_v3.json

# 启用性能模式
python main.py examples/advanced/advanced_ecommerce.yaml --performance
```

### V2.0
```bash
python src/generators/v2_generator.py examples/intermediate/shopping_cart.yaml
```

### V1.0
```bash
python src/generators/v1_generator.py examples/basic/simple_arrays.yaml
```

## 🎯 功能对比

| 特性 | V1.0 | V2.0 | V3.0 |
|-----|------|------|------|
| Z3 约束求解 | ✅ | ✅ | ✅ |
| 可执行代码生成 | ❌ | ✅ | ✅ |
| Optional 字段 | ❌ | ✅ | ✅ |
| 测试模板 | ❌ | ❌ | ✅ |
| 时间约束 | ❌ | ❌ | ✅ |
| 性能优化 | ❌ | ❌ | ✅ |
| 配置系统 | ❌ | ❌ | ✅ |
| 平均生成时间 | 0.074s | 0.073s | 0.063s |
| 成功率 | 75% | 50% | 100% |

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