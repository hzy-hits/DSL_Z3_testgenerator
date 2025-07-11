# V2.0 项目结构 (重构后)

## 核心架构

项目采用模块化设计，所有源代码位于`src/`目录下，实现代码复用和清晰的组织结构。

## 目录结构

```
v2.0/
├── main.py                        # 统一入口程序
├── src/                          # 源代码目录
│   ├── cli/                      # 命令行接口模块
│   │   ├── __init__.py
│   │   ├── generate.py          # 测试生成CLI
│   │   └── evaluate.py          # 测试质量评估CLI
│   ├── core/                     # 核心引擎
│   │   ├── __init__.py
│   │   ├── combination_engine.py # 组合测试引擎
│   │   └── concrete_value_generator.py # 具体值生成器
│   ├── generators/              # 测试生成器
│   │   ├── __init__.py
│   │   ├── v8/                 # V8核心实现
│   │   │   ├── __init__.py
│   │   │   ├── core.py        # 核心生成逻辑
│   │   │   ├── models.py      # 数据模型
│   │   │   ├── parser.py      # YAML解析器
│   │   │   ├── value_generator.py # 值生成器
│   │   │   ├── constraint_handler.py # 约束处理
│   │   │   └── test_strategies.py # 测试策略
│   │   ├── v8_improved/       # V8优化版本 ⭐
│   │   │   ├── __init__.py
│   │   │   ├── improved_test_generator.py # 改进的主生成器
│   │   │   ├── type_aware_value_generator.py # 类型感知生成器
│   │   │   ├── negative_test_strategy.py # 改进的负面测试
│   │   │   ├── boundary_test_strategy.py # 精确边界值测试
│   │   │   ├── enhanced_constraint_solver.py # 增强的约束求解
│   │   │   └── constraint_validator.py # 约束验证器
│   │   └── v8_modular/        # V8模块化版本
│   ├── layers/                # 分层架构组件
│   │   ├── __init__.py
│   │   ├── dsl_parser.py     # DSL解析层
│   │   ├── expression_parser.py # 表达式解析
│   │   └── constraint_solver.py # 约束求解层
│   ├── strategies/           # 测试策略
│   │   ├── __init__.py
│   │   └── test_planner.py  # 测试规划器
│   └── utils/               # 工具模块
│       ├── __init__.py
│       ├── logger.py        # 统一日志配置
│       └── output_formatter.py # 输出格式化
├── examples/                # DSL示例文件
│   ├── basic/              # 基础示例
│   │   └── simple_arrays.yaml
│   ├── intermediate/       # 中级示例
│   │   ├── shopping_cart.yaml
│   │   └── permission_system.yaml
│   └── advanced/          # 高级示例
│       ├── advanced_ecommerce.yaml
│       ├── order_processing_system.yaml
│       ├── student_system_mixed.yaml
│       └── user_account_system.yaml
├── docs/                  # 文档
│   ├── API_REFERENCE.md
│   ├── DSL_REFERENCE.md
│   ├── TROUBLESHOOTING.md
│   ├── Chinese_Support.md
│   └── 中文需求转DSL指南.md
├── outputs/              # 测试输出目录
├── tests/               # 单元测试
├── configs/             # 配置文件
├── pyproject.toml      # Python项目配置
├── requirements.txt    # 依赖列表
├── .gitignore         # Git忽略文件
├── LICENSE           # MIT许可证
├── README.md         # 项目说明
└── *.md             # 各种文档文件
```

## 使用方式

### 1. 主入口程序
```bash
# 查看帮助
python main.py --help

# 生成测试（新命令格式）
python main.py generate examples/intermediate/shopping_cart.yaml

# 旧版兼容模式
python main.py examples/intermediate/shopping_cart.yaml

# 评估测试质量
python main.py evaluate outputs/cart_tests.json
```

### 2. 命令行工具
主程序提供两个子命令：
- `generate`: 生成测试用例
- `evaluate`: 评估测试质量

### 3. 批量处理
```bash
python main.py generate --batch examples/
```

### 4. 高级选项
```bash
# 生成详细报告
python main.py generate examples/advanced/advanced_ecommerce.yaml --report

# 指定输出格式
python main.py generate examples/intermediate/shopping_cart.yaml --format markdown

# 验证生成的测试
python main.py generate examples/intermediate/shopping_cart.yaml --validate
```

## 核心模块说明

### CLI模块 (`src/cli/`)
- `generate.py`: 处理测试生成相关的命令行参数和逻辑
- `evaluate.py`: 处理测试质量评估的命令行参数和逻辑

### 生成器模块 (`src/generators/`)
- `v8/`: 基础V8实现
- `v8_improved/`: 优化后的V8实现（推荐使用）
- `v8_modular/`: 模块化的V8实现

### 工具模块 (`src/utils/`)
- `logger.py`: 提供统一的日志配置
- `output_formatter.py`: 处理不同格式的输出

## 质量指标

- 文件生成成功率：100%
- 整体测试通过率：91.4%+
- 集合类型正确率：100%
- 边界值精确性：100%

## 开发指南

1. 所有新功能应添加到相应的`src/`子目录中
2. 避免在根目录创建单独的.py文件
3. 使用模块化设计，提高代码复用
4. 遵循现有的代码风格和命名规范
5. 添加适当的单元测试

## 维护建议

1. 定期清理`outputs/`目录中的旧文件
2. 保持文档与代码同步更新
3. 使用版本标签管理重要的发布
4. 通过Issue跟踪问题和功能请求