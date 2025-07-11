# V2.0 项目结构

## 核心源代码
```
src/
├── core/                          # 核心模型和引擎
│   ├── combination_engine.py      # 组合测试引擎
│   └── concrete_value_generator.py # 具体值生成器
├── generators/                    # 测试生成器
│   ├── v8/                       # V8版本生成器
│   │   ├── __init__.py
│   │   ├── core.py              # 核心生成逻辑
│   │   ├── models.py            # 数据模型
│   │   ├── parser.py            # YAML解析器
│   │   ├── value_generator.py   # 值生成器
│   │   ├── constraint_handler.py # 约束处理
│   │   └── test_strategies.py   # 测试策略
│   ├── v8_improved/             # V8改进版 ⭐
│   │   ├── __init__.py
│   │   ├── improved_test_generator.py      # 改进的主生成器
│   │   ├── type_aware_value_generator.py   # 类型感知生成器
│   │   ├── negative_test_strategy.py       # 改进的负面测试
│   │   ├── boundary_test_strategy.py       # 精确边界值测试
│   │   ├── enhanced_constraint_solver.py   # 增强的约束求解
│   │   └── constraint_validator.py         # 约束验证器
│   └── v8_modular/              # V8模块化版本
├── layers/                       # 分层架构组件
│   ├── dsl_parser.py           # DSL解析层
│   ├── expression_parser.py     # 表达式解析
│   └── constraint_solver.py     # 约束求解层
├── strategies/                   # 测试策略
│   └── test_planner.py         # 测试规划器
└── utils/                       # 工具模块
    └── output_formatter.py      # 输出格式化
```

## 主要执行文件
```
├── v8_improved_generator.py     # V8改进版CLI ⭐
├── v8_final_optimized.py       # 最终优化版CLI ⭐⭐⭐
├── comprehensive_test_evaluation.py # 综合评估工具
├── evaluate_test_quality.py    # 测试质量验证工具
└── main.py                     # 原始主程序入口
```

## DSL示例文件
```
examples/
├── basic/                      # 基础示例
│   └── simple_arrays.yaml
├── intermediate/               # 中级示例
│   ├── shopping_cart.yaml     # 购物车系统
│   └── permission_system.yaml  # 权限系统
└── advanced/                   # 高级示例
    ├── advanced_ecommerce.yaml # 高级电商系统
    ├── order_processing_system.yaml
    ├── student_system_mixed.yaml
    └── user_account_system.yaml
```

## 文档
```
docs/
├── API_REFERENCE.md            # API参考
├── DSL_REFERENCE.md           # DSL语法参考
├── TROUBLESHOOTING.md         # 故障排除
├── Chinese_Support.md         # 中文支持
├── 中文需求转DSL指南.md        # 中文指南
├── final_optimization_summary.md # 最终优化总结
└── 各种优化报告...
```

## 配置文件
```
├── pyproject.toml             # Python项目配置
├── .gitignore                # Git忽略文件
├── LICENSE                   # MIT许可证
├── README.md                 # 项目说明
├── SETUP_GUIDE.md           # 设置指南
├── USER_GUIDE.md            # 用户指南
├── DSL_GUIDE.md             # DSL指南
├── CONTRIBUTING.md          # 贡献指南
├── MIGRATION_GUIDE.md       # 迁移指南
├── PROJECT_OVERVIEW.md      # 项目概览
├── PROJECT_STRUCTURE.md     # 本文件
└── final_optimization_report.md # 最终优化报告 ⭐
```

## 测试相关
```
tests/                         # 单元测试
test_outputs/                 # 测试输出目录
outputs/                      # 生成的测试用例输出
```

## 推荐使用

### 生产使用
```bash
# 使用最终优化版（推荐）
python v8_final_optimized.py examples/intermediate/shopping_cart.yaml

# 批量处理
python v8_final_optimized.py --batch examples/
```

### 开发调试
```bash
# 使用改进版生成器
python v8_improved_generator.py examples/intermediate/shopping_cart.yaml -v

# 评估测试质量
python evaluate_test_quality.py output_file.json
```

## 核心改进

1. **类型感知生成** - 正确处理所有数据类型，特别是集合类型
2. **精确边界值** - 生成满足约束的边界测试用例
3. **智能负面测试** - 生成违反约束而非错误类型的测试
4. **增强约束求解** - 改进的Z3集成和回退策略
5. **约束验证** - 自动验证和修复生成的测试用例

## 质量指标

- 文件生成成功率：100%
- 整体测试通过率：91.4%+
- 集合类型正确率：100%
- 边界值精确性：100%