# 优化后的目录结构

```
v2.0/
├── src/                          # 源代码
│   ├── core/                     # 核心模块
│   │   ├── __init__.py
│   │   ├── combination_engine.py
│   │   ├── concrete_value_generator.py
│   │   └── test_generator.py
│   ├── parsers/                  # 解析器
│   │   ├── __init__.py
│   │   └── dsl_parser.py
│   ├── generators/               # 生成器
│   │   ├── __init__.py
│   │   ├── v1_generator.py      # dsl2test.py
│   │   ├── v2_generator.py      # unified_dsl2test_v2.py
│   │   └── v3_generator.py      # unified_dsl2test_v3.py
│   ├── evaluators/               # 评估器
│   │   ├── __init__.py
│   │   ├── test_evaluator.py
│   │   └── version_comparator.py
│   └── utils/                    # 工具类
│       ├── __init__.py
│       └── output_formatter.py
├── examples/                     # DSL 示例文件
│   ├── basic/                    # 基础示例
│   │   ├── simple_arrays.yaml
│   │   └── simple_test.yaml
│   ├── intermediate/             # 中级示例
│   │   ├── user_account_system.yaml
│   │   ├── shopping_cart.yaml
│   │   └── order_processing_system.yaml
│   └── advanced/                 # 高级示例
│       ├── permission_system.yaml
│       ├── student_system_mixed.yaml
│       └── advanced_ecommerce.yaml
├── outputs/                      # 输出结果
│   ├── v1/                      # V1 版本输出
│   ├── v2/                      # V2 版本输出
│   └── v3/                      # V3 版本输出
│       ├── user_account_v3.json
│       └── advanced_ecommerce_v3.json
├── tests/                       # 单元测试
│   ├── test_parsers.py
│   ├── test_generators.py
│   └── test_evaluators.py
├── configs/                     # 配置文件
│   ├── default_config.json
│   └── test_config_v3.json
├── docs/                        # 文档
│   ├── README.md
│   ├── USER_GUIDE.md
│   ├── DSL_REFERENCE.md
│   ├── API_REFERENCE.md
│   ├── TROUBLESHOOTING.md
│   └── OPTIMIZATION_SUMMARY.md
├── scripts/                     # 实用脚本
│   ├── compare_versions.py
│   ├── validate_tests.py
│   └── batch_generate.py
├── main.py                      # 主入口（V3）
├── requirements.txt
├── pyproject.toml
├── .gitignore
└── README.md
```