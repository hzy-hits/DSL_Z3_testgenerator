# DSL Test Generator v8.0 Extended (生产级)

一个高质量的DSL（领域特定语言）测试生成器，能够从YAML格式的需求文档自动生成全面的测试用例。支持状态机、业务场景和时序约束测试，达到生产级质量标准。

## 核心特性

- **状态机测试**: 支持状态转换、路径测试和边界条件验证
- **场景测试**: 端到端业务流程测试，支持复杂业务逻辑
- **时序约束测试**: 时间窗口、超时处理和并发时序验证
- **高质量生成**: 91.4%测试通过率，100%文件生成稳定性
- **智能约束求解**: 集成Z3求解器，支持复杂约束表达式
- **全面测试覆盖**: 功能、边界、负面、约束、规则等多维度测试

## 测试类型

### 基础测试类型
- **功能测试** (Functional): 验证基本功能
- **边界测试** (Boundary): 测试极限值和边界条件
- **约束测试** (Constraint): 满足/违反约束条件
- **负面测试** (Negative): 错误类型和无效值测试

### 高级测试类型
- **状态转换测试** (State Transition): 状态机行为验证
- **场景测试** (Scenario): 端到端业务流程测试
- **时序约束测试** (Timed Constraint): 时间窗口和超时处理
- **组合测试** (Combinatorial): 多属性组合测试

## 快速开始

### 环境要求

- Python 3.8+
- 支持的操作系统: macOS, Linux, Windows

### 安装依赖

使用 uv (推荐):
```bash
uv venv
source .venv/bin/activate  # Linux/macOS
uv pip install pyyaml z3-solver colorama tabulate
```

或使用 pip:
```bash
pip install pyyaml z3-solver colorama tabulate
```

## 使用方法

### 1. 基础测试生成

```bash
# 生成基础测试用例
python main.py generate examples/intermediate/shopping_cart.yaml

# 指定输出文件
python main.py generate examples/intermediate/shopping_cart.yaml -o outputs/cart_tests.json

# 批量处理
python main.py generate --batch examples/

# 生成详细报告
python main.py generate examples/advanced/advanced_ecommerce.yaml --report --format markdown
```

### 2. 扩展测试生成 (推荐)

使用扩展生成器获得完整的测试覆盖，包括状态机、场景和时序约束测试：

```bash
# 生成完整的扩展测试（包含状态机、场景、时序测试）
python generate_extended.py examples/dispatch_system.yaml

# 指定输出文件并启用详细日志
python generate_extended.py examples/dispatch_system.yaml -o dispatch_tests.json -v

# 生成购物车扩展测试
python generate_extended.py examples/intermediate/shopping_cart.yaml -o shopping_cart_extended.json
```

### 3. V2.0 生成器（实验性）

```bash
# 使用V2.0生成器
python v2.0/dsl2test.py --input examples/intermediate/shopping_cart.yaml --output v2_tests.json

# 使用高级功能
python v2.0/dsl2test_advanced.py --input examples/dispatch_system.yaml --output advanced_tests.json --analyze-combinations
```

## 项目结构

```
DSL Test Generator
├── generate_extended.py          # 扩展测试生成器 (推荐使用)
├── main.py                       # 基础测试生成器
├── examples/                     # 示例DSL文件
│   ├── dispatch_system.yaml      # 派单系统示例 (支持状态机)
│   ├── intermediate/
│   │   ├── shopping_cart.yaml       # 购物车示例
│   │   └── permission_system.yaml   # 权限系统示例
│   ├── advanced/
│   │   ├── advanced_ecommerce.yaml  # 复杂电商系统
│   │   └── user_account_system.yaml # 用户账户系统
│   └── basic/
│       └── simple_arrays.yaml       # 简单数组示例
├── src/                         # 源代码
│   ├── generators/
│   │   ├── v8/                     # V8基础生成器
│   │   ├── v8_extended/            # V8扩展生成器
│   │   ├── v8_improved/            # V8改进版本
│   │   └── v8_modular/             # V8模块化版本
│   ├── cli/                        # 命令行接口
│   └── utils/                      # 工具类
├── v2.0/                        # V2.0实验版本
├── docs/                        # 文档
├── tests/                       # 单元测试
└── pyproject.toml               # 项目配置
```

## DSL语法指南

### 基础实体定义

```yaml
domain: 你的业务领域

entities:
  - name: Order
    description: 订单实体
    attributes:
      - name: order_id
        type: integer
        min: 1
        max: 999999
        description: 订单ID
      
      - name: status
        type: integer
        enum_values: [1, 2, 3, 4]  # 1=创建, 2=支付, 3=发货, 4=完成
        description: 订单状态
      
      - name: amount
        type: real
        min: 0.01
        max: 99999.99
        description: 订单金额
```

### 约束定义

```yaml
constraints:
  # 简单约束
  - amount > 0
  - order_id > 0
  
  # 复杂约束
  - (status == 2) implies (amount > 0)
  - status >= 1 and status <= 4
```

### 状态机定义

```yaml
state_machines:
  - name: OrderFlow
    entity: Order
    state_attribute: status
    states:
      - name: Created
        value: 1
        description: "订单已创建"
      - name: Paid
        value: 2
        description: "订单已支付"
      - name: Shipped
        value: 3
        description: "订单已发货"
      - name: Completed
        value: 4
        description: "订单已完成"
    
    transitions:
      - name: PayOrder
        from: Created
        to: Paid
        condition: amount > 0
        description: "支付订单"
      
      - name: ShipOrder
        from: Paid
        to: Shipped
        condition: payment_confirmed == true
        description: "发货"
```

### 业务规则定义

```yaml
rules:
  - name: 订单超时取消
    condition: minutes_since_created > 30 and status == 1
    description: 创建30分钟后未支付自动取消
  
  - name: 金额验证
    condition: amount > 0 and amount <= 99999.99
    description: 订单金额必须在有效范围内
```

### 测试提示

```yaml
test_hints:
  - type: focus
    target: [status, amount, order_id]
    reason: 核心业务属性
  
  - type: combine
    target: [status, payment_method]
    reason: 状态与支付方式的组合测试
```

## 使用场景

### 1. 派单系统测试

```bash
# 生成包含状态机、时序约束和业务场景的完整测试
python generate_extended.py examples/dispatch_system.yaml -o dispatch_tests.json -v
```

生成的测试包括：
- 完整派单流程测试
- 拒单处理和重派流程
- 超时自动取消测试
- 改约流程测试
- 状态转换验证

### 2. 电商系统测试

```bash
# 生成电商系统测试
python generate_extended.py examples/intermediate/shopping_cart.yaml -o ecommerce_tests.json
```

### 3. 权限系统测试

```bash
# 生成权限系统测试
python main.py generate examples/intermediate/permission_system.yaml -o permission_tests.json --report
```

## 测试输出格式

生成的JSON测试文件包含：

```json
{
  "metadata": {
    "domain": "派单系统架构",
    "generation_time": "2025-07-14T17:15:37.080090",
    "generator_version": "v8_extended",
    "total_tests": 101,
    "total_entities": 8,
    "total_state_machines": 3
  },
  "summary": {
    "test_types": {
      "functional": 24,
      "boundary": 32,
      "negative": 16,
      "constraint_satisfaction": 8,
      "scenario": 21          # 场景测试
    },
    "coverage": {
      "state_coverage": 100.0,
      "transition_coverage": 100.0,
      "rule_coverage": 100.0
    }
  },
  "tests": [
    {
      "test_id": "ReserveOrder_scenario_complete_dispatch_flow",
      "test_type": "scenario",
      "description": "完整的派单流程测试：从创建预约到派单成功",
      "test_data": {
        "scenario_name": "complete_dispatch_flow",
        "steps": [
          {
            "action": "创建新的预约单",
            "timing": 0,
            "state_change": {"reserve_status": 1},
            "expected_result": {"reserve_order_created": true}
          }
        ]
      }
    }
  ]
}
```

## 高级功能

### 命令行参数

#### 基础生成器 (main.py)
```bash
python main.py [command] [options]

Commands:
  generate          生成测试用例
  evaluate          评估测试质量

Options:
  -o, --output      输出文件路径
  --batch           批量处理目录
  --report          生成详细报告
  --format          输出格式 (json/yaml/markdown/csv)
  --verbose         详细日志
  --validate        验证模式
```

#### 扩展生成器 (generate_extended.py)
```bash
python generate_extended.py <input_file> [options]

Options:
  -o, --output      输出文件路径 (默认: extended_tests.json)
  -v, --verbose     启用详细日志
  --version         显示版本信息
```

### 配置文件

项目配置在 `pyproject.toml` 中：

```toml
[project]
name = "dsl-test-generator"
version = "8.0.0"
description = "A high-quality DSL test generator"

dependencies = [
    "pyyaml>=6.0",
    "z3-solver>=4.12.0",
    "colorama>=0.4.6",
    "tabulate>=0.9.0",
]
```

## 贡献指南

1. Fork 项目
2. 创建功能分支 (`git checkout -b feature/AmazingFeature`)
3. 提交更改 (`git commit -m 'Add some AmazingFeature'`)
4. 推送到分支 (`git push origin feature/AmazingFeature`)
5. 开启 Pull Request

## 许可证

本项目采用 MIT 许可证 - 查看 [LICENSE](LICENSE) 文件了解详情。

## 问题反馈

如果遇到问题或有建议，请：

1. 查看 [docs/TROUBLESHOOTING.md](docs/TROUBLESHOOTING.md)
2. 在 [Issues](https://github.com/hzy-hits/DSL_Z3_testgenerator/issues) 中提交问题
3. 参考 [用户指南](USER_GUIDE.md) 获取详细帮助

## 更新日志

### v8.0 Extended (2025-07-14)
- 新增状态机测试支持
- 新增场景测试生成
- 新增时序约束测试
- 扩展YAML解析器支持
- 推出扩展测试生成器
- 显著提升测试覆盖率

### v8.0 Final (2024)
- 91.4%测试通过率
- 100%文件生成稳定性
- 增强Z3约束求解
- 完整测试类型支持

---

**DSL Test Generator** - 让测试生成变得简单而强大