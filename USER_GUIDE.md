# DSL Test Generator v8.0 Extended - 用户指南

本文档详细介绍如何使用DSL测试生成器创建高质量的测试用例，包括新增的状态机、场景和时序约束测试功能。

## 目录

1. [快速开始](#快速开始)
2. [基础使用](#基础使用)
3. [扩展功能](#扩展功能)
4. [DSL语法详解](#dsl语法详解)
5. [高级特性](#高级特性)
6. [最佳实践](#最佳实践)
7. [故障排除](#故障排除)

## 快速开始

### 环境要求

- Python 3.8+
- 操作系统: macOS, Linux, Windows
- 内存: 建议4GB以上

### 安装步骤

1. **使用 uv (推荐)**
   ```bash
   # 安装 uv (如果没有的话)
   curl -LsSf https://astral.sh/uv/install.sh | sh
   
   # 创建虚拟环境
   uv venv
   source .venv/bin/activate  # Linux/macOS
   
   # 安装依赖
   uv pip install pyyaml z3-solver colorama tabulate
   ```

2. **使用 pip**
   ```bash
   pip install pyyaml z3-solver colorama tabulate
   ```

### 5分钟快速体验

```bash
# 1. 生成基础测试
python main.py generate examples/intermediate/shopping_cart.yaml

# 2. 生成扩展测试（推荐）
python generate_extended.py examples/dispatch_system.yaml -v

# 3. 查看生成的测试文件
cat extended_tests.json
```

##  基础使用

### 1. 基础测试生成

```bash
# 最简单的用法
python main.py generate <yaml_file>

# 指定输出文件
python main.py generate examples/intermediate/shopping_cart.yaml -o my_tests.json

# 批量处理
python main.py generate --batch examples/

# 生成报告
python main.py generate examples/advanced/advanced_ecommerce.yaml --report
```

### 2. 输出格式选择

```bash
# JSON格式 (默认)
python main.py generate input.yaml --format json

# YAML格式
python main.py generate input.yaml --format yaml

# Markdown报告
python main.py generate input.yaml --format markdown

# CSV格式
python main.py generate input.yaml --format csv
```

##  扩展功能

### 1. 扩展测试生成器

扩展生成器是本项目的核心特性，支持状态机、场景和时序约束测试：

```bash
# 基本用法
python generate_extended.py <input_file>

# 详细用法
python generate_extended.py examples/dispatch_system.yaml \
  -o dispatch_comprehensive_tests.json \
  -v
```

**扩展功能优势：**
-  **状态机测试**: 自动验证状态转换逻辑
-  **场景测试**: 端到端业务流程验证
-  **时序约束测试**: 时间窗口和超时处理
-  **更高覆盖率**: 传统测试 + 业务逻辑测试

### 2. V2.0 实验性功能

```bash
# 基础V2.0生成
python v2.0/dsl2test.py --input input.yaml --output output.json

# 高级组合分析
python v2.0/dsl2test_advanced.py \
  --input examples/dispatch_system.yaml \
  --output advanced_tests.json \
  --analyze-combinations \
  --use-advanced-planner
```

##  DSL语法详解

### 1. 基础结构

```yaml
domain: 业务领域名称

entities:
  - name: 实体名称
    description: 实体描述
    attributes: []

constraints: []
rules: []
state_machines: []  # 新增
test_hints: []      # 新增
```

### 2. 实体定义

#### 基础属性类型

```yaml
entities:
  - name: User
    attributes:
      # 整数类型
      - name: user_id
        type: integer
        min: 1
        max: 999999
        description: 用户ID
      
      # 实数类型
      - name: balance
        type: real
        min: 0.0
        max: 99999.99
        description: 账户余额
      
      # 字符串类型
      - name: username
        type: string
        min_length: 3
        max_length: 20
        pattern: "^[a-zA-Z0-9_]+$"
        description: 用户名
      
      # 布尔类型
      - name: is_active
        type: boolean
        description: 是否激活
      
      # 枚举类型
      - name: status
        type: integer
        enum_values: [1, 2, 3, 4]
        description: 状态
```

#### 集合类型

```yaml
attributes:
  # 数组类型
  - name: tags
    type: array[string]
    min_size: 0
    max_size: 10
    description: 标签列表
  
  # 集合类型
  - name: permissions
    type: set[integer]
    min_size: 1
    max_size: 20
    description: 权限集合
```

### 3. 约束定义

#### 简单约束

```yaml
constraints:
  - user_id > 0
  - balance >= 0
  - length(username) >= 3
```

#### 复杂约束

```yaml
constraints:
  # 逻辑约束
  - (is_active == true) implies (status > 0)
  - (status == 4) implies (balance == 0)
  
  # 集合约束
  - size(tags) <= 10
  - size(permissions) >= 1
  
  # 跨字段约束
  - (user_type == "premium") implies (balance >= 100)
```

### 4. 状态机定义 

状态机是扩展功能的核心特性：

```yaml
state_machines:
  - name: UserLifecycle
    entity: User
    state_attribute: status
    
    states:
      - name: Inactive
        value: 1
        description: "未激活"
      - name: Active
        value: 2
        description: "已激活"
      - name: Suspended
        value: 3
        description: "已暂停"
      - name: Deleted
        value: 4
        description: "已删除"
    
    transitions:
      - name: Activate
        from: Inactive
        to: Active
        condition: email_verified == true
        description: "激活用户"
      
      - name: Suspend
        from: Active
        to: Suspended
        condition: violation_count >= 3
        description: "暂停用户"
      
      - name: Delete
        from: [Active, Suspended]  # 支持多源状态
        to: Deleted
        condition: delete_requested == true
        description: "删除用户"
```

### 5. 业务规则定义

```yaml
rules:
  # 时序规则
  - name: 账户自动锁定
    condition: failed_login_attempts >= 5 and last_login_minutes > 30
    description: 连续失败登录5次且30分钟内无活动则锁定账户
  
  # 业务逻辑规则
  - name: VIP升级条件
    condition: balance >= 10000 and transaction_count >= 100
    description: 余额超过1万且交易次数超过100次自动升级VIP
  
  # 状态规则
  - name: 暂停用户限制
    condition: status == 3
    description: 暂停用户不能进行交易操作
```

### 6. 测试提示 

指导生成器重点测试特定属性或场景：

```yaml
test_hints:
  # 关注重点属性
  - type: focus
    target: [user_id, status, balance]
    reason: 核心业务属性，需要重点测试
  
  # 属性组合测试
  - type: combine
    target: [status, is_active, user_type]
    reason: 状态、激活状态和用户类型的组合很重要
  
  # 忽略某些属性
  - type: ignore
    target: [created_at, updated_at]
    reason: 时间戳字段不需要重点测试
```

##  高级特性

### 1. 复杂场景测试

扩展生成器会自动识别和生成以下场景测试：

#### 派单系统场景
```yaml
# 会自动生成的场景测试：
- 完整派单流程测试
- 拒单处理和重派流程
- 超时自动取消测试
- 改约流程测试
- 服务人员状态转换
```

#### 电商系统场景
```yaml
# 会自动生成的场景测试：
- 下单支付完整流程
- 购物车操作序列
- 库存扣减和恢复
- 优惠券使用流程
- 退款处理流程
```

### 2. 时序约束测试

自动检测和测试时间相关的业务规则：

```yaml
# 示例：系统会自动识别这些时序约束
rules:
  - name: 支付超时
    condition: order_status == 1 and minutes_since_created > 30
    description: 订单创建30分钟后未支付自动取消

# 生成的测试包括：
- 29分钟时的测试（不触发）
- 30分钟时的边界测试
- 31分钟时的测试（触发取消）
```

### 3. 状态转换测试

自动生成状态机的各种测试：

```yaml
# 自动生成的测试类型：
- 有效状态转换测试
- 无效状态转换测试（不允许的跳转）
- 状态转换路径测试（完整流程）
- 转换条件边界测试
```

##  测试输出解析

### 1. 输出文件结构

```json
{
  "metadata": {
    "domain": "业务领域",
    "generation_time": "生成时间",
    "generator_version": "生成器版本",
    "total_tests": 101,
    "total_entities": 8,
    "total_state_machines": 3
  },
  "summary": {
    "test_types": {
      "functional": 24,        // 功能测试
      "boundary": 32,          // 边界测试
      "negative": 16,          // 负面测试
      "constraint_satisfaction": 8,  // 约束测试
      "scenario": 21           // 场景测试 
    },
    "coverage": {
      "state_coverage": 100.0,      // 状态覆盖率
      "transition_coverage": 100.0,  // 转换覆盖率
      "rule_coverage": 100.0        // 规则覆盖率
    }
  },
  "tests": [ /* 详细测试用例 */ ]
}
```

### 2. 测试用例结构

#### 基础测试用例
```json
{
  "test_id": "User_functional_1",
  "test_name": "User_functional_1",
  "test_type": "functional",
  "description": "Test basic functionality of User",
  "test_data": {
    "user_id": 12345,
    "username": "testuser",
    "balance": 1000.50,
    "is_active": true,
    "status": 2
  },
  "expected_result": "pass",
  "priority": 8
}
```

#### 场景测试用例 
```json
{
  "test_id": "User_scenario_complete_lifecycle",
  "test_type": "scenario",
  "description": "用户完整生命周期测试",
  "test_data": {
    "scenario_name": "user_complete_lifecycle",
    "steps": [
      {
        "action": "创建用户",
        "timing": 0,
        "state_change": {"status": 1},
        "expected_result": {"user_created": true}
      },
      {
        "action": "激活用户",
        "timing": 5,
        "state_change": {"status": 2, "is_active": true},
        "expected_result": {"user_activated": true}
      }
    ]
  },
  "expected_result": "pass",
  "priority": 9
}
```

##  最佳实践

### 1. DSL编写建议

#### 实体设计
```yaml
#  好的实体设计
entities:
  - name: Order  # 简洁明确的名称
    description: 订单实体  # 清晰的描述
    attributes:
      - name: order_id
        type: integer
        min: 1
        max: 999999999  # 合理的范围
        description: 订单唯一标识  # 详细描述
```

#### 约束设计
```yaml
#  好的约束设计
constraints:
  # 简单易懂
  - order_id > 0
  - total_amount >= 0
  
  # 业务逻辑清晰
  - (status == "paid") implies (payment_time > 0)
  - (user_type == "vip") implies (discount_rate >= 0.1)
```

#### 状态机设计
```yaml
#  好的状态机设计
state_machines:
  - name: OrderFlow
    entity: Order
    state_attribute: status
    states:
      # 状态定义清晰
      - name: Created
        value: 1
        description: "订单已创建"
    transitions:
      # 转换条件明确
      - name: PayOrder
        from: Created
        to: Paid
        condition: payment_amount >= total_amount
        description: "支付订单"
```

### 2. 测试策略

#### 选择合适的生成器
```bash
# 简单系统：使用基础生成器
python main.py generate simple_system.yaml

# 复杂业务系统：使用扩展生成器
python generate_extended.py complex_system.yaml -v

# 实验性功能：使用V2.0
python v2.0/dsl2test_advanced.py --input complex_system.yaml --analyze-combinations
```

#### 测试重点配置
```yaml
test_hints:
  # 核心业务流程
  - type: focus
    target: [order_status, payment_status, user_id]
    reason: 订单核心属性
  
  # 重要组合
  - type: combine
    target: [user_type, order_amount, discount_rate]
    reason: 影响定价的关键组合
```

### 3. 性能优化

#### 大型系统处理
```bash
# 分批处理大型系统
python main.py generate --batch large_system_dir/ --timeout 300

# 限制测试数量
python generate_extended.py large_system.yaml --max-tests 500
```

#### 内存优化
```yaml
# 控制集合大小
attributes:
  - name: items
    type: array[integer]
    max_size: 100  # 避免过大的集合
```

##  故障排除

### 1. 常见问题

#### 依赖问题
```bash
# 问题：ModuleNotFoundError: No module named 'yaml'
# 解决：
uv pip install pyyaml

# 问题：Z3 solver timeout
# 解决：简化约束或增加超时时间
```

#### 解析错误
```yaml
# 问题：YAML解析失败
# 检查：缩进是否正确，是否有语法错误

#  错误的缩进
entities:
- name: User
attributes:
  - name: id

#  正确的缩进
entities:
  - name: User
    attributes:
      - name: id
```

#### 约束冲突
```yaml
# 问题：约束不可满足
# 检查：约束是否互相矛盾

#  矛盾约束
constraints:
  - value > 100
  - value < 50

#  合理约束
constraints:
  - value >= 0
  - value <= 1000
```

### 2. 调试技巧

#### 启用详细日志
```bash
# 查看详细生成过程
python generate_extended.py input.yaml -v

# 查看约束求解过程
python main.py generate input.yaml --verbose
```

#### 分步验证
```bash
# 1. 先验证DSL语法
python main.py generate input.yaml --validate-only

# 2. 生成简单测试
python main.py generate input.yaml --max-tests 10

# 3. 逐步增加复杂度
python generate_extended.py input.yaml
```

### 3. 性能监控

#### 生成时间优化
```bash
# 监控生成时间
time python generate_extended.py input.yaml

# 如果太慢，尝试：
# 1. 简化约束
# 2. 减少实体数量
# 3. 限制测试数量
```

##  参考资源

- [DSL语法参考](docs/DSL_REFERENCE.md)
- [API文档](docs/API_REFERENCE.md)
- [故障排除指南](docs/TROUBLESHOOTING.md)
- [贡献指南](CONTRIBUTING.md)

---

**DSL Test Generator v8.0 Extended** - 让复杂业务测试变得简单 