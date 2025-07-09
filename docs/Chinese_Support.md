# Chinese Language Support / 中文支持说明

## What's Supported / 支持的内容

### ✅ Chinese Values in Data
- Domain names: `domain: 电商系统`
- String values: `name: "张三"`
- Enum values: `enum: ["待审核", "已通过", "已拒绝"]`
- Descriptions: `description: 这是一个描述`
- Rule names: `name: 年龄限制规则`

### ❌ What's NOT Supported
- Chinese DSL keywords (must use `entities`, not `实体`)
- Chinese variable names in constraints (use `user_age`, not `用户_年龄`)
- Chinese operators (use `and`, not `且`)

## Correct Usage Examples / 正确用法示例

### Example 1: Student System
```yaml
# All keywords must be English
domain: 学生管理系统  # Domain name can be Chinese

entities:
  - name: Student  # Entity names should be English
    attributes:
      - name: grade  # Attribute names should be English
        type: string  # Type keywords must be English
        enum: ["一年级", "二年级", "三年级"]  # Enum values can be Chinese
        description: 学生年级  # Descriptions can be Chinese

rules:
  - name: 低年级限制  # Rule names can be Chinese
    condition: student_grade == "一年级"  # String values can be Chinese
    implies: student_course_count <= 3
    description: 一年级学生最多选3门课
```

### Example 2: Order System
```yaml
domain: 订单系统

entities:
  - name: Order
    attributes:
      - name: status
        type: string
        enum: ["待付款", "待发货", "已发货", "已完成", "已取消"]
        default: "待付款"
      
      - name: payment_method
        type: string
        enum: ["支付宝", "微信支付", "银行卡", "信用卡"]

constraints:
  - order_status in ["待付款", "待发货", "已发货", "已完成", "已取消"]

rules:
  - name: 待付款订单限制
    condition: order_status == "待付款"
    implies: order_payment_method != null
```

## Why These Limitations? / 为什么有这些限制？

1. **Z3 Solver**: The underlying Z3 SMT solver only accepts ASCII identifiers
2. **Parser Design**: The DSL parser expects English keywords for parsing rules
3. **Compatibility**: Ensures compatibility with standard YAML/JSON tools

## Best Practices / 最佳实践

1. **Use English for Structure**
   ```yaml
   # Good
   entities:
     - name: User
       attributes:
         - name: status
   
   # Bad
   实体:
     - 名称: 用户
       属性:
         - 名称: 状态
   ```

2. **Use Chinese for Values**
   ```yaml
   # Good
   status:
     type: string
     enum: ["活跃", "休眠", "注销"]
   
   # This allows constraints like:
   constraints:
     - user_status == "活跃"
   ```

3. **Document in Chinese**
   ```yaml
   rules:
     - name: VIP会员优惠规则  # Chinese name
       condition: user_level == "VIP"
       implies: user_discount >= 0.8
       description: VIP会员享受8折优惠  # Chinese description
   ```

## Working with Chinese Requirements / 处理中文需求

### Step 1: Understand Requirements (Chinese)
```
需求：18岁以下的用户不能注册VIP会员
```

### Step 2: Translate to DSL (English structure, Chinese values)
```yaml
rules:
  - name: 未成年人限制
    condition: user_age < 18
    implies: user_member_type != "VIP会员"
    description: 18岁以下用户不能注册VIP会员
```

### Step 3: Generate Tests
The system will generate test cases that properly handle the Chinese values.

## Common Patterns / 常见模式

### Status Fields / 状态字段
```yaml
- name: approval_status
  type: string
  enum: ["待审核", "审核中", "已通过", "已拒绝"]
  default: "待审核"
```

### Level Fields / 等级字段
```yaml
- name: member_level
  type: string
  enum: ["普通会员", "银卡会员", "金卡会员", "钻石会员"]
```

### Category Fields / 分类字段
```yaml
- name: product_category
  type: string
  enum: ["电子产品", "服装", "食品", "图书", "其他"]
```

## Summary / 总结

- **Structure**: English (keywords, identifiers)
- **Content**: Can be Chinese (values, descriptions)
- **Result**: A system that works with Chinese business data while maintaining technical compatibility