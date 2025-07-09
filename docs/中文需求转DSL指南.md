# 中文需求文档转换为DSL指南

## 概述

本指南帮助您将中文需求文档转换为可执行的DSL规范。虽然DSL语法必须使用英文，但可以通过注释保留中文说明。

## 转换步骤

### 1. 识别实体（Entities）

从需求中提取名词，通常是：
- 用户、客户、申请人 → User, Customer, Applicant
- 订单、商品、产品 → Order, Product, Item
- 账户、账单、交易 → Account, Bill, Transaction

**示例需求**：
> "贷款申请人必须年满18岁，信用分数不低于600分"

**转换为DSL**：
```yaml
entities:
  - name: Applicant  # 申请人
    attributes:
      - name: age      # 年龄
        type: integer
      - name: credit_score  # 信用分数
        type: integer
```

### 2. 提取约束（Constraints）

识别需求中的限制条件，关键词包括：
- 必须、需要、应该
- 不能、禁止、不允许
- 最大、最小、至少、至多

**示例需求**：
> "年龄必须在18到70岁之间"
> "贷款金额不能超过月收入的50倍"

**转换为DSL**：
```yaml
constraints:
  - applicant_age >= 18
  - applicant_age <= 70
  - loan_amount <= applicant_monthly_income * 50
```

### 3. 定义业务规则（Rules）

识别条件逻辑，关键词包括：
- 如果...则...
- 当...时...
- 只有...才...
- 除非...否则...

**示例需求**：
> "如果申请人信用分数低于600分，则必须提供抵押物"

**转换为DSL**：
```yaml
rules:
  - name: Low credit needs collateral
    condition: applicant_credit_score < 600
    implies: applicant_has_collateral == true
    description: 信用分低于600分必须有抵押物
```

## 常见中文术语映射

### 数据类型

| 中文描述 | DSL类型 | 示例 |
|---------|---------|------|
| 年龄、数量、个数 | integer | age, count, quantity |
| 金额、价格、费率 | real | amount, price, rate |
| 是否、有无 | boolean | is_active, has_collateral |
| 名称、编号、类型 | string | name, id, type |
| 列表、清单 | array | item_list, history |
| 分类、标签 | set | categories, tags |

### 比较运算

| 中文表达 | DSL运算符 | 示例 |
|---------|-----------|------|
| 大于、超过 | > | age > 18 |
| 至少、不少于 | >= | score >= 60 |
| 小于、低于 | < | rate < 0.1 |
| 最多、不超过 | <= | count <= 100 |
| 等于、为 | == | status == "active" |
| 不等于、不是 | != | type != "expired" |

### 逻辑运算

| 中文表达 | DSL运算符 | 示例 |
|---------|-----------|------|
| 并且、同时、且 | and | age >= 18 and score >= 600 |
| 或者、或 | or | type == "vip" or amount >= 1000 |
| 如果...则... | -> | age < 18 -> guardian_required == true |

## 完整转换示例

### 原始中文需求

> **贷款审批系统需求**
> 
> 1. 申请人基本要求：
>    - 年龄必须在18-70岁之间
>    - 必须有稳定收入（月收入大于0）
>    - 信用分数范围为300-850分
> 
> 2. 贷款规则：
>    - 25岁以下的申请人，贷款额度不超过50万
>    - 信用分数低于600分的申请人必须提供抵押物
>    - 月收入5万以上的申请人可享受优惠利率（不超过8%）
>    - 申请购房贷款的期限最长不超过30年（360个月）
> 
> 3. 风险控制：
>    - 如果申请人有超过10笔历史负债记录，贷款额度不能超过月收入的50倍

### 转换后的DSL

```yaml
# 贷款审批系统
domain: Loan Approval System

entities:
  - name: Applicant  # 申请人
    attributes:
      - name: age  # 年龄
        type: integer
        min: 18
        max: 70
      
      - name: monthly_income  # 月收入
        type: real
        min: 0
      
      - name: credit_score  # 信用分数
        type: integer
        min: 300
        max: 850
      
      - name: has_collateral  # 是否有抵押物
        type: boolean
      
      - name: debt_records  # 负债记录
        type: array[real]
        max_size: 100

  - name: Loan  # 贷款
    attributes:
      - name: amount  # 贷款金额
        type: real
        min: 0
      
      - name: term_months  # 期限（月）
        type: integer
        min: 1
        max: 360
      
      - name: interest_rate  # 利率
        type: real
        min: 0
        max: 1
      
      - name: type  # 贷款类型
        type: string
        enum: ["personal", "mortgage", "auto", "business"]

# 基本约束
constraints:
  - applicant_age >= 18 and applicant_age <= 70
  - applicant_monthly_income > 0
  - applicant_credit_score >= 300 and applicant_credit_score <= 850
  
# 业务规则
rules:
  - name: Young age limit  # 年轻人限额
    condition: applicant_age < 25
    implies: loan_amount <= 500000
  
  - name: Low credit collateral  # 低信用抵押
    condition: applicant_credit_score < 600
    implies: applicant_has_collateral == true
  
  - name: High income discount  # 高收入优惠
    condition: applicant_monthly_income >= 50000
    implies: loan_interest_rate <= 0.08
  
  - name: Mortgage term limit  # 房贷期限
    condition: loan_type == "mortgage"
    implies: loan_term_months <= 360
  
  - name: Debt risk control  # 负债风控
    condition: size(applicant_debt_records) > 10
    implies: loan_amount <= applicant_monthly_income * 50

# 测试要求
test_requirements:
  - name: Age boundaries  # 年龄边界
    type: boundary
    focus: [age]
  
  - name: Credit scenarios  # 信用场景
    type: equivalence
    focus: [credit_score]
  
  - name: Risk combinations  # 风险组合
    type: combinatorial
    combinations: 2
    focus: [age, credit_score, has_collateral]
```

## 最佳实践

1. **保持双语注释**：在关键位置添加中文注释
2. **使用描述性英文名**：选择清晰的英文标识符
3. **遵循命名规范**：
   - 实体名用 PascalCase：`LoanApplication`
   - 属性名用 snake_case：`credit_score`
   - 保持一致性

4. **验证转换**：
   - 检查所有需求都已覆盖
   - 确保约束条件完整
   - 测试生成的用例是否合理

## 常见问题

### Q: 为什么不能用中文变量名？
A: Z3求解器只支持ASCII字符的变量名，使用中文会导致求解失败。

### Q: 如何处理复杂的中文业务逻辑？
A: 分解为多个简单规则，每个规则对应一个具体的业务场景。

### Q: 描述字段可以用中文吗？
A: 可以，`description`字段支持中文，用于说明规则含义。