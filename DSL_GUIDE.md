# DSL Writing Guide with Z3 Solver

## Table of Contents
1. [Introduction](#introduction)
2. [DSL Structure](#dsl-structure)
3. [Z3 Solver Considerations](#z3-solver-considerations)
4. [Best Practices](#best-practices)
5. [Common Patterns](#common-patterns)
6. [Troubleshooting](#troubleshooting)

## Introduction

This guide explains how to write effective Domain Specific Language (DSL) files that work seamlessly with the Z3 SMT solver for automatic test generation.

## DSL Structure

A DSL file consists of the following sections:

### 1. Domain Declaration
```yaml
domain: Your Business Domain Name
```

### 2. Entities
Define the business objects in your system:

```yaml
entities:
  - name: Customer
    description: Customer information
    attributes:
      - name: age
        type: integer
        min: 18
        max: 120
        description: Customer age must be at least 18
      
      - name: member_type
        type: integer
        enum_values: [1, 2, 3]  # 1=Regular, 2=Silver, 3=Gold
        description: Membership level
      
      - name: account_balance
        type: real
        min: 0.0
        max: 1000000.0
        description: Account balance in USD
      
      - name: is_active
        type: boolean
        description: Whether account is active
```

### 3. Constraints
Global business rules that must always be satisfied:

```yaml
constraints:
  - expression: age >= 18
    description: Customers must be adults
  
  - expression: account_balance >= 0
    description: No negative balances allowed
  
  - expression: member_type >= 1 and member_type <= 3
    description: Valid membership levels only
```

### 4. Rules
Conditional business logic:

```yaml
rules:
  - name: Senior Discount
    condition: age >= 65
    action: discount = 10
    description: 10% discount for seniors
  
  - name: Premium Member Benefits
    condition: member_type == 3
    action: max_purchase_limit = 50000
    description: Gold members have higher limits
```

### 5. Test Requirements (Optional)
Guide test generation:

```yaml
test_requirements:
  - name: Age Validation Tests
    type: boundary
    focus: [age]
    description: Test age boundaries
  
  - name: Member Type Tests
    type: equivalence
    focus: [member_type]
    description: Test all membership levels
```

## Z3 Solver Considerations

### 1. Supported Data Types

The Z3 solver supports these types:

| DSL Type | Z3 Type | Example Values | Notes |
|----------|---------|----------------|-------|
| integer | Int | 1, -5, 100 | Whole numbers only |
| real | Real | 1.5, -3.14, 0.001 | Floating point numbers |
| boolean | Bool | true, false | Binary values |
| string | String | "text" | Limited support - use enums instead |

### 2. Expression Syntax

Z3 understands mathematical and logical expressions:

**Arithmetic Operators:**
- `+`, `-`, `*`, `/` - Basic math
- `%` - Modulo (integers only)

**Comparison Operators:**
- `==`, `!=` - Equality
- `<`, `<=`, `>`, `>=` - Ordering

**Logical Operators:**
- `and`, `or`, `not` - Boolean logic
- `implies` - Logical implication

**Examples:**
```yaml
# Simple constraint
expression: price > 0

# Compound constraint
expression: age >= 18 and age <= 65

# Implication
expression: is_premium implies discount >= 20

# Complex calculation
expression: total_price == base_price * quantity * (1 - discount/100)
```

### 3. Avoiding Z3 Limitations

#### Use Integers for Enums
Instead of strings, use integer mappings:

```yaml
# GOOD - Z3 friendly
attributes:
  - name: status
    type: integer
    enum_values: [1, 2, 3]  # 1=Active, 2=Pending, 3=Closed

# AVOID - Z3 has limited string support
attributes:
  - name: status
    type: string
    enum_values: ["Active", "Pending", "Closed"]
```

#### Keep Expressions Simple
Break complex logic into multiple rules:

```yaml
# GOOD - Simple, clear rules
rules:
  - name: Base Discount
    condition: purchase_amount > 100
    action: discount = 5
  
  - name: Additional Member Discount
    condition: is_member == true
    action: discount = discount + 5

# AVOID - Complex nested conditions
rules:
  - name: Complex Discount
    condition: (purchase_amount > 100 and is_member) or (purchase_amount > 500)
    action: discount = if(is_member, 10, 5)
```

#### Define Clear Boundaries
Always specify min/max for numeric types:

```yaml
# GOOD - Clear boundaries
attributes:
  - name: quantity
    type: integer
    min: 1
    max: 100

# AVOID - Unbounded values
attributes:
  - name: quantity
    type: integer
```

## Best Practices

### 1. Naming Conventions

- **Entities**: PascalCase (e.g., `CustomerOrder`)
- **Attributes**: snake_case (e.g., `order_total`)
- **Rules**: Descriptive names (e.g., `Bulk Purchase Discount`)

### 2. Documentation

Always include descriptions:

```yaml
entities:
  - name: Order
    description: Customer purchase order  # Document entity purpose
    attributes:
      - name: total_amount
        type: real
        min: 0.01
        max: 999999.99
        description: Total order value including tax  # Explain attribute
```

### 3. Constraint Organization

Group related constraints:

```yaml
constraints:
  # Age constraints
  - expression: customer_age >= 18
    description: Must be adult
  
  - expression: customer_age <= 120
    description: Reasonable age limit
  
  # Financial constraints
  - expression: order_total >= 0
    description: No negative orders
  
  - expression: discount_percent >= 0 and discount_percent <= 100
    description: Valid discount range
```

### 4. Test Coverage Strategy

Design your DSL to enable comprehensive testing:

```yaml
# Include boundary-friendly attributes
attributes:
  - name: score
    type: integer
    min: 0      # Clear lower boundary
    max: 100    # Clear upper boundary

# Add enum values for equivalence testing
  - name: tier
    type: integer
    enum_values: [1, 2, 3, 4]  # All valid values listed

# Create rules that can be tested
rules:
  - name: High Score Bonus
    condition: score >= 90
    action: bonus_points = 50
    # This creates testable scenarios: score=89 (no bonus), score=90 (bonus)
```

## Common Patterns

### 1. Percentage Validation
```yaml
attributes:
  - name: discount_percent
    type: integer
    min: 0
    max: 100

constraints:
  - expression: discount_percent >= 0 and discount_percent <= 100
    description: Valid percentage range
```

### 2. Status State Machine
```yaml
attributes:
  - name: order_status
    type: integer
    enum_values: [1, 2, 3, 4, 5]  # 1=New, 2=Processing, 3=Shipped, 4=Delivered, 5=Cancelled

rules:
  - name: Cancel Only New Orders
    condition: order_status > 1
    action: can_cancel = false
    description: Cannot cancel after processing starts
```

### 3. Date/Time as Days
Since Z3 doesn't handle dates well, use integers:

```yaml
attributes:
  - name: days_since_registration
    type: integer
    min: 0
    max: 3650  # ~10 years

rules:
  - name: New User Promotion
    condition: days_since_registration <= 30
    action: eligible_for_promo = true
```

### 4. Dependent Attributes
```yaml
constraints:
  - expression: end_date >= start_date
    description: End must be after start
  
  - expression: actual_amount <= budget_amount
    description: Cannot exceed budget
```

## Troubleshooting

### Common Errors and Solutions

#### 1. Parser Errors
**Error:** `KeyError: 'name'`

**Solution:** Ensure all entities, attributes, and test requirements have names:
```yaml
test_requirements:
  - name: My Test Requirement  # Don't forget this!
    type: boundary
    focus: [age]
```

#### 2. Z3 Type Mismatches
**Error:** `Z3 sort mismatch`

**Solution:** Ensure consistent types in expressions:
```yaml
# WRONG - Comparing integer to real
expression: age > 18.5  # age is integer

# CORRECT
expression: age > 18
```

#### 3. Unsatisfiable Constraints
**Error:** No test cases generated

**Solution:** Check for contradictory constraints:
```yaml
# WRONG - Impossible constraint
constraints:
  - expression: x > 10
  - expression: x < 5  # Contradiction!

# CORRECT - Valid range
constraints:
  - expression: x >= 5 and x <= 10
```

#### 4. Missing Boundaries
**Warning:** Incomplete test coverage

**Solution:** Add min/max values:
```yaml
attributes:
  - name: price
    type: real
    min: 0.01      # Add these
    max: 99999.99  # boundaries
```

### Validation Checklist

Before running the test generator:

- [ ] All entities have unique names
- [ ] All attributes have names and types
- [ ] Numeric attributes have min/max values
- [ ] Enum attributes use integers, not strings
- [ ] Constraints use valid Z3 expressions
- [ ] Rules have conditions and actions
- [ ] Test requirements have names (if used)
- [ ] No contradictory constraints

## Advanced Topics

### 1. Array Handling
For collections, define size constraints:

```yaml
attributes:
  - name: item_count
    type: integer
    min: 0
    max: 100
    description: Number of items in cart

constraints:
  - expression: item_count >= 0
    description: Non-negative item count
```

### 2. Conditional Constraints
Use implications for conditional logic:

```yaml
constraints:
  - expression: is_premium implies min_purchase == 0
    description: Premium users have no minimum
  
  - expression: not is_premium implies min_purchase >= 10
    description: Regular users have $10 minimum
```

### 3. Multi-Entity Relationships
Reference attributes across entities:

```yaml
constraints:
  - expression: order_customer_id == customer_id
    description: Order must belong to customer
  
  - expression: order_total <= customer_credit_limit
    description: Cannot exceed credit limit
```

## Examples

See the `demo/` directory for complete examples:
- `hotel_booking_system.yaml` - Service industry example
- `insurance_claim_system.yaml` - Financial domain example

## Z3 Resources

- [Z3 Python API](https://z3prover.github.io/api/html/namespacez3py.html)
- [Z3 Tutorial](https://rise4fun.com/z3/tutorialcontent/guide)
- [SMT-LIB Standard](http://smtlib.cs.uiowa.edu/)

## Configuration and Customization

The DSL Test Generator now supports flexible configuration to customize its behavior for different domains:

### Adjusting Precision
For financial applications requiring high precision:
```python
config = DSLEngineConfig()
config.test_generation.decimal_precision = 4  # 4 decimal places
```

### Extending Test Ranges
For testing edge cases further from boundaries:
```python
config.test_generation.negative_test_integer_extension = 5  # Test ±5 beyond bounds
config.test_generation.negative_test_real_extension = 10.0  # Test ±10.0 beyond bounds
```

### Business Logic Validation
Enable automatic correction of test data to match business rules:
```python
config.test_generation.validate_business_logic = True  # Ensures realistic test data
```

See `docs/API_REFERENCE.md` for complete configuration options.

## Summary

Writing effective DSLs for Z3-based test generation requires:
1. Clear structure with well-defined entities and attributes
2. Integer-based enums instead of strings
3. Explicit boundaries for all numeric values
4. Simple, testable business rules
5. Comprehensive test requirements to guide generation
6. Appropriate configuration for your domain

Follow these guidelines to create DSLs that generate high-quality, comprehensive test suites automatically.