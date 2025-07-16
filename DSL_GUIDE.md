# DSL Writing Guide - Domain-Agnostic Test Generation

## Table of Contents
1. [Introduction](#introduction)
2. [DSL Structure](#dsl-structure)
3. [Semantic Naming Convention](#semantic-naming-convention)
4. [State Machines](#state-machines)
5. [Business Rules](#business-rules)
6. [Best Practices](#best-practices)
7. [Real-World Examples](#real-world-examples)

## Introduction

This guide explains how to write effective Domain Specific Language (DSL) files for the generic test generator. The system uses semantic analysis to understand your domain without requiring any code changes.

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

## Semantic Naming Convention

The generator understands attribute meanings from their names. Follow these patterns for automatic semantic understanding:

### Distance and Location
- `*_distance`, `*_radius`, `*_range` → Geographic distances
- `*_location`, `*_position` → Location identifiers
- `*_coordinate`, `*_latitude`, `*_longitude` → GPS coordinates

### Time and Duration
- `*_time`, `*_timestamp` → Time values
- `*_duration`, `*_hours`, `*_minutes` → Time periods
- `*_date`, `*_day`, `*_month`, `*_year` → Date components
- `hours_until_*`, `*_before`, `*_after` → Time relationships

### Quantities and Counts
- `*_count`, `*_number`, `*_quantity` → Integer counts
- `*_amount` → Can be integer or decimal
- `*_size`, `*_length`, `*_width`, `*_height` → Dimensions

### Financial
- `*_price`, `*_cost`, `*_fee` → Monetary values
- `*_balance`, `*_credit`, `*_debit` → Account values
- `*_rate`, `*_percentage` → Percentages

### Status and Types
- `*_status`, `*_state` → State indicators
- `*_type`, `*_category`, `*_class` → Classification
- `*_level`, `*_grade`, `*_rank` → Hierarchical values

### Boolean Indicators
- `is_*`, `has_*`, `can_*` → Boolean flags
- `*_enabled`, `*_active`, `*_available` → Availability flags

### Example Impact:
```yaml
# The generator automatically understands:
attributes:
  - name: delivery_distance  # Will generate values like 2.5, 5.8, 8.9
  - name: order_count       # Will generate integers: 0, 1, 5, 10
  - name: total_price       # Will generate prices: 9.99, 49.99, 199.99
  - name: is_available      # Will generate: true/false
```

## State Machines

State machines allow you to model and test temporal behavior and state transitions in your system.

### Structure

```yaml
state_machines:
  - name: OrderStatusFlow
    entity: Order              # Which entity this state machine applies to
    state_attribute: status    # Which attribute represents the state
    states:
      - name: PendingPayment
        description: "Order awaiting payment"
      - name: PendingShipment
        description: "Order paid, ready to ship"
      - name: Shipped
        description: "Order has been shipped"
      - name: Cancelled
        description: "Order has been cancelled"
    
    transitions:
      - name: PayOrder
        from: PendingPayment
        to: PendingShipment
        condition: order_has_stock == true and order_amount > 0
        description: "Complete payment when stock available"
      
      - name: CancelOrder
        from: PendingPayment
        to: Cancelled
        condition: true
        description: "Cancel pending order"
```

### Generated Test Types

State machines automatically generate:
- **Valid Transition Tests**: Tests for each valid transition
- **Invalid Transition Tests**: Tests for forbidden transitions
- **State Coverage Tests**: Ensures all states are tested
- **Condition Boundary Tests**: Tests transition conditions

## Business Rules

Define complex business logic that spans entities:

```yaml
rules:
  - name: High Value Customer Discount
    condition: customer_total_purchases > 10000
    action: discount_percentage = 20
    description: Customers with >$10k purchases get 20% discount
  
  - name: Rush Order Premium
    condition: delivery_type == "rush" and hours_until_delivery < 24
    action: delivery_fee = base_fee * 2
    description: Double fee for rush orders
  
  - name: Skill Matching Requirement
    condition: service_type == 1
    action: service_person_skill_daily == true
    description: Daily cleaning requires daily skill
```

### Cross-Entity Rules

Rules can reference multiple entities:

```yaml
rules:
  - name: Driver Assignment Rule
    condition: order_weight > 50 and driver_has_truck == true
    action: can_assign = true
    description: Heavy orders require drivers with trucks
```

## Best Practices

### 1. Use Meaningful Names
```yaml
# Good - semantic meaning is clear
attributes:
  - name: order_total_amount
  - name: customer_age
  - name: delivery_distance

# Poor - ambiguous names
attributes:
  - name: amt
  - name: val1
  - name: temp
```

### 2. Define Clear Constraints
```yaml
# Good - explicit constraints
constraints:
  - expression: age >= 18 and age <= 120
    description: Valid age range
  
# Poor - implicit constraints
# (Don't rely on just min/max in attributes)
```

### 3. Document Everything
```yaml
entities:
  - name: Order
    description: Customer order with delivery details  # Clear description
    attributes:
      - name: status
        type: integer
        enum_values: [1, 2, 3, 4, 5]  # Document each value
        description: Order status (1=New, 2=Processing, 3=Shipped, 4=Delivered, 5=Cancelled)
```

### 4. Use Appropriate Data Types
```yaml
# Good - appropriate types
attributes:
  - name: user_count
    type: integer    # Counts are integers
  
  - name: product_price
    type: real       # Prices can have decimals
  
  - name: is_premium
    type: boolean    # Clear true/false

# Poor - wrong types
attributes:
  - name: user_count
    type: string     # Don't use string for numbers
```

## Real-World Examples

### 1. E-Commerce System
```yaml
domain: E-Commerce Platform

entities:
  - name: Product
    attributes:
      - name: product_id
        type: integer
        min: 1000
        max: 999999
      - name: price
        type: real
        min: 0.01
        max: 10000.00
      - name: stock_count
        type: integer
        min: 0
        max: 9999
      - name: is_available
        type: boolean

  - name: Order
    attributes:
      - name: order_id
        type: integer
      - name: total_amount
        type: real
        min: 0.01
      - name: order_status
        type: integer
        enum_values: [1, 2, 3, 4, 5]

constraints:
  - expression: stock_count >= 0
    description: Stock cannot be negative
  - expression: total_amount > 0
    description: Order must have positive value

rules:
  - name: Out of Stock Check
    condition: stock_count == 0
    action: is_available = false
    description: Products with no stock are unavailable
```

### 2. Banking System
```yaml
domain: Banking System

entities:
  - name: Account
    attributes:
      - name: account_balance
        type: real
        min: 0.0
      - name: daily_withdrawal_amount
        type: real
        min: 0.0
      - name: account_type
        type: integer
        enum_values: [1, 2, 3]  # 1=Checking, 2=Savings, 3=Business
      - name: is_active
        type: boolean

constraints:
  - expression: account_balance >= 0
    description: No overdrafts allowed
  - expression: daily_withdrawal_amount <= 5000
    description: Daily limit $5000

rules:
  - name: Business Account Unlimited
    condition: account_type == 3
    action: daily_withdrawal_limit = 999999
    description: Business accounts have no daily limit
```

### 3. Delivery Service
```yaml
domain: Delivery Service

entities:
  - name: Driver
    attributes:
      - name: driver_id
        type: integer
      - name: current_location_distance
        type: real
        min: 0.0
        max: 100.0
      - name: has_vehicle
        type: boolean
      - name: delivery_count
        type: integer
        min: 0

  - name: Delivery
    attributes:
      - name: delivery_id
        type: integer
      - name: pickup_distance
        type: real
        min: 0.1
        max: 50.0
      - name: delivery_distance
        type: real
        min: 0.1
        max: 50.0
      - name: delivery_status
        type: integer
        enum_values: [1, 2, 3, 4]

constraints:
  - expression: pickup_distance <= 25.0
    description: Maximum pickup distance 25km
  - expression: delivery_distance <= 50.0
    description: Maximum delivery distance 50km

state_machines:
  - name: DeliveryFlow
    entity: Delivery
    state_attribute: delivery_status
    states:
      - name: Assigned
        value: 1
      - name: PickedUp
        value: 2
      - name: InTransit
        value: 3
      - name: Delivered
        value: 4
    transitions:
      - name: Pickup
        from: Assigned
        to: PickedUp
        condition: driver_at_pickup_location == true
      - name: StartDelivery
        from: PickedUp
        to: InTransit
        condition: true
      - name: CompleteDelivery
        from: InTransit
        to: Delivered
        condition: driver_at_delivery_location == true
```

## Tips for Success

1. **Start Simple**: Begin with basic entities and add complexity gradually
2. **Test Incrementally**: Generate tests after each major addition
3. **Use Comments**: YAML supports `#` comments - use them liberally
4. **Validate Your DSL**: Run the generator with `-v` flag to see parsing details
5. **Check Coverage**: Review the generated test summary to ensure completeness

## Common Pitfalls to Avoid

1. **Ambiguous Names**: Avoid generic names like `value`, `data`, `info`
2. **Missing Constraints**: Always define business rules as constraints
3. **Wrong Types**: Don't use strings for numeric values
4. **Undocumented Enums**: Always explain what each enum value means
5. **Complex Expressions**: Keep constraints simple and readable

---

With this guide, you can create DSL files for any business domain. The generator will automatically understand your semantics and create comprehensive tests without any code changes.