# DSL Reference Guide

## Table of Contents

1. [Overview](#overview)
2. [Type System](#type-system)
3. [Entities](#entities)
4. [Constraints](#constraints)
5. [Rules](#rules)
6. [Test Requirements](#test-requirements)
7. [Collection Operations](#collection-operations)
8. [Examples](#examples)

## Overview

The DSL Test Generator uses YAML format to define system specifications. Each DSL file consists of:

- **domain**: The system domain name
- **entities**: Data structures with typed attributes
- **constraints**: System-wide invariants
- **rules**: Business logic conditions
- **test_requirements**: Test generation directives

## Type System

### Scalar Types

| Type | Description | Example |
|------|-------------|---------|
| `integer` | Whole numbers | `age: 25` |
| `real` | Floating-point numbers | `price: 19.99` |
| `boolean` | True/false values | `is_active: true` |
| `string` | Text values | `name: "John"` |

### Collection Types

| Type | Description | Example |
|------|-------------|---------|
| `array[T]` | Ordered list with duplicates | `array[integer]` |
| `set[T]` | Unordered unique elements | `set[string]` |

### Type Constraints

```yaml
attributes:
  - name: age
    type: integer
    min: 0          # Minimum value
    max: 150        # Maximum value
    
  - name: status
    type: string
    enum: [active, inactive, pending]  # Allowed values
    
  - name: email
    type: string
    pattern: "^[\\w.-]+@[\\w.-]+\\.\\w+$"  # Regex pattern
    
  - name: tags
    type: set[string]
    min_size: 1     # Minimum elements
    max_size: 10    # Maximum elements
    
  - name: scores
    type: array[real]
    min_size: 0
    max_size: 100
    min: 0.0        # Min value for elements
    max: 100.0      # Max value for elements
```

## Entities

Entities represent the main data structures in your system:

```yaml
entities:
  - name: User
    attributes:
      - name: id
        type: integer
        min: 1
      - name: username
        type: string
        pattern: "^[a-zA-Z0-9_]{3,20}$"
      - name: roles
        type: set[string]
        min_size: 1
        max_size: 5
      - name: preferences
        type: array[string]
        max_size: 50
      - name: is_verified
        type: boolean
        default: false
      - name: created_at
        type: integer  # Unix timestamp
        nullable: false
```

### Attribute Properties

- **name**: Attribute identifier
- **type**: Data type (scalar or collection)
- **min/max**: Value bounds for numeric types
- **min_size/max_size**: Size bounds for collections
- **enum**: Allowed values
- **pattern**: Regex for string validation
- **default**: Default value
- **nullable**: Whether null is allowed

## Constraints

Constraints define system-wide invariants that must always hold:

```yaml
constraints:
  # Simple comparisons
  - user_age >= 18
  - product_price > 0
  
  # Arithmetic expressions
  - order_total == order_subtotal + order_tax
  - account_balance >= 0
  
  # Logical operators
  - user_is_active == true and user_is_verified == true
  - status == "pending" or status == "processing"
  
  # Implications
  - user_is_premium == true -> user_subscription_end > current_time
  - order_status == "shipped" -> order_tracking_number != null
  
  # Collection constraints
  - size(user_roles) >= 1
  - size(cart_items) <= 100
  - "admin" in user_roles -> user_is_verified == true
  
  # Complex expressions
  - (user_age >= 65 or user_is_student == true) -> discount_rate >= 0.1
```

### Supported Operators

- **Comparison**: `>`, `<`, `>=`, `<=`, `==`, `!=`
- **Logical**: `and`, `or`, `not`, `->` (implies)
- **Arithmetic**: `+`, `-`, `*`, `/`
- **Collection**: `in`, `contains`, `size()`, `subset`

## Rules

Rules define conditional business logic:

```yaml
rules:
  - name: Premium user benefits
    condition: user_subscription_type == "premium"
    implies: user_storage_limit >= 100
    description: Premium users get at least 100GB storage
    priority: 1
    
  - name: Fraud detection
    condition: transaction_amount > 10000 and user_verified == false
    action: flag_for_review
    description: Large transactions from unverified users need review
    
  - name: Bulk discount
    condition: size(order_items) >= 10
    implies: order_discount_percent >= 10
    
  - name: Role-based access
    condition: "admin" in user_roles
    implies: size(user_permissions) >= 50
```

### Rule Properties

- **name**: Unique rule identifier
- **condition**: Triggering condition
- **implies**: Constraint that must hold when condition is true
- **action**: Action to take (alternative to implies)
- **description**: Human-readable explanation
- **priority**: Execution order (higher = first)

## Test Requirements

Control how tests are generated:

```yaml
test_requirements:
  - name: User boundary tests
    type: boundary
    focus: [age, balance]
    
  - name: Cart collection tests
    type: collection
    collection_tests: [empty, single, multiple, boundary]
    
  - name: Security combinations
    type: combinatorial
    combinations: 3
    focus: [is_verified, is_active, roles]
    
  - name: Negative scenarios
    type: negative
    focus: [constraints]
    
  - name: Equivalence partitions
    type: equivalence
    focus: [status, subscription_type]
```

### Test Types

| Type | Description | Parameters |
|------|-------------|------------|
| `boundary` | Test min/max values | `focus`: attributes to test |
| `equivalence` | Test representative values | `focus`: attributes to test |
| `negative` | Test constraint violations | `focus`: constraints to violate |
| `collection` | Test collection scenarios | `collection_tests`: test types |
| `combinatorial` | Test value combinations | `combinations`: n-way testing |

### Collection Test Types

- **empty**: Empty collection
- **single**: Single element
- **multiple**: Multiple elements
- **boundary**: Min/max size
- **duplicates**: Duplicate elements (arrays only)

## Collection Operations

### Size Operations

```yaml
constraints:
  - size(array_var) >= 5
  - length(set_var) <= 10  # 'length' is alias for 'size'
  - cart_items.size > 0    # Property syntax
```

### Membership Operations

```yaml
constraints:
  - "admin" in user_roles
  - product_categories contains "electronics"
  - user_id in allowed_users
```

### Set Operations

```yaml
constraints:
  - required_permissions subset user_permissions
  - user_roles subset available_roles
```

### Array Access

```yaml
constraints:
  - scores[0] >= 0         # First element
  - grades[index] <= 100   # Variable index
```

## Examples

### Example 1: User Authentication System

```yaml
domain: Authentication System

entities:
  - name: User
    attributes:
      - name: username
        type: string
        pattern: "^[a-zA-Z0-9_]{3,20}$"
      - name: password_attempts
        type: integer
        min: 0
        max: 5
      - name: roles
        type: set[string]
        min_size: 1
        max_size: 10
      - name: sessions
        type: array[integer]
        max_size: 5
      - name: is_locked
        type: boolean

constraints:
  - user_password_attempts <= 5
  - user_is_locked == true -> user_password_attempts >= 5
  - size(user_sessions) <= 5
  - size(user_roles) >= 1

rules:
  - name: Account lockout
    condition: user_password_attempts >= 5
    implies: user_is_locked == true
    
  - name: Admin multi-session
    condition: "admin" in user_roles
    implies: size(user_sessions) <= 10

test_requirements:
  - name: Security boundaries
    type: boundary
    focus: [password_attempts]
  - name: Role combinations
    type: combinatorial
    combinations: 2
```

### Example 2: E-commerce Order System

```yaml
domain: Order Management

entities:
  - name: Order
    attributes:
      - name: items
        type: array[integer]
        min_size: 1
        max_size: 100
      - name: total
        type: real
        min: 0
      - name: discounts
        type: set[string]
        max_size: 5
      - name: status
        type: string
        enum: [pending, processing, shipped, delivered]
      - name: is_express
        type: boolean

constraints:
  - order_total >= 0
  - size(order_items) >= 1
  - order_status == "shipped" -> order_total > 0
  - size(order_discounts) <= 5

rules:
  - name: Free express shipping
    condition: order_total >= 100
    implies: order_is_express == true
    
  - name: Bulk order discount
    condition: size(order_items) >= 20
    implies: "BULK20" in order_discounts

test_requirements:
  - name: Order scenarios
    type: collection
    collection_tests: [single, multiple, boundary]
  - name: Status transitions
    type: equivalence
    focus: [status]
```

## Best Practices

1. **Use meaningful names**: Choose descriptive names for entities and attributes
2. **Define appropriate bounds**: Set realistic min/max values
3. **Keep constraints simple**: Complex constraints are harder to solve
4. **Document rules**: Use descriptions to explain business logic
5. **Focus test generation**: Use test requirements to target specific scenarios
6. **Validate patterns**: Test regex patterns before using them
7. **Consider null values**: Explicitly mark nullable attributes