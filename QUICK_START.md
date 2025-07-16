# Quick Start Guide

Get started with the DSL Test Generator in 5 minutes!

## 1. Install Dependencies

```bash
# Using uv (recommended)
uv venv && source .venv/bin/activate
uv pip install -e .

# Or using pip
pip install pyyaml z3-solver colorama tabulate
```

## 2. Create Your First DSL File

Create `my_system.yaml`:

```yaml
domain: My Business System

entities:
  - name: User
    attributes:
      - name: user_id
        type: integer
        min: 1
        max: 999999
      - name: account_balance
        type: real
        min: 0.0
        max: 100000.0
      - name: user_type
        type: integer
        enum_values: [1, 2, 3]  # 1=Basic, 2=Premium, 3=VIP
      - name: is_active
        type: boolean

constraints:
  - expression: account_balance >= 0
    description: No negative balance
  - expression: user_type >= 1 and user_type <= 3
    description: Valid user types only

rules:
  - name: VIP Benefits
    condition: user_type == 3
    action: max_withdrawal = 50000
    description: VIP users have higher limits
```

## 3. Generate Tests

```bash
python generate_extended.py my_system.yaml -o my_tests.json
```

## 4. View Results

The generator creates comprehensive tests including:
- ✅ Functional tests
- ✅ Boundary value tests  
- ✅ Constraint satisfaction tests
- ✅ Business rule tests
- ✅ Negative/error tests

## Example Output

```json
{
  "metadata": {
    "domain": "My Business System",
    "total_tests": 25,
    "generator_version": "v9.0"
  },
  "tests": [
    {
      "test_name": "User_functional_1",
      "test_type": "functional",
      "description": "Test basic functionality",
      "test_data": {
        "user_id": 12345,
        "account_balance": 1500.50,
        "user_type": 2,
        "is_active": true
      }
    }
  ]
}
```

## Next Steps

1. 📖 Read the [DSL Guide](DSL_GUIDE.md) for advanced features
2. 🔍 Explore [examples](examples/) for more complex scenarios
3. 🚀 Add state machines for workflow testing
4. 🎯 Define business rules for your domain

## Tips

- Use semantic naming: `order_count`, `delivery_distance`, `is_available`
- Define all constraints explicitly
- Document enum values clearly
- Start simple and add complexity gradually

That's it! You're ready to generate tests for any domain.