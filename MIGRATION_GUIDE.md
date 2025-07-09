# Migration Guide

## Migrating from Version 0.2.x to 0.3.x

### New Features in v0.3.0

#### 1. Configuration System

The biggest change in v0.3.0 is the introduction of a comprehensive configuration system:

```python
from dsl_test_generator import DSLEngine, DSLEngineConfig

# Create custom configuration
config = DSLEngineConfig()
config.test_generation.validate_business_logic = True
config.test_generation.decimal_precision = 2
config.solver.timeout = 10000

# Use with engine
engine = DSLEngine(config)
```

#### 2. Business Logic Validation

Test data is now automatically validated and corrected to ensure business logic consistency:

```yaml
# This constraint is now automatically enforced in generated tests
constraints:
  - claim_type == policy_type
```

#### 3. No More Hardcoded Values

All previously hardcoded values are now configurable:
- Decimal precision (was 6, now configurable)
- Collection limits (was 10/100, now configurable)
- Test ranges (was ±1, now configurable)

### Migration Steps

1. **Update imports** (if using Python API):
   ```python
   # Old
   from dsl_test_generator import DSLEngine
   
   # New (optional - works with defaults)
   from dsl_test_generator import DSLEngine, DSLEngineConfig
   ```

2. **No DSL changes required** - Your existing DSL files work as-is

3. **Optional: Add configuration** for better control:
   ```python
   config = DSLEngineConfig()
   config.test_generation.validate_business_logic = True
   engine = DSLEngine(config)
   ```

### CLI Changes

The CLI tool remains backward compatible:
```bash
# Still works exactly the same
./dsl2test.py my_dsl.yaml -o tests.json

# New: Can use configuration file
./dsl2test.py my_dsl.yaml --config my_config.json
```

## Migrating from Version 0.1.x to 0.2.x

### Breaking Changes

#### 1. Focus Parameter Behavior

The `focus` parameter in `test_requirements` now correctly handles attribute names with entity prefixes.

**Before (v0.1.x)**:
```yaml
# This would only generate 1 test due to naming mismatch
test_requirements:
  - name: Age tests
    type: boundary
    focus: [age]  # Would fail to find 'customer_age'
```

**After (v0.2.x)**:
```yaml
# Now works correctly
test_requirements:
  - name: Age tests
    type: boundary
    focus: [age]  # Correctly matches attributes named 'age' in any entity
```

### Recommended Migration Steps

#### Step 1: Review Your DSL Files

Check if you're using `focus` parameters in `test_requirements`:

```bash
grep -r "focus:" *.yaml
```

#### Step 2: Choose Migration Strategy

**Option A: Keep existing DSL (now it works!)**
```yaml
# Your existing DSL with focus should now generate more tests
test_requirements:
  - name: Customer tests
    type: boundary
    focus: [age, level]
```

**Option B: Simplify to single entity (recommended)**
```yaml
# Consolidate related attributes into one entity
entities:
  - name: Booking
    attributes:
      - name: customer_age
        type: integer
        min: 18
        max: 100
      - name: customer_level
        type: integer
        min: 1
        max: 3
```

**Option C: Remove test_requirements (simplest)**
```yaml
# Just remove test_requirements section
# The system will generate comprehensive tests automatically
```

#### Step 3: Test the Migration

Run your test generation and verify increased test count:

```python
from dsl_test_generator import DSLParser, DSLEngine

# Before migration
parser = DSLParser()
model = parser.parse_file("your_dsl.yaml")
engine = DSLEngine()
tests = engine.generate_tests(model)
print(f"Before: {len(tests)} tests")

# After migration (should be more tests)
# ... make changes ...
model2 = parser.parse_file("your_dsl_updated.yaml")
tests2 = engine.generate_tests(model2)
print(f"After: {len(tests2)} tests")
```

### New Features in v0.2.x

#### 1. Better Attribute Resolution
- Focus parameters now correctly resolve attributes across entities
- Full variable names (entity_attribute) are properly handled

#### 2. Enhanced Test Generation
- More comprehensive boundary tests
- Better equivalence class coverage
- Improved rule coverage tests

#### 3. Chinese Value Support
- Full support for Chinese values in constraints
- English keywords remain required

### Example: Complete Migration

**Original DSL (v0.1.x)**:
```yaml
domain: Hotel System

entities:
  - name: Customer
    attributes:
      - name: age
        type: integer
        min: 18
        max: 80
  - name: Room
    attributes:
      - name: price
        type: real
        min: 100
        max: 1000
  - name: Booking
    attributes:
      - name: days
        type: integer
        min: 1
        max: 30

constraints:
  - customer_age >= 18
  - room_price >= 100
  - booking_days >= 1

test_requirements:
  - name: Customer tests
    type: boundary
    focus: [age]  # Would only generate 1 test
  - name: Room tests
    type: boundary
    focus: [price]  # Would fail
```

**Migrated DSL (v0.2.x) - Option 1: Minimal Changes**:
```yaml
# Same DSL now works correctly and generates multiple tests!
# No changes needed - the fix handles the focus parameter properly
```

**Migrated DSL (v0.2.x) - Option 2: Optimized**:
```yaml
domain: Hotel System Optimized

entities:
  - name: HotelBooking
    attributes:
      - name: customer_age
        type: integer
        min: 18
        max: 80
      - name: room_price
        type: real
        min: 100.0
        max: 1000.0
      - name: booking_days
        type: integer
        min: 1
        max: 30
      - name: customer_level
        type: integer
        min: 1
        max: 3
        enum_values: [1, 2, 3]  # Added for more tests

constraints:
  - hotelbooking_customer_age >= 18
  - hotelbooking_room_price >= 100.0
  - hotelbooking_booking_days >= 1

rules:
  - name: VIP discount
    condition: hotelbooking_customer_level == 3
    implies: hotelbooking_room_price <= 800.0

# No test_requirements - use default strategy for maximum coverage
```

### Troubleshooting Migration Issues

#### Issue: Still getting only 1 test after upgrade

**Check**:
1. Ensure you're using the latest version
2. Verify attribute names in focus match actual attribute names
3. Try removing focus or test_requirements entirely

#### Issue: Different test names after migration

**Note**: Test names may change slightly due to improved naming logic. This is expected and doesn't affect test validity.

### Need Help?

- See `docs/TROUBLESHOOTING.md` for detailed debugging steps
- Check `demo/test_fix.py` for working examples
- Review `examples/` directory for best practices