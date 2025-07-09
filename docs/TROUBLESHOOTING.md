# Troubleshooting Guide

## Common Issues and Solutions

### 1. Only One Test Case Generated

**Problem**: When running the test generator, only 1 test case is generated instead of multiple tests.

**Root Cause**: The `focus` parameter in `test_requirements` uses simple attribute names (e.g., `age`), but the Z3 solver uses fully qualified names (e.g., `customer_age`). This mismatch causes test generation to fail.

**Solutions**:

#### Solution 1: Remove focus parameter
```yaml
test_requirements:
  - name: All boundaries
    type: boundary
    # Don't specify focus - test all attributes
```

#### Solution 2: Use single entity design
```yaml
domain: Hotel System
entities:
  - name: Booking  # Put all attributes in one entity
    attributes:
      - name: customer_age
        type: integer
        min: 18
        max: 100
      - name: stay_days
        type: integer
        min: 1
        max: 30
```

#### Solution 3: Use default test generation
```yaml
# Don't specify test_requirements at all
# The system will automatically generate:
# - Boundary tests for all numeric attributes
# - Rule coverage tests for all rules
# - Equivalence tests for enum values
```

### 2. Z3 Parser Errors with Chinese Strings

**Problem**: Error `b'parser error'` when using Chinese strings in constraints.

**Root Cause**: Z3 solver cannot directly handle Unicode strings in constraints.

**Solution**: Use integer mappings for string enums:
```yaml
entities:
  - name: Student
    attributes:
      - name: status
        type: integer
        min: 1
        max: 3
        description: "1=在读, 2=休学, 3=毕业"
```

### 3. Complex Constraints Not Satisfiable

**Problem**: No test cases generated due to conflicting constraints.

**Debugging Steps**:

1. **Simplify constraints** - Remove constraints one by one to find conflicts
2. **Check rule implications** - Ensure rules don't create impossible conditions
3. **Use simpler types** - Start with integers before adding complex types

**Example of conflicting constraints**:
```yaml
# ❌ BAD: Conflicting constraints
constraints:
  - user_age >= 18
  - user_age <= 16  # Conflicts with above!
```

### 4. Installation Issues on macOS

**Problem**: `pip install` fails with "externally-managed-environment" error.

**Solution**: Use virtual environment:
```bash
# Create virtual environment
python3 -m venv venv
source venv/bin/activate

# Now install
pip install -e .
```

Or use uv:
```bash
brew install uv
uv pip install -e .
```

### 5. Module Import Errors

**Problem**: `ModuleNotFoundError` when running scripts.

**Solution**: Add the src directory to Python path:
```python
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))
```

## Best Practices for Maximum Test Generation

### 1. Design DSL for Testability

```yaml
domain: Testable System

entities:
  - name: Entity
    attributes:
      # Use clear min/max bounds
      - name: numeric_attr
        type: integer
        min: 1
        max: 100
        
      # Add enum_values for more tests
      - name: category
        type: integer
        min: 1
        max: 3
        enum_values: [1, 2, 3]
        
      # Boolean attributes are good for combinations
      - name: is_active
        type: boolean

# Keep constraints simple and non-conflicting
constraints:
  - entity_numeric_attr >= 1
  - entity_numeric_attr <= 100

# Add rules for more test variety
rules:
  - name: Category rule
    condition: entity_category == 2
    implies: entity_numeric_attr >= 50
```

### 2. Optimal Test Requirements

```yaml
# Option A: No test requirements (recommended)
# Let the system use its default strategy

# Option B: Broad test requirements without focus
test_requirements:
  - name: All boundaries
    type: boundary
    
  - name: All equivalence
    type: equivalence
    
  - name: Negative tests
    type: negative
```

### 3. Debugging Test Generation

Create a debug script:
```python
from dsl_test_generator import DSLParser, DSLEngine

# Parse DSL
parser = DSLParser()
model = parser.parse_file("your_dsl.yaml")

# Check what was parsed
print(f"Entities: {[e.name for e in model.entities]}")
print(f"Constraints: {len(model.constraints)}")
print(f"Rules: {len(model.rules)}")

# Generate tests
engine = DSLEngine()
tests = engine.generate_tests(model)

# Analyze results
print(f"Generated {len(tests)} tests")
for test in tests:
    print(f"  - {test['name']} ({test.get('type', 'unknown')})")
```

## Getting Help

If you encounter issues not covered here:

1. Check the examples in the `examples/` directory
2. Run the debug scripts in `demo/`
3. File an issue with:
   - Your DSL file
   - Expected vs actual output
   - Error messages (if any)