# DSL Test Generator API Reference

## Table of Contents

1. [Core Classes](#core-classes)
2. [Parser Classes](#parser-classes)
3. [Type System](#type-system)
4. [Configuration](#configuration)
5. [Validators](#validators)
6. [Examples](#examples)

## Core Classes

### DSLEngine

The main engine for DSL-based test generation.

```python
from dsl_test_generator import DSLEngine, DSLEngineConfig

class DSLEngine:
    def __init__(self, config: Optional[DSLEngineConfig] = None)
    def generate_tests(self, model: DSLModel) -> List[Dict[str, Any]]
```

#### Parameters

- `config` (Optional[DSLEngineConfig]): Configuration object for customizing engine behavior

#### Methods

##### `generate_tests(model: DSLModel) -> List[Dict[str, Any]]`

Generates comprehensive test cases from a DSL model.

**Parameters:**
- `model` (DSLModel): The parsed DSL model

**Returns:**
- List of test cases, each containing:
  - `name`: Test case name
  - `description`: Test description
  - `values`: Dictionary of test data
  - `expected`: Expected result ('pass' or 'fail')
  - `type`: Test type (boundary, negative, etc.)

**Example:**
```python
engine = DSLEngine()
test_cases = engine.generate_tests(model)
```

### EnhancedDSLEngine

Enhanced engine with smart test generation and business logic validation.

```python
from dsl_test_generator.core import EnhancedDSLEngine

class EnhancedDSLEngine(DSLEngine):
    def __init__(self, config: Optional[DSLEngineConfig] = None)
    def generate_tests_with_extended_ranges(self, model: DSLModel) -> List[Dict[str, Any]]
```

#### Additional Methods

##### `generate_tests_with_extended_ranges(model: DSLModel) -> List[Dict[str, Any]]`

Generates tests with temporarily extended attribute ranges for more comprehensive negative testing.

## Parser Classes

### DSLParser

Parses DSL files and validates the model structure.

```python
from dsl_test_generator import DSLParser

class DSLParser:
    def __init__(self)
    def parse_file(self, file_path: str) -> DSLModel
    def parse_dict(self, data: Dict[str, Any]) -> DSLModel
    
    @property
    def errors(self) -> List[str]
    @property
    def warnings(self) -> List[str]
```

#### Methods

##### `parse_file(file_path: str) -> DSLModel`

Parses a YAML DSL file.

**Parameters:**
- `file_path`: Path to the YAML file

**Returns:**
- DSLModel object

**Raises:**
- `ValueError`: If parsing fails or validation errors occur

**Example:**
```python
parser = DSLParser()
try:
    model = parser.parse_file("hotel_booking.yaml")
except ValueError as e:
    print(f"Parsing error: {e}")
    print(f"Errors: {parser.errors}")
    print(f"Warnings: {parser.warnings}")
```

##### `parse_dict(data: Dict[str, Any]) -> DSLModel`

Parses a dictionary representation of the DSL.

## Type System

### DSLModel

The main model class representing a complete DSL specification.

```python
@dataclass
class DSLModel:
    domain: str
    entities: List[Entity]
    constraints: List[Constraint] = field(default_factory=list)
    rules: List[Rule] = field(default_factory=list)
    test_requirements: List[TestRequirement] = field(default_factory=list)
    
    def get_all_attributes(self) -> List[Attribute]
    def get_collection_attributes(self) -> List[Attribute]
```

### Entity

Represents a business entity with attributes.

```python
@dataclass
class Entity:
    name: str
    attributes: List[Attribute]
    
    def get_attribute(self, name: str) -> Optional[Attribute]
```

### Attribute

Represents an entity attribute with type and constraints.

```python
@dataclass
class Attribute:
    name: str
    type: DSLType
    collection_info: Optional[Union[ArrayType, SetType]] = None
    min_value: Optional[Union[int, float]] = None
    max_value: Optional[Union[int, float]] = None
    enum_values: Optional[List[Any]] = None
    pattern: Optional[str] = None
    default: Optional[Any] = None
    nullable: bool = False
```

### DSLType

Enumeration of supported data types.

```python
class DSLType(Enum):
    INTEGER = "integer"
    REAL = "real"
    BOOLEAN = "boolean"
    STRING = "string"
    ARRAY = "array"
    SET = "set"
    
    @classmethod
    def from_string(cls, type_str: str) -> "DSLType"
```

### Constraint

Represents a system constraint.

```python
@dataclass
class Constraint:
    expression: str
    description: Optional[str] = None
    
    def involves_collections(self) -> bool
```

### Rule

Represents a business rule.

```python
@dataclass
class Rule:
    name: str
    condition: str
    action: Optional[str] = None
    implies: Optional[str] = None
    description: Optional[str] = None
    priority: int = 0
```

## Configuration

### DSLEngineConfig

Main configuration class for the DSL engine.

```python
from dsl_test_generator import DSLEngineConfig, default_config

@dataclass
class DSLEngineConfig:
    test_generation: TestGenerationConfig
    solver: SolverConfig
    operators: OperatorConfig
    
    @classmethod
    def from_dict(cls, config_dict: Dict) -> 'DSLEngineConfig'
    def to_dict(self) -> Dict
```

### TestGenerationConfig

Configuration for test generation behavior.

```python
@dataclass
class TestGenerationConfig:
    test_types: List[str]  # ["boundary", "equivalence", "negative", ...]
    collection_test_scenarios: List[str]  # ["empty", "single", "multiple", ...]
    decimal_precision: int = 6
    negative_test_integer_extension: int = 1
    negative_test_real_extension: float = 1.0
    set_domain_check_limit: int = 100
    array_membership_check_limit: int = 10
    string_hash_modulo: int = 1000000
    validate_business_logic: bool = True
    cross_entity_validation: bool = True
```

### SolverConfig

Configuration for Z3 solver.

```python
@dataclass
class SolverConfig:
    timeout: Optional[int] = 5000  # milliseconds
    random_seed: Optional[int] = None
    enable_optimization: bool = True
    use_simplification: bool = True
```

### Configuration Example

```python
# Create custom configuration
config = DSLEngineConfig()
config.test_generation.decimal_precision = 2
config.test_generation.validate_business_logic = True
config.solver.timeout = 10000  # 10 seconds

# Use with engine
engine = EnhancedDSLEngine(config)

# Or load from dictionary
config_dict = {
    'test_generation': {
        'decimal_precision': 2,
        'validate_business_logic': True,
        'negative_test_integer_extension': 2
    },
    'solver': {
        'timeout': 10000
    }
}
config = DSLEngineConfig.from_dict(config_dict)
```

## Validators

### BusinessLogicValidator

Validates and corrects test data to ensure business logic consistency.

```python
from dsl_test_generator.validators import BusinessLogicValidator

class BusinessLogicValidator:
    def __init__(self, model: DSLModel, config: Optional[DSLEngineConfig] = None)
    def validate_and_fix_test_case(self, test_data: Dict[str, Any]) -> Dict[str, Any]
    def validate_test_suite(self, test_cases: List[Dict[str, Any]]) -> List[Dict[str, Any]]
```

#### Methods

##### `validate_and_fix_test_case(test_data: Dict[str, Any]) -> Dict[str, Any]`

Validates and fixes a single test case to ensure business logic consistency.

**Features:**
- Enforces cross-entity equality constraints (e.g., claim_type == policy_type)
- Fixes dependent attribute relationships
- Applies domain-specific business logic corrections
- Ensures realistic test data values

##### `validate_test_suite(test_cases: List[Dict[str, Any]]) -> List[Dict[str, Any]]`

Validates and fixes an entire test suite.

## Examples

### Basic Usage

```python
from dsl_test_generator import DSLParser, DSLEngine

# Parse DSL file
parser = DSLParser()
model = parser.parse_file("insurance_claim.yaml")

# Generate tests with default configuration
engine = DSLEngine()
test_cases = engine.generate_tests(model)

# Save to file
import json
with open("tests.json", "w") as f:
    json.dump(test_cases, f, indent=2)
```

### Advanced Usage with Configuration

```python
from dsl_test_generator import DSLParser, EnhancedDSLEngine, DSLEngineConfig

# Create custom configuration
config = DSLEngineConfig()
config.test_generation.validate_business_logic = True
config.test_generation.decimal_precision = 2
config.solver.timeout = 30000  # 30 seconds

# Parse and generate tests
parser = DSLParser()
model = parser.parse_file("complex_system.yaml")

engine = EnhancedDSLEngine(config)
test_cases = engine.generate_tests(model)

# Group tests by type
tests_by_type = {}
for test in test_cases:
    test_type = test.get('type', 'unknown')
    if test_type not in tests_by_type:
        tests_by_type[test_type] = []
    tests_by_type[test_type].append(test)

print(f"Generated {len(test_cases)} total tests:")
for test_type, tests in tests_by_type.items():
    print(f"  {test_type}: {len(tests)} tests")
```

### Programmatic DSL Creation

```python
from dsl_test_generator.types import (
    DSLModel, Entity, Attribute, DSLType, 
    Constraint, Rule, TestRequirement
)

# Create model programmatically
model = DSLModel(
    domain="Custom System",
    entities=[
        Entity(
            name="User",
            attributes=[
                Attribute(
                    name="age",
                    type=DSLType.INTEGER,
                    min_value=0,
                    max_value=120
                ),
                Attribute(
                    name="is_active",
                    type=DSLType.BOOLEAN
                )
            ]
        )
    ],
    constraints=[
        Constraint(expression="user_age >= 18", description="Adults only")
    ],
    rules=[
        Rule(
            name="Senior Benefits",
            condition="user_age >= 65",
            implies="user_has_benefits == true"
        )
    ]
)

# Generate tests
engine = DSLEngine()
test_cases = engine.generate_tests(model)
```

### Custom Validation

```python
from dsl_test_generator.validators import BusinessLogicValidator

# Parse model
parser = DSLParser()
model = parser.parse_file("business_system.yaml")

# Generate tests
engine = DSLEngine()
test_cases = engine.generate_tests(model)

# Apply custom validation
validator = BusinessLogicValidator(model)
validated_tests = validator.validate_test_suite(test_cases)

# Check what was fixed
for i, (original, validated) in enumerate(zip(test_cases, validated_tests)):
    if original['values'] != validated['values']:
        print(f"Test {i} was modified:")
        for key in original['values']:
            if original['values'][key] != validated['values'][key]:
                print(f"  {key}: {original['values'][key]} -> {validated['values'][key]}")
```

## Error Handling

The API uses exceptions and error collections for error handling:

```python
try:
    parser = DSLParser()
    model = parser.parse_file("invalid.yaml")
except ValueError as e:
    print(f"Parsing failed: {e}")
    
    # Detailed error information
    for error in parser.errors:
        print(f"ERROR: {error}")
    
    for warning in parser.warnings:
        print(f"WARNING: {warning}")
```

## Thread Safety

The DSL Test Generator is not thread-safe by default. If you need to use it in a multi-threaded environment:

1. Create separate instances for each thread
2. Use thread-local storage
3. Implement your own synchronization

```python
import threading

# Thread-local storage for parser and engine
thread_local = threading.local()

def get_engine():
    if not hasattr(thread_local, 'engine'):
        thread_local.engine = DSLEngine()
    return thread_local.engine

def generate_tests_for_file(file_path):
    parser = DSLParser()
    model = parser.parse_file(file_path)
    
    engine = get_engine()
    return engine.generate_tests(model)
```

## Performance Considerations

1. **Z3 Solver Timeout**: Set appropriate timeout values for complex models
2. **Test Case Limits**: Use `max_test_cases_per_type` to limit generation
3. **Collection Sizes**: Large collection limits can slow down constraint solving
4. **Business Logic Validation**: Can be disabled for better performance

```python
# Performance-optimized configuration
config = DSLEngineConfig()
config.test_generation.validate_business_logic = False  # Faster but less accurate
config.test_generation.max_test_cases_per_type = 50    # Limit test cases
config.solver.timeout = 2000                            # 2 second timeout
config.solver.enable_optimization = False               # Disable solver optimization
```