"""
Core data models for V2.0 DSL Test Generator

This module defines the fundamental data structures used throughout the system.
No business logic, just pure data models.
"""

from dataclasses import dataclass, field
from typing import List, Dict, Any, Optional, Set
from enum import Enum


class AttributeType(Enum):
    """Supported attribute types"""
    INTEGER = "integer"
    REAL = "real"
    BOOLEAN = "boolean"
    STRING = "string"
    DATE = "date"
    ENUM = "enum"
    ARRAY = "array"
    SET = "set"


class ConstraintType(Enum):
    """Types of constraints"""
    RANGE = "range"
    PATTERN = "pattern"
    RELATION = "relation"
    IMPLICATION = "implication"
    COLLECTION = "collection"
    ENUM = "enum"


@dataclass
class Attribute:
    """Attribute definition with full context"""
    name: str
    entity_name: str
    type: AttributeType
    min_value: Optional[float] = None
    max_value: Optional[float] = None
    enum_values: Optional[List[Any]] = None
    pattern: Optional[str] = None
    nullable: bool = False
    
    @property
    def full_name(self) -> str:
        """Get fully qualified name"""
        return f"{self.entity_name.lower()}_{self.name}"
    
    def __post_init__(self):
        """Validate attribute definition"""
        if self.type == AttributeType.ENUM and not self.enum_values:
            raise ValueError(f"Enum attribute {self.name} must have enum_values")
        if self.type in [AttributeType.INTEGER, AttributeType.REAL]:
            if self.min_value is not None and self.max_value is not None:
                if self.min_value > self.max_value:
                    raise ValueError(f"min_value ({self.min_value}) > max_value ({self.max_value})")


@dataclass
class Entity:
    """Entity definition"""
    name: str
    attributes: List[Attribute] = field(default_factory=list)
    
    def __post_init__(self):
        """Set entity reference in attributes"""
        for attr in self.attributes:
            attr.entity_name = self.name
    
    def get_attribute(self, name: str) -> Optional[Attribute]:
        """Get attribute by name"""
        for attr in self.attributes:
            if attr.name == name:
                return attr
        return None


@dataclass
class Constraint:
    """Constraint definition"""
    expression: str
    type: ConstraintType
    description: Optional[str] = None
    attributes: List[str] = field(default_factory=list)  # Involved attributes
    
    def __post_init__(self):
        """Extract attributes from expression if not provided"""
        if not self.attributes:
            # Simple extraction - real implementation would use proper parsing
            import re
            # Match attribute names (entity_attribute pattern)
            pattern = r'\b[a-z]+_[a-z_]+\b'
            self.attributes = list(set(re.findall(pattern, self.expression)))


@dataclass
class Rule:
    """Business rule with condition and consequence"""
    name: str
    condition: str
    consequence: str
    priority: int = 1
    description: Optional[str] = None
    
    def __post_init__(self):
        """Validate rule structure"""
        if not self.condition:
            raise ValueError(f"Rule {self.name} must have a condition")
        if not self.consequence:
            raise ValueError(f"Rule {self.name} must have a consequence")


@dataclass
class TestHint:
    """User-provided test hint"""
    type: str  # "focus", "ignore", "combine"
    target: List[str]  # Attributes or rules to focus on
    reason: Optional[str] = None


@dataclass
class DSLModel:
    """Complete DSL model"""
    domain: str
    entities: List[Entity]
    constraints: List[Constraint] = field(default_factory=list)
    rules: List[Rule] = field(default_factory=list)
    test_hints: List[TestHint] = field(default_factory=list)
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    def get_all_attributes(self) -> List[Attribute]:
        """Get all attributes from all entities"""
        attributes = []
        for entity in self.entities:
            attributes.extend(entity.attributes)
        return attributes
    
    def get_attribute_by_full_name(self, full_name: str) -> Optional[Attribute]:
        """Get attribute by its full name"""
        for attr in self.get_all_attributes():
            if attr.full_name == full_name:
                return attr
        return None
    
    def get_rule_by_name(self, name: str) -> Optional[Rule]:
        """Get rule by name"""
        for rule in self.rules:
            if rule.name == name:
                return rule
        return None
    
    def validate(self) -> List[str]:
        """Validate model consistency"""
        errors = []
        
        # Check attribute uniqueness
        attr_names = set()
        for attr in self.get_all_attributes():
            if attr.full_name in attr_names:
                errors.append(f"Duplicate attribute: {attr.full_name}")
            attr_names.add(attr.full_name)
        
        # Check constraint references
        for constraint in self.constraints:
            for attr_name in constraint.attributes:
                if attr_name not in attr_names:
                    errors.append(f"Constraint references unknown attribute: {attr_name}")
        
        # Check rule references
        for rule in self.rules:
            # Simple check - real implementation would parse expressions
            for attr_name in attr_names:
                if attr_name in rule.condition or attr_name in rule.consequence:
                    # Attribute is referenced, good
                    pass
        
        return errors


# Test Generation Models

@dataclass
class TestObjective:
    """What we want to test and why"""
    type: str  # boundary_min, boundary_max, rule_active, rule_inactive, equivalence, negative
    target: str  # attribute name or rule name
    priority: int
    reason: str
    constraints: List[str] = field(default_factory=list)  # Additional constraints
    
    def __hash__(self):
        """Make objective hashable for deduplication"""
        return hash((self.type, self.target))


@dataclass
class TestCase:
    """A single test case with metadata"""
    name: str
    objective: TestObjective
    values: Dict[str, Any]
    expected: str = "pass"
    coverage: Set[str] = field(default_factory=set)  # What this test covers
    validation_errors: List[str] = field(default_factory=list)
    
    def is_valid(self) -> bool:
        """Check if test case is valid"""
        return len(self.validation_errors) == 0
    
    def add_coverage(self, item: str):
        """Add coverage information"""
        self.coverage.add(item)


@dataclass
class TestPlan:
    """Complete test plan"""
    objectives: List[TestObjective]
    coverage_goals: Dict[str, float] = field(default_factory=dict)
    max_tests: Optional[int] = None
    
    def __post_init__(self):
        """Set default coverage goals"""
        if not self.coverage_goals:
            self.coverage_goals = {
                'constraint': 1.0,  # 100% constraint coverage
                'rule': 1.0,        # 100% rule coverage
                'boundary': 0.9,    # 90% boundary coverage
                'equivalence': 0.8  # 80% equivalence coverage
            }


@dataclass
class CoverageReport:
    """Test coverage analysis"""
    total_constraints: int = 0
    covered_constraints: int = 0
    total_rules: int = 0
    covered_rules: int = 0
    total_boundaries: int = 0
    covered_boundaries: int = 0
    coverage_matrix: Dict[str, Set[str]] = field(default_factory=dict)
    
    @property
    def constraint_coverage(self) -> float:
        """Calculate constraint coverage percentage"""
        if self.total_constraints == 0:
            return 1.0
        return self.covered_constraints / self.total_constraints
    
    @property
    def rule_coverage(self) -> float:
        """Calculate rule coverage percentage"""
        if self.total_rules == 0:
            return 1.0
        return self.covered_rules / self.total_rules
    
    @property
    def boundary_coverage(self) -> float:
        """Calculate boundary coverage percentage"""
        if self.total_boundaries == 0:
            return 1.0
        return self.covered_boundaries / self.total_boundaries
    
    def add_test_coverage(self, test: TestCase):
        """Add coverage from a test case"""
        if test.name not in self.coverage_matrix:
            self.coverage_matrix[test.name] = set()
        self.coverage_matrix[test.name].update(test.coverage)