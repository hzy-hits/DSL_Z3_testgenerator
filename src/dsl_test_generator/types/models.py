"""Data models for DSL Test Generator with enhanced type support."""

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Union, Set
from enum import Enum


class DSLType(Enum):
    """Supported DSL types including collections."""
    
    INTEGER = "integer"
    REAL = "real"
    BOOLEAN = "boolean"
    STRING = "string"
    ARRAY = "array"
    SET = "set"
    
    @classmethod
    def from_string(cls, type_str: str) -> "DSLType":
        """Parse type string supporting array[T] and set[T] syntax."""
        type_str = type_str.lower().strip()
        
        if type_str.startswith("array[") and type_str.endswith("]"):
            return cls.ARRAY
        elif type_str.startswith("set[") and type_str.endswith("]"):
            return cls.SET
        
        type_map = {
            "integer": cls.INTEGER,
            "int": cls.INTEGER,
            "real": cls.REAL,
            "float": cls.REAL,
            "boolean": cls.BOOLEAN,
            "bool": cls.BOOLEAN,
            "string": cls.STRING,
            "str": cls.STRING,
        }
        
        if type_str in type_map:
            return type_map[type_str]
        raise ValueError(f"Unknown type: {type_str}")


@dataclass
class CollectionType:
    """Base class for collection types."""
    element_type: DSLType
    min_size: Optional[int] = None
    max_size: Optional[int] = None


@dataclass
class ArrayType(CollectionType):
    """Array type with element type and size constraints."""
    pass


@dataclass
class SetType(CollectionType):
    """Set type with element type and size constraints."""
    pass


@dataclass
class Attribute:
    """Enhanced attribute supporting arrays and sets."""
    
    name: str
    type: DSLType
    collection_info: Optional[Union[ArrayType, SetType]] = None
    min_value: Optional[Union[int, float]] = None
    max_value: Optional[Union[int, float]] = None
    enum_values: Optional[List[Any]] = None
    pattern: Optional[str] = None  # For string validation
    default: Optional[Any] = None
    nullable: bool = False
    
    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> "Attribute":
        """Create attribute from dictionary with collection support."""
        type_str = data.get("type", "string")
        dsl_type = DSLType.from_string(type_str)
        
        collection_info = None
        if dsl_type in (DSLType.ARRAY, DSLType.SET):
            # Extract element type from array[T] or set[T]
            start = type_str.index("[") + 1
            end = type_str.index("]")
            element_type_str = type_str[start:end]
            element_type = DSLType.from_string(element_type_str)
            
            CollectionClass = ArrayType if dsl_type == DSLType.ARRAY else SetType
            collection_info = CollectionClass(
                element_type=element_type,
                min_size=data.get("min_size"),
                max_size=data.get("max_size")
            )
        
        return cls(
            name=data["name"],
            type=dsl_type,
            collection_info=collection_info,
            min_value=data.get("min"),
            max_value=data.get("max"),
            enum_values=data.get("enum"),
            pattern=data.get("pattern"),
            default=data.get("default"),
            nullable=data.get("nullable", False)
        )


@dataclass
class Entity:
    """Entity with enhanced attributes."""
    
    name: str
    attributes: List[Attribute]
    
    def get_attribute(self, name: str) -> Optional[Attribute]:
        """Get attribute by name."""
        for attr in self.attributes:
            if attr.name == name:
                return attr
        return None


@dataclass
class Constraint:
    """Constraint supporting collection operations."""
    
    expression: str
    description: Optional[str] = None
    
    def involves_collections(self) -> bool:
        """Check if constraint involves array/set operations."""
        collection_ops = ["in", "contains", "size", "length", "count", "subset", "union", "intersection"]
        return any(op in self.expression.lower() for op in collection_ops)


@dataclass
class Rule:
    """Business rule with support for collection conditions."""
    
    name: str
    condition: str
    action: Optional[str] = None
    implies: Optional[str] = None
    description: Optional[str] = None
    priority: int = 0
    
    def __post_init__(self):
        if not self.action and not self.implies:
            raise ValueError(f"Rule '{self.name}' must have either 'action' or 'implies'")


@dataclass
class TestRequirement:
    """Test requirement with collection test support."""
    
    name: str
    type: str  # boundary, equivalence, negative, collection, etc.
    focus: Optional[List[str]] = None
    combinations: Optional[int] = None
    collection_tests: Optional[List[str]] = None  # empty, single, multiple, duplicates, etc.


@dataclass
class DSLModel:
    """Complete DSL model with enhanced type support."""
    
    domain: str
    entities: List[Entity] = field(default_factory=list)
    constraints: List[Constraint] = field(default_factory=list)
    rules: List[Rule] = field(default_factory=list)
    test_requirements: List[TestRequirement] = field(default_factory=list)
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    def get_entity(self, name: str) -> Optional[Entity]:
        """Get entity by name."""
        for entity in self.entities:
            if entity.name == name:
                return entity
        return None
    
    def get_all_attributes(self) -> List[Attribute]:
        """Get all attributes from all entities."""
        attributes = []
        for entity in self.entities:
            attributes.extend(entity.attributes)
        return attributes
    
    def get_collection_attributes(self) -> List[Attribute]:
        """Get all array and set attributes."""
        return [
            attr for attr in self.get_all_attributes()
            if attr.type in (DSLType.ARRAY, DSLType.SET)
        ]