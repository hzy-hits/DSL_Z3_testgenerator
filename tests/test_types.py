"""Test the type system."""

import pytest
from dsl_test_generator.types import (
    DSLType, Attribute, Entity, ArrayType, SetType, TypeValidator
)


class TestDSLType:
    """Test DSLType enum and parsing."""
    
    def test_scalar_types(self):
        assert DSLType.from_string("integer") == DSLType.INTEGER
        assert DSLType.from_string("real") == DSLType.REAL
        assert DSLType.from_string("boolean") == DSLType.BOOLEAN
        assert DSLType.from_string("string") == DSLType.STRING
    
    def test_type_aliases(self):
        assert DSLType.from_string("int") == DSLType.INTEGER
        assert DSLType.from_string("float") == DSLType.REAL
        assert DSLType.from_string("bool") == DSLType.BOOLEAN
        assert DSLType.from_string("str") == DSLType.STRING
    
    def test_collection_types(self):
        assert DSLType.from_string("array[integer]") == DSLType.ARRAY
        assert DSLType.from_string("set[string]") == DSLType.SET
        assert DSLType.from_string("array[real]") == DSLType.ARRAY
    
    def test_invalid_type(self):
        with pytest.raises(ValueError):
            DSLType.from_string("invalid")


class TestAttribute:
    """Test Attribute creation and parsing."""
    
    def test_scalar_attribute(self):
        data = {
            "name": "age",
            "type": "integer",
            "min": 0,
            "max": 150
        }
        attr = Attribute.from_dict(data)
        
        assert attr.name == "age"
        assert attr.type == DSLType.INTEGER
        assert attr.min_value == 0
        assert attr.max_value == 150
        assert attr.collection_info is None
    
    def test_array_attribute(self):
        data = {
            "name": "scores",
            "type": "array[real]",
            "min_size": 0,
            "max_size": 10
        }
        attr = Attribute.from_dict(data)
        
        assert attr.name == "scores"
        assert attr.type == DSLType.ARRAY
        assert isinstance(attr.collection_info, ArrayType)
        assert attr.collection_info.element_type == DSLType.REAL
        assert attr.collection_info.min_size == 0
        assert attr.collection_info.max_size == 10
    
    def test_set_attribute(self):
        data = {
            "name": "tags",
            "type": "set[string]",
            "min_size": 1,
            "max_size": 5
        }
        attr = Attribute.from_dict(data)
        
        assert attr.name == "tags"
        assert attr.type == DSLType.SET
        assert isinstance(attr.collection_info, SetType)
        assert attr.collection_info.element_type == DSLType.STRING
        assert attr.collection_info.min_size == 1
        assert attr.collection_info.max_size == 5
    
    def test_enum_attribute(self):
        data = {
            "name": "status",
            "type": "string",
            "enum": ["active", "inactive", "pending"]
        }
        attr = Attribute.from_dict(data)
        
        assert attr.enum_values == ["active", "inactive", "pending"]


class TestTypeValidator:
    """Test TypeValidator functionality."""
    
    def test_validate_integer(self):
        attr = Attribute(
            name="age",
            type=DSLType.INTEGER,
            min_value=0,
            max_value=150
        )
        
        assert TypeValidator.validate(25, attr) is True
        assert TypeValidator.validate(0, attr) is True
        assert TypeValidator.validate(150, attr) is True
        assert TypeValidator.validate(-1, attr) is False
        assert TypeValidator.validate(151, attr) is False
        assert TypeValidator.validate(25.5, attr) is False
        assert TypeValidator.validate("25", attr) is False
    
    def test_validate_string_with_pattern(self):
        attr = Attribute(
            name="email",
            type=DSLType.STRING,
            pattern=r"^[a-zA-Z0-9]+@[a-zA-Z0-9]+\.[a-zA-Z]+$"
        )
        
        assert TypeValidator.validate("user@example.com", attr) is True
        assert TypeValidator.validate("invalid-email", attr) is False
    
    def test_validate_array(self):
        attr = Attribute(
            name="scores",
            type=DSLType.ARRAY,
            collection_info=ArrayType(
                element_type=DSLType.INTEGER,
                min_size=1,
                max_size=5
            ),
            min_value=0,
            max_value=100
        )
        
        assert TypeValidator.validate([50, 75, 90], attr) is True
        assert TypeValidator.validate([], attr) is False  # Too small
        assert TypeValidator.validate([1, 2, 3, 4, 5, 6], attr) is False  # Too large
        assert TypeValidator.validate([50, 75, 150], attr) is False  # Element too large
        assert TypeValidator.validate([50, "75", 90], attr) is False  # Wrong type
    
    def test_validate_set(self):
        attr = Attribute(
            name="tags",
            type=DSLType.SET,
            collection_info=SetType(
                element_type=DSLType.STRING,
                min_size=1,
                max_size=3
            )
        )
        
        assert TypeValidator.validate({"tag1", "tag2"}, attr) is True
        assert TypeValidator.validate(["tag1", "tag2"], attr) is True  # List is converted
        assert TypeValidator.validate(set(), attr) is False  # Too small
        assert TypeValidator.validate(["tag1", "tag1"], attr) is False  # Duplicates
    
    def test_validate_nullable(self):
        attr = Attribute(
            name="optional",
            type=DSLType.STRING,
            nullable=True
        )
        
        assert TypeValidator.validate(None, attr) is True
        assert TypeValidator.validate("value", attr) is True
        
        attr.nullable = False
        assert TypeValidator.validate(None, attr) is False