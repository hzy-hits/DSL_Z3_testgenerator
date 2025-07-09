"""Type validators for DSL Test Generator."""

import re
from typing import Any, List, Set, Union

from .models import DSLType, ArrayType, SetType, Attribute


class TypeValidator:
    """Validate values against DSL types."""
    
    @staticmethod
    def validate(value: Any, attr: Attribute) -> bool:
        """Validate a value against an attribute's type and constraints."""
        if value is None:
            return attr.nullable
        
        # Handle collection types
        if attr.type == DSLType.ARRAY:
            return TypeValidator._validate_array(value, attr)
        elif attr.type == DSLType.SET:
            return TypeValidator._validate_set(value, attr)
        
        # Handle scalar types
        validators = {
            DSLType.INTEGER: TypeValidator._validate_integer,
            DSLType.REAL: TypeValidator._validate_real,
            DSLType.BOOLEAN: TypeValidator._validate_boolean,
            DSLType.STRING: TypeValidator._validate_string,
        }
        
        validator = validators.get(attr.type)
        if not validator:
            return False
        
        return validator(value, attr)
    
    @staticmethod
    def _validate_integer(value: Any, attr: Attribute) -> bool:
        """Validate integer value."""
        if not isinstance(value, int) or isinstance(value, bool):
            return False
        
        if attr.min_value is not None and value < attr.min_value:
            return False
        if attr.max_value is not None and value > attr.max_value:
            return False
        if attr.enum_values and value not in attr.enum_values:
            return False
        
        return True
    
    @staticmethod
    def _validate_real(value: Any, attr: Attribute) -> bool:
        """Validate real/float value."""
        if not isinstance(value, (int, float)) or isinstance(value, bool):
            return False
        
        if attr.min_value is not None and value < attr.min_value:
            return False
        if attr.max_value is not None and value > attr.max_value:
            return False
        if attr.enum_values and value not in attr.enum_values:
            return False
        
        return True
    
    @staticmethod
    def _validate_boolean(value: Any, attr: Attribute) -> bool:
        """Validate boolean value."""
        return isinstance(value, bool)
    
    @staticmethod
    def _validate_string(value: Any, attr: Attribute) -> bool:
        """Validate string value."""
        if not isinstance(value, str):
            return False
        
        if attr.pattern and not re.match(attr.pattern, value):
            return False
        if attr.enum_values and value not in attr.enum_values:
            return False
        
        return True
    
    @staticmethod
    def _validate_array(value: Any, attr: Attribute) -> bool:
        """Validate array value."""
        if not isinstance(value, list):
            return False
        
        if not attr.collection_info:
            return False
        
        array_info = attr.collection_info
        
        # Check size constraints
        if array_info.min_size is not None and len(value) < array_info.min_size:
            return False
        if array_info.max_size is not None and len(value) > array_info.max_size:
            return False
        
        # Validate each element
        element_attr = Attribute(
            name=f"{attr.name}_element",
            type=array_info.element_type,
            min_value=attr.min_value,
            max_value=attr.max_value,
            enum_values=attr.enum_values,
            pattern=attr.pattern
        )
        
        for elem in value:
            if not TypeValidator.validate(elem, element_attr):
                return False
        
        return True
    
    @staticmethod
    def _validate_set(value: Any, attr: Attribute) -> bool:
        """Validate set value."""
        if not isinstance(value, (set, list)):
            return False
        
        if not attr.collection_info:
            return False
        
        set_info = attr.collection_info
        
        # Convert to set to check uniqueness
        if isinstance(value, list):
            if len(value) != len(set(value)):
                return False  # Duplicates found
            value = set(value)
        
        # Check size constraints
        if set_info.min_size is not None and len(value) < set_info.min_size:
            return False
        if set_info.max_size is not None and len(value) > set_info.max_size:
            return False
        
        # Validate each element
        element_attr = Attribute(
            name=f"{attr.name}_element",
            type=set_info.element_type,
            min_value=attr.min_value,
            max_value=attr.max_value,
            enum_values=attr.enum_values,
            pattern=attr.pattern
        )
        
        for elem in value:
            if not TypeValidator.validate(elem, element_attr):
                return False
        
        return True