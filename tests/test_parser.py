"""Test DSL parser functionality."""

import pytest
from dsl_test_generator.parsers import DSLParser
from dsl_test_generator.types import DSLType, DSLModel


class TestDSLParser:
    """Test DSL parsing functionality."""
    
    def test_parse_simple_dsl(self):
        dsl_data = {
            "domain": "Test System",
            "entities": [
                {
                    "name": "User",
                    "attributes": [
                        {"name": "age", "type": "integer", "min": 0, "max": 150},
                        {"name": "name", "type": "string"}
                    ]
                }
            ],
            "constraints": ["user_age >= 18"],
            "rules": [
                {
                    "name": "Adult rule",
                    "condition": "user_age >= 18",
                    "implies": "user_name != null"
                }
            ]
        }
        
        parser = DSLParser()
        model = parser.parse_dict(dsl_data)
        
        assert model.domain == "Test System"
        assert len(model.entities) == 1
        assert model.entities[0].name == "User"
        assert len(model.entities[0].attributes) == 2
        assert len(model.constraints) == 1
        assert len(model.rules) == 1
    
    def test_parse_collection_types(self):
        dsl_data = {
            "domain": "Collection Test",
            "entities": [
                {
                    "name": "Cart",
                    "attributes": [
                        {
                            "name": "items",
                            "type": "array[integer]",
                            "min_size": 0,
                            "max_size": 50
                        },
                        {
                            "name": "tags",
                            "type": "set[string]",
                            "max_size": 10
                        }
                    ]
                }
            ]
        }
        
        parser = DSLParser()
        model = parser.parse_dict(dsl_data)
        
        cart = model.entities[0]
        items_attr = cart.attributes[0]
        tags_attr = cart.attributes[1]
        
        assert items_attr.type == DSLType.ARRAY
        assert items_attr.collection_info.element_type == DSLType.INTEGER
        assert items_attr.collection_info.max_size == 50
        
        assert tags_attr.type == DSLType.SET
        assert tags_attr.collection_info.element_type == DSLType.STRING
        assert tags_attr.collection_info.max_size == 10
    
    def test_parse_complex_constraints(self):
        dsl_data = {
            "domain": "Complex Constraints",
            "entities": [
                {
                    "name": "Order",
                    "attributes": [
                        {"name": "total", "type": "real"},
                        {"name": "items", "type": "array[integer]"},
                        {"name": "discounts", "type": "set[string]"}
                    ]
                }
            ],
            "constraints": [
                "order_total >= 0",
                "size(order_items) >= 1",
                '"BULK" in order_discounts -> order_total >= 100'
            ]
        }
        
        parser = DSLParser()
        model = parser.parse_dict(dsl_data)
        
        assert len(model.constraints) == 3
        assert "size(order_items)" in model.constraints[1].expression
        assert "->" in model.constraints[2].expression
    
    def test_parse_test_requirements(self):
        dsl_data = {
            "domain": "Test Requirements",
            "entities": [],
            "test_requirements": [
                {
                    "name": "Boundary tests",
                    "type": "boundary",
                    "focus": ["age", "price"]
                },
                {
                    "name": "Collection tests",
                    "type": "collection",
                    "collection_tests": ["empty", "single", "multiple"]
                }
            ]
        }
        
        parser = DSLParser()
        model = parser.parse_dict(dsl_data)
        
        assert len(model.test_requirements) == 2
        assert model.test_requirements[0].type == "boundary"
        assert model.test_requirements[0].focus == ["age", "price"]
        assert model.test_requirements[1].collection_tests == ["empty", "single", "multiple"]
    
    def test_parse_invalid_rule(self):
        dsl_data = {
            "domain": "Invalid Rule",
            "entities": [],
            "rules": [
                {
                    "name": "Bad rule",
                    "condition": "x > 0"
                    # Missing both 'action' and 'implies'
                }
            ]
        }
        
        parser = DSLParser()
        with pytest.raises(ValueError, match="must have either 'action' or 'implies'"):
            parser.parse_dict(dsl_data)
    
    def test_parse_duplicate_entities(self):
        dsl_data = {
            "domain": "Duplicate Test",
            "entities": [
                {"name": "User", "attributes": []},
                {"name": "User", "attributes": []}  # Duplicate
            ]
        }
        
        parser = DSLParser()
        with pytest.raises(ValueError, match="Duplicate entity names"):
            parser.parse_dict(dsl_data)
    
    def test_parse_metadata(self):
        dsl_data = {
            "domain": "Metadata Test",
            "metadata": {
                "version": "1.0",
                "author": "Test Author",
                "tags": ["test", "example"]
            },
            "entities": []
        }
        
        parser = DSLParser()
        model = parser.parse_dict(dsl_data)
        
        assert model.metadata["version"] == "1.0"
        assert model.metadata["author"] == "Test Author"
        assert "test" in model.metadata["tags"]