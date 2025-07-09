"""Enhanced DSL parser with collection support."""

from typing import Any, Dict, List, Union
import yaml

from ..types import (
    DSLModel,
    Entity,
    Attribute,
    Constraint,
    Rule,
    TestRequirement,
)


class DSLParser:
    """Parse DSL specifications with enhanced type support."""
    
    def __init__(self):
        self.errors: List[str] = []
        self.warnings: List[str] = []
    
    def parse_file(self, file_path: str) -> DSLModel:
        """Parse DSL from file."""
        with open(file_path, 'r', encoding='utf-8') as f:
            if file_path.endswith('.yaml') or file_path.endswith('.yml'):
                data = yaml.safe_load(f)
            else:
                raise ValueError(f"Unsupported file format: {file_path}")
        
        return self.parse_dict(data)
    
    def parse_dict(self, data: Dict[str, Any]) -> DSLModel:
        """Parse DSL from dictionary."""
        self.errors = []
        self.warnings = []
        
        model = DSLModel(domain=data.get('domain', 'Unknown Domain'))
        
        # Parse metadata
        if 'metadata' in data:
            model.metadata = data['metadata']
        
        # Parse entities
        if 'entities' in data:
            for entity_data in data['entities']:
                entity = self._parse_entity(entity_data)
                model.entities.append(entity)
        
        # Parse constraints
        if 'constraints' in data:
            for constraint in data['constraints']:
                if isinstance(constraint, str):
                    model.constraints.append(Constraint(expression=constraint))
                elif isinstance(constraint, dict):
                    model.constraints.append(
                        Constraint(
                            expression=constraint['expression'],
                            description=constraint.get('description')
                        )
                    )
        
        # Parse rules
        if 'rules' in data:
            for rule_data in data['rules']:
                rule = self._parse_rule(rule_data)
                model.rules.append(rule)
        
        # Parse test requirements
        if 'test_requirements' in data:
            for req_data in data['test_requirements']:
                req = self._parse_test_requirement(req_data)
                model.test_requirements.append(req)
        
        # Validate the model
        self._validate_model(model)
        
        if self.errors:
            raise ValueError(f"DSL parsing errors: {'; '.join(self.errors)}")
        
        return model
    
    def _parse_entity(self, data: Dict[str, Any]) -> Entity:
        """Parse entity with enhanced attribute support."""
        attributes = []
        
        for attr_data in data.get('attributes', []):
            try:
                attr = Attribute.from_dict(attr_data)
                attributes.append(attr)
            except Exception as e:
                self.errors.append(f"Failed to parse attribute {attr_data}: {e}")
        
        return Entity(
            name=data['name'],
            attributes=attributes
        )
    
    def _parse_rule(self, data: Dict[str, Any]) -> Rule:
        """Parse rule."""
        return Rule(
            name=data['name'],
            condition=data['condition'],
            action=data.get('action'),
            implies=data.get('implies'),
            description=data.get('description'),
            priority=data.get('priority', 0)
        )
    
    def _parse_test_requirement(self, data: Dict[str, Any]) -> TestRequirement:
        """Parse test requirement with collection test support."""
        return TestRequirement(
            name=data['name'],
            type=data['type'],
            focus=data.get('focus'),
            combinations=data.get('combinations'),
            collection_tests=data.get('collection_tests')
        )
    
    def _validate_model(self, model: DSLModel):
        """Validate the parsed model."""
        # Check for duplicate entity names
        entity_names = [e.name for e in model.entities]
        if len(entity_names) != len(set(entity_names)):
            self.errors.append("Duplicate entity names found")
        
        # Check for duplicate attribute names within entities
        for entity in model.entities:
            attr_names = [a.name for a in entity.attributes]
            if len(attr_names) != len(set(attr_names)):
                self.errors.append(f"Duplicate attribute names in entity {entity.name}")
        
        # Validate references in constraints and rules
        all_attributes = model.get_all_attributes()
        attr_names = {attr.name for attr in all_attributes}
        
        # Add entity-prefixed names
        for entity in model.entities:
            for attr in entity.attributes:
                attr_names.add(f"{entity.name.lower()}_{attr.name}")
        
        # Check constraints
        for constraint in model.constraints:
            self._validate_expression(constraint.expression, attr_names, "Constraint")
        
        # Check rules
        for rule in model.rules:
            self._validate_expression(rule.condition, attr_names, f"Rule '{rule.name}' condition")
            if rule.implies:
                self._validate_expression(rule.implies, attr_names, f"Rule '{rule.name}' implies")
    
    def _validate_expression(self, expr: str, valid_names: set, context: str):
        """Basic validation of expressions."""
        # This is a simplified validation - in a real implementation,
        # you'd want to parse the expression properly
        tokens = expr.replace('(', ' ').replace(')', ' ').replace(',', ' ').split()
        
        for token in tokens:
            # Skip operators and literals
            if token in ['and', 'or', 'not', '>', '<', '>=', '<=', '==', '!=', 
                        '+', '-', '*', '/', '->', 'in', 'contains', 'size']:
                continue
            
            # Skip numeric literals
            try:
                float(token)
                continue
            except ValueError:
                pass
            
            # Skip string literals
            if token.startswith('"') or token.startswith("'"):
                continue
            
            # Skip boolean literals
            if token.lower() in ['true', 'false']:
                continue
            
            # Check if it's a valid attribute reference
            if not any(name in token for name in valid_names):
                self.warnings.append(f"{context}: Unknown reference '{token}'")
