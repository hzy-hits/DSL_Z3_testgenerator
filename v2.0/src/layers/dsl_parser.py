"""
DSL Parser for V2.0

Parses YAML DSL files into normalized internal models.
This parser is strict and validates everything upfront.
"""

import yaml
from typing import Dict, Any, List, Optional
from pathlib import Path

from ..core.models import (
    DSLModel, Entity, Attribute, AttributeType, 
    Constraint, ConstraintType, Rule, TestHint,
    State, Transition, StateMachine
)


class DSLParseError(Exception):
    """DSL parsing error with context"""
    def __init__(self, message: str, context: str = None):
        super().__init__(message)
        self.context = context


class DSLParser:
    """Parse YAML DSL files into normalized model"""
    
    def __init__(self):
        self.attribute_map = {}  # Map simple names to full names
    
    def parse_file(self, path: str) -> DSLModel:
        """Parse DSL from file"""
        file_path = Path(path)
        if not file_path.exists():
            raise DSLParseError(f"File not found: {path}")
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                data = yaml.safe_load(f)
        except yaml.YAMLError as e:
            raise DSLParseError(f"Invalid YAML: {e}")
        
        return self.parse_dict(data)
    
    def parse_dict(self, data: Dict[str, Any]) -> DSLModel:
        """Parse DSL from dictionary"""
        # Validate required fields
        if 'domain' not in data:
            raise DSLParseError("Missing required field: domain")
        if 'entities' not in data:
            raise DSLParseError("Missing required field: entities")
        
        # Parse domain
        domain = data['domain']
        
        # Parse entities and build attribute map
        entities = []
        for entity_data in data.get('entities', []):
            entity = self._parse_entity(entity_data)
            entities.append(entity)
            # Build attribute map
            for attr in entity.attributes:
                self.attribute_map[attr.name] = attr.full_name
        
        if not entities:
            raise DSLParseError("At least one entity is required")
        
        # Parse constraints
        constraints = []
        for constraint_data in data.get('constraints', []):
            constraint = self._parse_constraint(constraint_data)
            constraints.append(constraint)
        
        # Parse rules
        rules = []
        for rule_data in data.get('rules', []):
            rule = self._parse_rule(rule_data)
            rules.append(rule)
        
        # Parse test hints
        test_hints = []
        for hint_data in data.get('test_hints', []):
            hint = self._parse_test_hint(hint_data)
            test_hints.append(hint)
        
        # Parse state machines
        state_machines = []
        for sm_data in data.get('state_machines', []):
            state_machine = self._parse_state_machine(sm_data)
            state_machines.append(state_machine)
        
        # Create model
        model = DSLModel(
            domain=domain,
            entities=entities,
            constraints=constraints,
            rules=rules,
            test_hints=test_hints,
            state_machines=state_machines,
            metadata=data.get('metadata', {})
        )
        
        # Validate model
        errors = model.validate()
        if errors:
            raise DSLParseError(f"Model validation failed: {'; '.join(errors)}")
        
        return model
    
    def _parse_entity(self, data: Dict[str, Any]) -> Entity:
        """Parse entity definition"""
        if 'name' not in data:
            raise DSLParseError("Entity missing required field: name")
        if 'attributes' not in data:
            raise DSLParseError(f"Entity {data['name']} missing required field: attributes")
        
        name = data['name']
        attributes = []
        
        for attr_data in data['attributes']:
            attr = self._parse_attribute(attr_data, entity_name=name)
            attributes.append(attr)
        
        if not attributes:
            raise DSLParseError(f"Entity {name} must have at least one attribute")
        
        return Entity(name=name, attributes=attributes)
    
    def _parse_attribute(self, data: Dict[str, Any], entity_name: str) -> Attribute:
        """Parse attribute definition"""
        if 'name' not in data:
            raise DSLParseError("Attribute missing required field: name", 
                              context=f"entity={entity_name}")
        if 'type' not in data:
            raise DSLParseError(f"Attribute {data['name']} missing required field: type",
                              context=f"entity={entity_name}")
        
        name = data['name']
        type_str = data['type'].lower()
        
        # Parse type
        try:
            if type_str in ['array', 'set']:
                # Collection types - for now treat as string
                attr_type = AttributeType.STRING
            else:
                attr_type = AttributeType(type_str)
        except ValueError:
            raise DSLParseError(f"Invalid attribute type: {type_str}",
                              context=f"attribute={entity_name}.{name}")
        
        # Create attribute
        attr = Attribute(
            name=name,
            entity_name=entity_name,
            type=attr_type,
            min_value=data.get('min'),
            max_value=data.get('max'),
            enum_values=data.get('values'),
            pattern=data.get('pattern'),
            nullable=data.get('nullable', False)
        )
        
        return attr
    
    def _normalize_expression(self, expr: str) -> str:
        """Normalize expression by adding entity prefixes to attributes"""
        # This is a simple implementation - a real one would use proper parsing
        normalized = expr
        
        # Sort by length descending to avoid replacing substrings
        for simple_name in sorted(self.attribute_map.keys(), key=len, reverse=True):
            full_name = self.attribute_map[simple_name]
            # Replace only whole words (bounded by non-alphanumeric characters)
            import re
            pattern = r'\b' + re.escape(simple_name) + r'\b'
            normalized = re.sub(pattern, full_name, normalized)
        
        return normalized
    
    def _parse_constraint(self, data: Any) -> Constraint:
        """Parse constraint definition"""
        # Handle both string and dict formats
        if isinstance(data, str):
            # Simple string constraint
            expr = self._normalize_expression(data)
            return Constraint(
                expression=expr,
                type=self._infer_constraint_type(expr),
                description=None
            )
        elif isinstance(data, dict):
            if 'expression' not in data:
                raise DSLParseError("Constraint missing required field: expression")
            
            expr = self._normalize_expression(data['expression'])
            return Constraint(
                expression=expr,
                type=self._infer_constraint_type(expr),
                description=data.get('description')
            )
        else:
            raise DSLParseError(f"Invalid constraint format: {type(data)}")
    
    def _infer_constraint_type(self, expression: str) -> ConstraintType:
        """Infer constraint type from expression"""
        expr = expression.lower()
        
        if '->' in expression:
            return ConstraintType.IMPLICATION
        elif any(op in expression for op in ['>=', '<=', '>', '<']):
            return ConstraintType.RANGE
        elif '==' in expression and any(k in expr for k in ['in', 'values', 'enum']):
            return ConstraintType.ENUM
        elif any(k in expr for k in ['length', 'size', 'count']):
            return ConstraintType.COLLECTION
        else:
            return ConstraintType.RELATION
    
    def _parse_rule(self, data: Dict[str, Any]) -> Rule:
        """Parse rule definition"""
        if 'name' not in data:
            raise DSLParseError("Rule missing required field: name")
        
        # Handle multiple formats: 'if/then', 'condition/action', 'condition/implies'
        condition = data.get('if') or data.get('condition')
        consequence = data.get('then') or data.get('action') or data.get('consequence') or data.get('implies')
        
        if not condition:
            raise DSLParseError(f"Rule {data['name']} missing condition (if/condition)")
        if not consequence:
            raise DSLParseError(f"Rule {data['name']} missing consequence (then/action/implies)")
        
        return Rule(
            name=data['name'],
            condition=self._normalize_expression(condition),
            consequence=self._normalize_expression(consequence),
            priority=data.get('priority', 1),
            description=data.get('description')
        )
    
    def _parse_test_hint(self, data: Dict[str, Any]) -> TestHint:
        """Parse test hint"""
        if 'type' not in data:
            raise DSLParseError("Test hint missing required field: type")
        if 'target' not in data:
            raise DSLParseError("Test hint missing required field: target")
        
        # Ensure target is a list
        target = data['target']
        if isinstance(target, str):
            target = [target]
        
        return TestHint(
            type=data['type'],
            target=target,
            reason=data.get('reason')
        )
    
    def _parse_state_machine(self, data: Dict[str, Any]) -> StateMachine:
        """Parse state machine definition"""
        if 'name' not in data:
            raise DSLParseError("State machine missing required field: name")
        if 'entity' not in data:
            raise DSLParseError("State machine missing required field: entity")
        if 'state_attribute' not in data:
            raise DSLParseError("State machine missing required field: state_attribute")
        if 'states' not in data:
            raise DSLParseError("State machine missing required field: states")
        if 'transitions' not in data:
            raise DSLParseError("State machine missing required field: transitions")
        
        # Parse states
        states = []
        state_value_map = {}  # Map state names to numeric values
        for i, state_data in enumerate(data['states']):
            if isinstance(state_data, str):
                # Simple state name
                state = State(name=state_data, value=i+1)
            else:
                # Detailed state definition
                if 'name' not in state_data:
                    raise DSLParseError("State missing required field: name")
                state = State(
                    name=state_data['name'],
                    value=state_data.get('value', i+1),
                    description=state_data.get('description')
                )
            states.append(state)
            state_value_map[state.name] = state.value
        
        # Parse transitions
        transitions = []
        for trans_data in data['transitions']:
            if 'name' not in trans_data:
                raise DSLParseError("Transition missing required field: name")
            if 'from' not in trans_data:
                raise DSLParseError(f"Transition {trans_data['name']} missing required field: from")
            if 'to' not in trans_data:
                raise DSLParseError(f"Transition {trans_data['name']} missing required field: to")
            
            # Normalize condition - handle various formats
            condition = trans_data.get('condition', 'true')
            if 'if' in trans_data:
                condition = trans_data['if']
            
            transition = Transition(
                name=trans_data['name'],
                from_state=trans_data['from'],
                to_state=trans_data['to'],
                condition=self._normalize_expression(condition),
                description=trans_data.get('description')
            )
            
            # Validate states exist
            if transition.from_state not in state_value_map:
                raise DSLParseError(f"Transition {transition.name} references unknown state: {transition.from_state}")
            if transition.to_state not in state_value_map:
                raise DSLParseError(f"Transition {transition.name} references unknown state: {transition.to_state}")
            
            transitions.append(transition)
        
        return StateMachine(
            name=data['name'],
            entity=data['entity'],
            state_attribute=data['state_attribute'],
            states=states,
            transitions=transitions
        )


class DSLValidator:
    """Additional validation for DSL models"""
    
    def validate_model(self, model: DSLModel) -> List[str]:
        """Perform deep validation of DSL model"""
        errors = []
        
        # Basic validation from model
        errors.extend(model.validate())
        
        # Check constraint validity
        for constraint in model.constraints:
            err = self._validate_constraint_expression(constraint, model)
            if err:
                errors.append(err)
        
        # Check rule validity
        for rule in model.rules:
            err = self._validate_rule_expressions(rule, model)
            if err:
                errors.extend(err)
        
        # Check for circular dependencies
        circular = self._check_circular_dependencies(model)
        if circular:
            errors.extend(circular)
        
        return errors
    
    def _validate_constraint_expression(self, constraint: Constraint, model: DSLModel) -> Optional[str]:
        """Validate constraint expression references valid attributes"""
        # This is a simplified check - real implementation would parse properly
        all_attrs = {attr.full_name for attr in model.get_all_attributes()}
        
        for attr_name in constraint.attributes:
            if attr_name not in all_attrs:
                return f"Constraint '{constraint.expression}' references unknown attribute: {attr_name}"
        
        return None
    
    def _validate_rule_expressions(self, rule: Rule, model: DSLModel) -> List[str]:
        """Validate rule expressions"""
        errors = []
        all_attrs = {attr.full_name for attr in model.get_all_attributes()}
        
        # Check condition
        for attr in all_attrs:
            if attr in rule.condition:
                break
        else:
            # No known attribute found in condition
            errors.append(f"Rule '{rule.name}' condition may not reference any known attributes")
        
        # Check consequence
        for attr in all_attrs:
            if attr in rule.consequence:
                break
        else:
            # No known attribute found in consequence
            errors.append(f"Rule '{rule.name}' consequence may not reference any known attributes")
        
        return errors
    
    def _check_circular_dependencies(self, model: DSLModel) -> List[str]:
        """Check for circular dependencies in rules"""
        errors = []
        
        # Build dependency graph
        deps = {}
        for rule in model.rules:
            # Extract attributes from condition and consequence
            # This is simplified - real implementation would parse properly
            condition_attrs = [a for a in model.get_all_attributes() 
                             if a.full_name in rule.condition]
            consequence_attrs = [a for a in model.get_all_attributes() 
                               if a.full_name in rule.consequence]
            
            deps[rule.name] = {
                'depends_on': [a.full_name for a in condition_attrs],
                'affects': [a.full_name for a in consequence_attrs]
            }
        
        # Check for cycles (simplified)
        # Real implementation would use proper graph algorithms
        
        return errors