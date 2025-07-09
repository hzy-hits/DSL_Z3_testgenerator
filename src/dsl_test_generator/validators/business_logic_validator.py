"""Business logic validator for test case generation.

This module ensures that generated test data follows business rules
and maintains realistic relationships between attributes.
"""

from typing import Dict, List, Any, Optional, Tuple
import re

from ..types import DSLModel, Constraint, Rule
from ..config import DSLEngineConfig


class BusinessLogicValidator:
    """Validates and corrects test data to ensure business logic consistency."""
    
    def __init__(self, model: DSLModel, config: Optional[DSLEngineConfig] = None):
        self.model = model
        self.config = config
        self.cross_entity_rules = self._extract_cross_entity_rules()
        self.dependent_attributes = self._find_dependent_attributes()
        
        # Debug: Print found rules
        if config and hasattr(config, 'test_generation') and hasattr(config.test_generation, 'debug'):
            print(f"Found {len(self.cross_entity_rules)} cross-entity rules")
            for rule in self.cross_entity_rules:
                print(f"  Rule: {rule}")
    
    def _extract_cross_entity_rules(self) -> List[Dict[str, Any]]:
        """Extract rules that involve multiple entities or cross-attribute dependencies."""
        rules = []
        
        # Look for constraints with multiple entity references
        for constraint in self.model.constraints:
            expr = constraint.expression
            # Find patterns like entity1_attr == entity2_attr
            matches = re.findall(r'(\w+)_(\w+)\s*==\s*(\w+)_(\w+)', expr)
            for match in matches:
                if match[0] != match[2]:  # Different entities
                    rules.append({
                        'type': 'cross_entity_equality',
                        'source': f"{match[0]}_{match[1]}",
                        'target': f"{match[2]}_{match[3]}",
                        'expression': constraint.expression
                    })
            
            # Find patterns like claim_type == policy_type (same attribute name)
            simple_matches = re.findall(r'(\w+)_(\w+)\s*==\s*(\w+)_(\w+)', expr)
            for match in simple_matches:
                if match[1] == match[3]:  # Same attribute name
                    rules.append({
                        'type': 'attribute_matching',
                        'attribute': match[1],
                        'entities': [match[0], match[2]],
                        'expression': constraint.expression
                    })
            
            # Also check for patterns without entity prefixes (e.g., claim_type == policy_type)
            # when entities are inferred from context
            simple_equality = re.findall(r'\b(\w+)\s*==\s*(\w+)\b', expr)
            for match in simple_equality:
                # Check if these could be attribute names (e.g., claim_type, policy_type)
                if match[0] != match[1] and '_' not in match[0] and '_' not in match[1]:
                    rules.append({
                        'type': 'direct_equality',
                        'source': match[0],
                        'target': match[1],
                        'expression': constraint.expression
                    })
        
        return rules
    
    def _find_dependent_attributes(self) -> Dict[str, List[str]]:
        """Find attributes that depend on other attributes."""
        dependencies = {}
        
        for constraint in self.model.constraints:
            expr = constraint.expression
            # Parse constraint to find dependencies
            # Example: "room_type == 1 -> room_base_price >= 200"
            if '->' in expr or 'implies' in expr:
                parts = re.split(r'->|implies', expr)
                if len(parts) == 2:
                    condition, result = parts
                    # Extract attributes from condition and result
                    condition_attrs = re.findall(r'(\w+_\w+)', condition)
                    result_attrs = re.findall(r'(\w+_\w+)', result)
                    
                    for result_attr in result_attrs:
                        if result_attr not in dependencies:
                            dependencies[result_attr] = []
                        dependencies[result_attr].extend(condition_attrs)
        
        return dependencies
    
    def validate_and_fix_test_case(self, test_data: Dict[str, Any]) -> Dict[str, Any]:
        """Validate and fix a single test case to ensure business logic consistency."""
        if not self.config or not self.config.test_generation.validate_business_logic:
            return test_data
        
        fixed_data = test_data.copy()
        
        # First, fix any None values that should have defaults
        fixed_data = self._fix_none_values(fixed_data)
        
        # Fix cross-entity equality rules
        for rule in self.cross_entity_rules:
            if rule['type'] == 'attribute_matching':
                # Ensure matching attributes have the same value
                attr_name = rule['attribute']
                entity_attrs = [f"{entity}_{attr_name}" for entity in rule['entities']]
                
                # Check if all relevant attributes exist in test data
                existing_attrs = [attr for attr in entity_attrs if attr in fixed_data]
                if len(existing_attrs) > 1:
                    # Use the first value for all matching attributes
                    first_value = fixed_data[existing_attrs[0]]
                    for attr in existing_attrs[1:]:
                        fixed_data[attr] = first_value
            
            elif rule['type'] == 'cross_entity_equality':
                source = rule['source']
                target = rule['target']
                if source in fixed_data and target in fixed_data:
                    # Make target equal to source
                    fixed_data[target] = fixed_data[source]
            
            elif rule['type'] == 'direct_equality':
                source = rule['source']
                target = rule['target']
                if source in fixed_data and target in fixed_data:
                    # Make target equal to source
                    fixed_data[target] = fixed_data[source]
        
        # Fix dependent attribute relationships
        fixed_data = self._fix_dependent_attributes(fixed_data)
        
        # Validate and fix rule consistency
        fixed_data = self._validate_rule_consistency(fixed_data)
        
        # Domain-specific fixes
        fixed_data = self._apply_domain_specific_fixes(fixed_data)
        
        # Final validation of constraints
        fixed_data = self._validate_constraints(fixed_data)
        
        return fixed_data
    
    def _fix_dependent_attributes(self, test_data: Dict[str, Any]) -> Dict[str, Any]:
        """Fix attributes that depend on other attributes."""
        fixed_data = test_data.copy()
        
        # Example: Fix room price based on room type
        if 'room_room_type' in fixed_data and 'room_base_price' in fixed_data:
            room_type = fixed_data['room_room_type']
            current_price = fixed_data['room_base_price']
            
            # Define price ranges for each room type
            price_ranges = {
                1: (200.0, 500.0),    # Standard room
                2: (500.0, 1000.0),   # Deluxe room
                3: (1000.0, 3000.0),  # Suite
            }
            
            if room_type in price_ranges:
                min_price, max_price = price_ranges[room_type]
                if current_price < min_price or current_price > max_price:
                    # Adjust price to middle of valid range
                    fixed_data['room_base_price'] = (min_price + max_price) / 2
        
        return fixed_data
    
    def _apply_domain_specific_fixes(self, test_data: Dict[str, Any]) -> Dict[str, Any]:
        """Apply domain-specific business logic fixes based on rules and constraints."""
        fixed_data = test_data.copy()
        
        # Instead of hardcoding domain logic, derive it from the model's rules and constraints
        # This method is left as a hook for future extensions where domain-specific
        # validators can be registered dynamically
        
        # For now, we only apply fixes that are explicitly defined in the DSL model
        # through rules and constraints, which are already handled by other methods
        
        return fixed_data
    
    def validate_test_suite(self, test_cases: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """Validate and fix an entire test suite."""
        validated_cases = []
        
        for test_case in test_cases:
            # Extract test data from the test case structure
            if 'values' in test_case:
                fixed_values = self.validate_and_fix_test_case(test_case['values'])
                validated_case = test_case.copy()
                validated_case['values'] = fixed_values
                validated_cases.append(validated_case)
            else:
                # Handle direct test data format
                validated_cases.append(self.validate_and_fix_test_case(test_case))
        
        return validated_cases
    
    def _fix_none_values(self, test_data: Dict[str, Any]) -> Dict[str, Any]:
        """Replace None values with appropriate defaults based on attribute type."""
        fixed_data = test_data.copy()
        
        for key, value in test_data.items():
            if value is None or value == "None":
                # Find the attribute definition
                for entity in self.model.entities:
                    for attr in entity.attributes:
                        full_name = f"{entity.name.lower()}_{attr.name}"
                        if full_name == key:
                            # Provide appropriate default based on type
                            if attr.type == "integer":
                                fixed_data[key] = attr.min_value if attr.min_value is not None else 0
                            elif attr.type == "real":
                                fixed_data[key] = attr.min_value if attr.min_value is not None else 0.0
                            elif attr.type == "boolean":
                                fixed_data[key] = False
                            elif attr.type == "string":
                                fixed_data[key] = f"default_{attr.name}"
                            break
        
        return fixed_data
    
    def _validate_rule_consistency(self, test_data: Dict[str, Any]) -> Dict[str, Any]:
        """Ensure test data is consistent with activated rules."""
        fixed_data = test_data.copy()
        
        for rule in self.model.rules:
            # Check if rule condition is satisfied
            if self._is_rule_activated(rule.condition, fixed_data):
                # Ensure the action is also satisfied
                if rule.action:
                    fixed_data = self._enforce_rule_action(rule.action, fixed_data)
        
        return fixed_data
    
    def _is_rule_activated(self, condition: str, test_data: Dict[str, Any]) -> bool:
        """Check if a rule condition is satisfied by the test data."""
        try:
            # Simple evaluation for common patterns
            if '>=' in condition:
                parts = condition.split('>=')
                if len(parts) == 2:
                    var, val = parts[0].strip(), parts[1].strip()
                    if var in test_data:
                        return test_data[var] >= float(val)
            
            if '<=' in condition:
                parts = condition.split('<=')
                if len(parts) == 2:
                    var, val = parts[0].strip(), parts[1].strip()
                    if var in test_data:
                        return test_data[var] <= float(val)
            
            if '==' in condition:
                parts = condition.split('==')
                if len(parts) == 2:
                    var, val = parts[0].strip(), parts[1].strip()
                    if var in test_data:
                        try:
                            return test_data[var] == float(val)
                        except:
                            return str(test_data[var]) == val
            
            return False
        except:
            return False
    
    def _enforce_rule_action(self, action: str, test_data: Dict[str, Any]) -> Dict[str, Any]:
        """Enforce a rule action by modifying test data."""
        fixed_data = test_data.copy()
        
        # Parse and apply the action
        if '==' in action:
            parts = action.split('==')
            if len(parts) == 2:
                var, val = parts[0].strip(), parts[1].strip()
                if var in fixed_data:
                    try:
                        fixed_data[var] = float(val)
                    except:
                        fixed_data[var] = val
        
        return fixed_data
    
    def _validate_constraints(self, test_data: Dict[str, Any]) -> Dict[str, Any]:
        """Ensure all constraints are satisfied."""
        fixed_data = test_data.copy()
        
        for constraint in self.model.constraints:
            expr = constraint.expression
            
            # Handle simple >= constraints
            if '>=' in expr and ' and ' not in expr:
                parts = expr.split('>=')
                if len(parts) == 2:
                    var, min_val = parts[0].strip(), parts[1].strip()
                    if var in fixed_data:
                        try:
                            min_num = float(min_val)
                            if fixed_data[var] < min_num:
                                fixed_data[var] = min_num
                        except:
                            pass
            
            # Handle simple <= constraints
            if '<=' in expr and ' and ' not in expr:
                parts = expr.split('<=')
                if len(parts) == 2:
                    var, max_val = parts[0].strip(), parts[1].strip()
                    if var in fixed_data:
                        try:
                            max_num = float(max_val)
                            if fixed_data[var] > max_num:
                                fixed_data[var] = max_num
                        except:
                            pass
        
        return fixed_data