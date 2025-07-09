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
        
        # Domain-specific fixes
        fixed_data = self._apply_domain_specific_fixes(fixed_data)
        
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
        """Apply domain-specific business logic fixes."""
        fixed_data = test_data.copy()
        
        # Insurance domain fixes
        if 'claim_amount' in fixed_data and 'coverage_amount' in fixed_data:
            # Ensure claim doesn't exceed coverage
            if fixed_data['claim_amount'] > fixed_data['coverage_amount']:
                fixed_data['claim_amount'] = fixed_data['coverage_amount'] * 0.8
        
        if 'claim_amount' in fixed_data and 'deductible' in fixed_data:
            # Ensure claim is reasonable compared to deductible
            if fixed_data['claim_amount'] > 0 and fixed_data['claim_amount'] < fixed_data['deductible']:
                # Make claim at least 2x deductible for it to make sense
                fixed_data['claim_amount'] = fixed_data['deductible'] * 2
        
        # Hotel booking domain fixes
        if 'booking_is_peak_season' in fixed_data and 'booking_discount_percent' in fixed_data:
            # In peak season, limit discounts
            if fixed_data['booking_is_peak_season'] and fixed_data['booking_discount_percent'] > 10:
                fixed_data['booking_discount_percent'] = 10
        
        if 'customer_is_vip' in fixed_data and 'booking_discount_percent' in fixed_data:
            # VIP customers should have meaningful discounts
            if fixed_data['customer_is_vip'] and fixed_data['booking_discount_percent'] < 15:
                fixed_data['booking_discount_percent'] = 15
        
        # Fix total price calculations if present
        if all(key in fixed_data for key in ['room_base_price', 'booking_days', 'booking_discount_percent', 'booking_total_price']):
            base_total = fixed_data['room_base_price'] * fixed_data['booking_days']
            discount_amount = base_total * (fixed_data['booking_discount_percent'] / 100)
            expected_total = base_total - discount_amount
            
            # Allow some tolerance for floating point
            if abs(fixed_data['booking_total_price'] - expected_total) > 1.0:
                fixed_data['booking_total_price'] = round(expected_total, 2)
        
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