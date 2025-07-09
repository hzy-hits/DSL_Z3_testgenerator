"""Smart test generator that understands DSL semantics"""

from typing import Dict, List, Any, Optional, Tuple
import re
import z3

from ..types import DSLModel, Rule, Constraint
from ..core.z3_solver import Z3Solver
from .domain_aware_test_generator import DomainAwareTestGenerator
from ..config import DSLEngineConfig, default_config
from ..validators import BusinessLogicValidator


class SmartTestGenerator(DomainAwareTestGenerator):
    """Test generator that intelligently creates tests based on DSL content."""
    
    def __init__(self, config: Optional[DSLEngineConfig] = None):
        self.config = config or default_config
        super().__init__()
    
    def generate_comprehensive_test_suite(
        self,
        solver: Z3Solver,
        model: DSLModel,
        translator: Any
    ) -> List[Dict[str, Any]]:
        """Generate comprehensive test suite based on DSL content."""
        # Store model for analysis
        self._model = model
        self._solver_vars = solver.variables
        
        test_cases = []
        
        # 1. Boundary tests - ensure all attributes are covered
        test_cases.extend(self._generate_all_boundary_tests(solver, model))
        
        # 2. Equivalence tests - test all enum values
        test_cases.extend(self._generate_all_equivalence_tests(solver, model))
        
        # 3. Rule coverage tests - test each rule activation
        smart_rule_tests = self._generate_smart_rule_tests(solver, model, translator)
        test_cases.extend(smart_rule_tests)
        
        # 4. Constraint violation tests - test each constraint
        constraint_tests = self._generate_smart_constraint_violations(solver, model, translator)
        test_cases.extend(constraint_tests)
        
        # 5. Negative tests - test invalid values
        test_cases.extend(self.generate_negative_tests(solver, model, translator))
        
        # 6. Combination tests - test important combinations
        combo_tests = self._generate_combination_tests(solver, model)
        test_cases.extend(combo_tests)
        
        # Remove duplicates
        unique_tests = self._deduplicate_tests(test_cases)
        
        # Validate and fix business logic if enabled
        if self.config.test_generation.validate_business_logic:
            validator = BusinessLogicValidator(model, self.config)
            unique_tests = validator.validate_test_suite(unique_tests)
        
        return unique_tests
    
    def _generate_smart_rule_tests(
        self,
        solver: Z3Solver,
        model: DSLModel,
        translator: Any
    ) -> List[Dict[str, Any]]:
        """Generate tests for each rule based on its condition."""
        test_cases = []
        
        for rule in model.rules:
            # Parse rule condition to understand what values to set
            condition_values = self._parse_rule_condition(rule.condition)
            
            # Create a test that activates this rule
            values = self._get_default_valid_values()
            
            # Apply parsed condition values
            for var, val in condition_values.items():
                if var in values:
                    values[var] = val
            
            # Ensure related constraints are satisfied
            self._ensure_constraint_consistency(values, model)
            
            test_case = {
                'name': f"rule_{self._sanitize_name(rule.name)}_active",
                'description': f"Activate rule: {rule.name} - {rule.description}",
                'values': values,
                'expected': 'pass',
                'type': 'rule_coverage',
                'rule': rule.name
            }
            test_cases.append(test_case)
            
            # Also create a test where the rule is NOT activated
            inactive_values = self._create_rule_inactive_scenario(rule, model)
            if inactive_values:
                test_case = {
                    'name': f"rule_{self._sanitize_name(rule.name)}_inactive",
                    'description': f"Rule not activated: {rule.name}",
                    'values': inactive_values,
                    'expected': 'pass',
                    'type': 'rule_coverage',
                    'rule': f"{rule.name} (inactive)"
                }
                test_cases.append(test_case)
        
        return test_cases
    
    def _generate_smart_constraint_violations(
        self,
        solver: Z3Solver,
        model: DSLModel,
        translator: Any
    ) -> List[Dict[str, Any]]:
        """Generate tests that violate each constraint."""
        test_cases = []
        
        # Add specific constraint violation tests
        for constraint in model.constraints:
            violation_scenarios = self._create_constraint_violations(constraint, model)
            
            for i, scenario in enumerate(violation_scenarios):
                # Handle constraints without descriptions
                constraint_desc = constraint.description or constraint.expression
                test_case = {
                    'name': f"constraint_violation_{self._sanitize_name(constraint_desc)}_{i+1}",
                    'description': f"Violate: {constraint_desc}",
                    'values': scenario,
                    'expected': 'fail',
                    'type': 'constraint_violation',
                    'violated_constraint': constraint.expression
                }
                test_cases.append(test_case)
        
        return test_cases
    
    def _generate_combination_tests(
        self,
        solver: Z3Solver,
        model: DSLModel
    ) -> List[Dict[str, Any]]:
        """Generate tests for important attribute combinations."""
        test_cases = []
        
        # Identify attributes that appear together in constraints
        related_attrs = self._find_related_attributes(model)
        
        for attr_group in related_attrs:
            # Create tests for different combinations
            combinations = self._generate_attribute_combinations(attr_group, model)
            
            for i, combo in enumerate(combinations[:5]):  # Limit to 5 combinations
                test_case = {
                    'name': f"combination_{i+1}_{'+'.join(attr_group)}",
                    'description': f"Test combination of: {', '.join(attr_group)}",
                    'values': combo,
                    'expected': 'pass',
                    'type': 'combination'
                }
                test_cases.append(test_case)
        
        return test_cases
    
    def _parse_rule_condition(self, condition: str) -> Dict[str, Any]:
        """Parse a rule condition to extract variable values."""
        values = {}
        
        # Split by 'and' to handle compound conditions
        conditions = condition.split(' and ')
        
        for cond in conditions:
            cond = cond.strip()
            
            # Handle equality conditions (var == value)
            eq_pattern = r'(\w+)\s*==\s*(\w+|"[^"]*"|\d+(?:\.\d+)?|True|False)'
            match = re.search(eq_pattern, cond)
            if match:
                var, val = match.groups()
                
                # Convert value to appropriate type
                if val == 'True':
                    values[var] = True
                elif val == 'False':
                    values[var] = False
                elif val.startswith('"') and val.endswith('"'):
                    values[var] = val[1:-1]
                elif '.' in val:
                    values[var] = float(val)
                else:
                    try:
                        values[var] = int(val)
                    except ValueError:
                        values[var] = val
                continue
            
            # Handle comparison conditions (var > value, var < value, etc.)
            comp_pattern = r'(\w+)\s*([><]=?)\s*(\d+(?:\.\d+)?)'
            match = re.search(comp_pattern, cond)
            if match:
                var, op, val = match.groups()
                val = float(val) if '.' in val else int(val)
                
                # Set value based on operator
                if op == '>':
                    values[var] = val + 1
                elif op == '>=':
                    values[var] = val
                elif op == '<':
                    values[var] = val - 1
                elif op == '<=':
                    values[var] = val
                continue
            
            # Handle 'in' conditions (value in var)
            in_pattern = r'"([^"]+)"\s+in\s+(\w+)'
            match = re.search(in_pattern, cond)
            if match:
                val, var = match.groups()
                # For 'in' conditions, we might need to set an array/set
                values[var] = [val]  # Simple approach
        
        # Map simple variable names to full entity-prefixed names
        mapped_values = {}
        for var, val in values.items():
            # Try to find the full variable name
            full_var = self._find_full_variable_name(var)
            if full_var:
                mapped_values[full_var] = val
            else:
                mapped_values[var] = val
        
        return mapped_values
    
    def _find_full_variable_name(self, simple_name: str) -> Optional[str]:
        """Find the full entity-prefixed variable name for a simple name."""
        if not hasattr(self, '_model') or not self._model:
            return None
        
        # Search through all attributes
        for entity in self._model.entities:
            for attr in entity.attributes:
                if attr.name == simple_name:
                    return f"{entity.name.lower()}_{attr.name}"
        
        return None
    
    def _ensure_constraint_consistency(self, values: Dict[str, Any], model: DSLModel) -> None:
        """Ensure values satisfy related constraints."""
        # Look for constraints that relate attributes
        for constraint in model.constraints:
            expr = constraint.expression
            
            # Handle "a == b" constraints
            if '==' in expr and ' and ' not in expr and ' or ' not in expr:
                parts = expr.split('==')
                if len(parts) == 2:
                    var1, var2 = parts[0].strip(), parts[1].strip()
                    if var1 in values and var2 in values:
                        # Make them equal
                        values[var2] = values[var1]
            
            # Handle range constraints
            if '>=' in expr and '<=' in expr:
                # This might be a range constraint like "x >= min and x <= max"
                # Parse and ensure value is within range
                pass
    
    def _create_rule_inactive_scenario(self, rule: Rule, model: DSLModel) -> Optional[Dict[str, Any]]:
        """Create a scenario where the rule is NOT activated."""
        values = self._get_default_valid_values()
        condition_values = self._parse_rule_condition(rule.condition)
        
        # Try to negate the condition
        for var, val in condition_values.items():
            if var in values:
                if isinstance(val, bool):
                    values[var] = not val
                elif isinstance(val, (int, float)):
                    # Set to a different value
                    values[var] = val - 1 if val > 0 else val + 1
                break  # Change just one condition
        
        self._ensure_constraint_consistency(values, model)
        return values
    
    def _create_constraint_violations(self, constraint: Constraint, model: DSLModel) -> List[Dict[str, Any]]:
        """Create scenarios that violate a specific constraint."""
        violations = []
        expr = constraint.expression
        
        # Parse different types of constraints
        if '==' in expr and '!=' not in expr:
            # Equality constraint - make them unequal
            parts = expr.split('==')
            if len(parts) == 2:
                var1, var2 = parts[0].strip(), parts[1].strip()
                values = self._get_default_valid_values()
                
                # Try to set different values
                if var1 in values and var2 in values:
                    if isinstance(values[var1], (int, float)):
                        values[var2] = values[var1] + 1
                    else:
                        values[var2] = 999  # Different value
                    violations.append(values)
        
        elif '<=' in expr and '>=' not in expr:
            # Upper bound constraint - exceed it
            parts = expr.split('<=')
            if len(parts) == 2:
                var, limit = parts[0].strip(), parts[1].strip()
                try:
                    limit_val = float(limit) if '.' in limit else int(limit)
                    values = self._get_default_valid_values()
                    if var in values:
                        values[var] = limit_val + 1
                        violations.append(values)
                except ValueError:
                    # Might be comparing to another variable
                    pass
        
        elif '>=' in expr and '<=' not in expr:
            # Lower bound constraint - go below it
            parts = expr.split('>=')
            if len(parts) == 2:
                var, limit = parts[0].strip(), parts[1].strip()
                try:
                    limit_val = float(limit) if '.' in limit else int(limit)
                    values = self._get_default_valid_values()
                    if var in values:
                        values[var] = limit_val - 1
                        violations.append(values)
                except ValueError:
                    pass
        
        return violations
    
    def _find_related_attributes(self, model: DSLModel) -> List[List[str]]:
        """Find attributes that appear together in constraints or rules."""
        related_groups = []
        
        # Analyze constraints
        for constraint in model.constraints:
            # Extract variable names from expression
            var_pattern = r'\b(\w+_\w+)\b'
            vars_in_constraint = list(set(re.findall(var_pattern, constraint.expression)))
            
            if len(vars_in_constraint) > 1:
                related_groups.append(vars_in_constraint)
        
        # Analyze rules
        for rule in model.rules:
            vars_in_rule = list(set(re.findall(var_pattern, rule.condition)))
            if len(vars_in_rule) > 1:
                related_groups.append(vars_in_rule)
        
        # Remove duplicates and return unique groups
        unique_groups = []
        for group in related_groups:
            if group not in unique_groups:
                unique_groups.append(sorted(group))
        
        return unique_groups[:3]  # Limit to top 3 groups
    
    def _generate_attribute_combinations(
        self,
        attr_group: List[str],
        model: DSLModel
    ) -> List[Dict[str, Any]]:
        """Generate different value combinations for related attributes."""
        combinations = []
        base_values = self._get_default_valid_values()
        
        # Generate a few different combinations
        for i in range(3):
            values = base_values.copy()
            
            # Vary the values in the group
            for attr in attr_group:
                if attr in values:
                    if isinstance(values[attr], bool):
                        values[attr] = (i % 2) == 0
                    elif isinstance(values[attr], (int, float)):
                        # Use different strategies for different iterations
                        if i == 0:
                            # Minimum values
                            values[attr] = self._get_min_value_for_attr(attr, model)
                        elif i == 1:
                            # Maximum values
                            values[attr] = self._get_max_value_for_attr(attr, model)
                        else:
                            # Mid-range values
                            min_val = self._get_min_value_for_attr(attr, model)
                            max_val = self._get_max_value_for_attr(attr, model)
                            if min_val is not None and max_val is not None:
                                values[attr] = (min_val + max_val) // 2
            
            self._ensure_constraint_consistency(values, model)
            combinations.append(values)
        
        return combinations
    
    def _get_min_value_for_attr(self, attr_name: str, model: DSLModel) -> Optional[Any]:
        """Get minimum value for an attribute from the model."""
        for entity in model.entities:
            for attr in entity.attributes:
                full_name = f"{entity.name.lower()}_{attr.name}"
                if full_name == attr_name:
                    return attr.min_value
        return None
    
    def _get_max_value_for_attr(self, attr_name: str, model: DSLModel) -> Optional[Any]:
        """Get maximum value for an attribute from the model."""
        for entity in model.entities:
            for attr in entity.attributes:
                full_name = f"{entity.name.lower()}_{attr.name}"
                if full_name == attr_name:
                    return attr.max_value
        return None
    
    def _sanitize_name(self, name: str) -> str:
        """Convert a name to a valid test name."""
        # Replace spaces and special characters with underscores
        sanitized = re.sub(r'[^a-zA-Z0-9]+', '_', name.lower())
        # Remove leading/trailing underscores
        return sanitized.strip('_')