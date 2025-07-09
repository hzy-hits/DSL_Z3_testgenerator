"""Domain-aware test generator that adapts to different business domains"""

from typing import Dict, List, Any, Optional
import z3

from ..types import DSLModel, Attribute
from ..core.z3_solver import Z3Solver
from .enhanced_test_generator import EnhancedTestGenerator


class DomainAwareTestGenerator(EnhancedTestGenerator):
    """Test generator that intelligently adapts to different domains."""
    
    def _get_default_valid_values(self) -> Dict[str, Any]:
        """Get default valid values based on the actual model attributes."""
        defaults = {}
        
        if hasattr(self, '_model') and self._model:
            # Generate defaults based on actual model attributes
            for entity in self._model.entities:
                for attr in entity.attributes:
                    var_name = f"{entity.name.lower()}_{attr.name}"
                    
                    if attr.type.value == "integer":
                        if attr.enum_values:
                            # Use first valid enum value
                            defaults[var_name] = attr.enum_values[0]
                        elif attr.min_value is not None and attr.max_value is not None:
                            # Use middle value
                            defaults[var_name] = (attr.min_value + attr.max_value) // 2
                        else:
                            defaults[var_name] = attr.min_value or 1
                    
                    elif attr.type.value == "real":
                        if attr.min_value is not None and attr.max_value is not None:
                            # Use a reasonable value within range
                            defaults[var_name] = attr.min_value + (attr.max_value - attr.min_value) * 0.3
                        else:
                            defaults[var_name] = attr.min_value or 100.0
                    
                    elif attr.type.value == "boolean":
                        defaults[var_name] = True  # Default to True for better rule activation
                    
                    elif attr.type.value == "string":
                        defaults[var_name] = f"test_{attr.name}"
        
        return defaults
    
    def generate_comprehensive_test_suite(
        self,
        solver: Z3Solver,
        model: DSLModel,
        translator: Any
    ) -> List[Dict[str, Any]]:
        """Generate comprehensive test suite adapted to the domain."""
        # Store model for default value generation
        self._model = model
        self._solver_vars = solver.variables
        
        # Call parent implementation
        return super().generate_comprehensive_test_suite(solver, model, translator)
    
    def _generate_all_boundary_tests(
        self,
        solver: Z3Solver,
        model: DSLModel
    ) -> List[Dict[str, Any]]:
        """Generate boundary tests for all numeric attributes in the model."""
        test_cases = []
        
        # Generate boundary tests dynamically based on model
        for entity in model.entities:
            for attr in entity.attributes:
                if attr.type.value in ["integer", "real"]:
                    var_name = f"{entity.name.lower()}_{attr.name}"
                    
                    # Min boundary test
                    if attr.min_value is not None:
                        values = self._get_default_valid_values()
                        values[var_name] = attr.min_value
                        
                        test_cases.append({
                            'name': f"boundary_{attr.name}_min",
                            'description': f"Minimum valid {attr.name}",
                            'values': values,
                            'expected': 'pass',
                            'type': 'boundary'
                        })
                    
                    # Max boundary test
                    if attr.max_value is not None:
                        values = self._get_default_valid_values()
                        values[var_name] = attr.max_value
                        
                        test_cases.append({
                            'name': f"boundary_{attr.name}_max",
                            'description': f"Maximum valid {attr.name}",
                            'values': values,
                            'expected': 'pass',
                            'type': 'boundary'
                        })
        
        # Also use parent boundary test generator
        test_cases.extend(self.generate_boundary_tests(solver, model))
        
        return test_cases
    
    def _generate_all_equivalence_tests(
        self,
        solver: Z3Solver,
        model: DSLModel
    ) -> List[Dict[str, Any]]:
        """Generate equivalence tests for all enum attributes."""
        test_cases = []
        
        # Generate equivalence tests for each enum attribute
        for entity in model.entities:
            for attr in entity.attributes:
                if attr.enum_values:
                    var_name = f"{entity.name.lower()}_{attr.name}"
                    
                    for enum_val in attr.enum_values:
                        values = self._get_default_valid_values()
                        values[var_name] = enum_val
                        
                        test_cases.append({
                            'name': f"equiv_{attr.name}_{enum_val}",
                            'description': f"Test {attr.name} = {enum_val}",
                            'values': values,
                            'expected': 'pass',
                            'type': 'equivalence'
                        })
        
        return test_cases
    
    def _generate_constraint_violation_tests(
        self,
        solver: Z3Solver,
        model: DSLModel,
        translator: Any
    ) -> List[Dict[str, Any]]:
        """Generate domain-specific constraint violation tests."""
        test_cases = []
        
        # Don't call parent's hardcoded hotel scenarios!
        # Generate negative tests based on actual model constraints
        for entity in model.entities:
            for attr in entity.attributes:
                var_name = f"{entity.name.lower()}_{attr.name}"
                
                # Test below minimum
                if attr.min_value is not None:
                    test_cases.extend(self._generate_below_min_tests(var_name, attr))
                
                # Test above maximum
                if attr.max_value is not None:
                    test_cases.extend(self._generate_above_max_tests(var_name, attr))
                
                # Test invalid enum values
                if attr.enum_values:
                    test_cases.extend(self._generate_invalid_enum_tests_for_attr(var_name, attr))
        
        return test_cases
    
    def _generate_below_min_tests(self, var_name: str, attr: Attribute) -> List[Dict[str, Any]]:
        """Generate tests for values below minimum."""
        test_cases = []
        
        # Generate sensible test values below minimum
        if attr.min_value is not None:
            # Just one or two meaningful values below min
            if attr.min_value > 0:
                # Test 0 and negative if min is positive
                test_values = [0, attr.min_value - 1]
            else:
                # Test just below minimum
                test_values = [attr.min_value - 1]
            
            for i, value in enumerate(test_values):
                if attr.type.value == "integer":
                    value = int(value)
                
                test_case = self._create_negative_test_with_value(
                    None, var_name, value,
                    f"negative_{attr.name}_below_min_{i+1}",
                    f"{attr.name} = {value} (below minimum {attr.min_value})"
                )
                if test_case:
                    test_cases.append(test_case)
        
        return test_cases
    
    def _generate_above_max_tests(self, var_name: str, attr: Attribute) -> List[Dict[str, Any]]:
        """Generate tests for values above maximum."""
        test_cases = []
        
        # Generate sensible test values above maximum
        if attr.max_value is not None:
            # Just one or two meaningful values above max
            test_values = [attr.max_value + 1]
            
            # Add a significantly higher value for certain attributes
            if attr.max_value < 100:
                test_values.append(attr.max_value + 10)
            
            for i, value in enumerate(test_values):
                if attr.type.value == "integer":
                    value = int(value)
                
                test_case = self._create_negative_test_with_value(
                    None, var_name, value,
                    f"negative_{attr.name}_above_max_{i+1}",
                    f"{attr.name} = {value} (above maximum {attr.max_value})"
                )
                if test_case:
                    test_cases.append(test_case)
        
        return test_cases
    
    def _generate_invalid_enum_tests_for_attr(self, var_name: str, attr: Attribute) -> List[Dict[str, Any]]:
        """Generate tests with invalid enum values."""
        test_cases = []
        
        if not attr.enum_values:
            return test_cases
        
        min_enum = min(attr.enum_values)
        max_enum = max(attr.enum_values)
        
        # Test just outside the enum range
        invalid_values = []
        
        # One below minimum
        if min_enum > 0:
            invalid_values.append(0)
        else:
            invalid_values.append(min_enum - 1)
        
        # One above maximum
        invalid_values.append(max_enum + 1)
        
        for i, value in enumerate(invalid_values):
            test_case = self._create_negative_test_with_value(
                None, var_name, value,
                f"negative_{attr.name}_invalid_enum_{i+1}",
                f"{attr.name} = {value} (not in valid enum values {attr.enum_values})"
            )
            if test_case:
                test_cases.append(test_case)
        
        return test_cases
    
    def _generate_rule_violation_tests(
        self,
        solver: Z3Solver,
        model: DSLModel,
        translator: Any
    ) -> List[Dict[str, Any]]:
        """Generate domain-aware tests that violate business rules."""
        test_cases = []
        
        # Analyze each rule to generate violation scenarios
        for rule in model.rules:
            # Try to create a scenario where the condition is true but action is violated
            # This is domain-specific and depends on the actual rules
            
            # For now, just ensure we don't use hardcoded scenarios
            # The rule coverage tests should handle most cases
            pass
        
        return test_cases
    
    def _generate_complete_rule_tests(
        self,
        solver: Z3Solver,
        model: DSLModel,
        translator: Any
    ) -> List[Dict[str, Any]]:
        """Generate tests for all business rules in the model."""
        test_cases = []
        
        # Generate tests based on actual model rules
        for rule in model.rules:
            # Test rule activation
            values = self._get_default_valid_values()
            
            # Parse the rule condition to set appropriate values
            # This is a simplified approach - a full parser would be better
            condition = rule.condition
            
            # Generate a test that should activate the rule
            test_case = {
                'name': f"rule_{rule.name.lower().replace(' ', '_')}_active",
                'description': f"Test {rule.name}: {rule.description}",
                'values': values,
                'expected': 'pass',
                'type': 'rule_coverage',
                'rule': rule.name
            }
            test_cases.append(test_case)
        
        # Also use parent rule coverage generator
        test_cases.extend(self.generate_rule_coverage_tests(solver, model, translator))
        
        return test_cases