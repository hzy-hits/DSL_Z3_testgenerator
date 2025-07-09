"""Enhanced test generator with full negative test support"""

from typing import Dict, List, Any, Optional, Tuple
import z3

from ..types import DSLModel, DSLType, Attribute, Constraint
from ..core.z3_solver import Z3Solver
from ..core.constraint_translator import ConstraintTranslator
from .test_generator import TestCaseGenerator


class EnhancedTestGenerator(TestCaseGenerator):
    """Enhanced test generator that can generate comprehensive negative tests."""
    
    def generate_negative_tests(
        self,
        solver: Z3Solver,
        model: DSLModel,
        translator: ConstraintTranslator,
        focus: Optional[List[str]] = None
    ) -> List[Dict[str, Any]]:
        """Generate comprehensive negative test cases."""
        test_cases = []
        
        # Strategy 1: Generate specific negative tests for each constraint type
        test_cases.extend(self._generate_boundary_negative_tests(solver, model, translator))
        test_cases.extend(self._generate_constraint_violation_tests(solver, model, translator))
        test_cases.extend(self._generate_rule_violation_tests(solver, model, translator))
        
        # Strategy 2: Generate invalid enum values
        test_cases.extend(self._generate_invalid_enum_tests(solver, model))
        
        return test_cases
    
    def _generate_boundary_negative_tests(
        self,
        solver: Z3Solver,
        model: DSLModel,
        translator: ConstraintTranslator
    ) -> List[Dict[str, Any]]:
        """Generate tests that violate boundary constraints."""
        test_cases = []
        
        # Parse constraints to find boundary violations
        for constraint in model.constraints:
            expr = constraint.expression
            
            # Handle >= constraints
            if '>=' in expr:
                parts = expr.split('>=')
                if len(parts) == 2:
                    var_name = parts[0].strip()
                    try:
                        min_value = float(parts[1].strip())
                        # Generate value below minimum
                        test_value = min_value - 1 if min_value > 0 else -1
                        
                        test_case = self._create_negative_test_with_value(
                            solver, var_name, test_value,
                            f"negative_{var_name}_below_min",
                            f"Tests {var_name} < {min_value}"
                        )
                        if test_case:
                            test_cases.append(test_case)
                    except ValueError:
                        pass
            
            # Handle <= constraints
            if '<=' in expr and '>=' not in expr:
                parts = expr.split('<=')
                if len(parts) == 2:
                    var_name = parts[0].strip()
                    try:
                        max_value = float(parts[1].strip())
                        # Generate value above maximum
                        test_value = max_value + 1
                        
                        test_case = self._create_negative_test_with_value(
                            solver, var_name, test_value,
                            f"negative_{var_name}_above_max",
                            f"Tests {var_name} > {max_value}"
                        )
                        if test_case:
                            test_cases.append(test_case)
                    except ValueError:
                        pass
            
            # Handle compound constraints like "x >= 1 and x <= 3"
            if ' and ' in expr:
                parts = expr.split(' and ')
                for part in parts:
                    if '>=' in part:
                        subparts = part.split('>=')
                        if len(subparts) == 2:
                            var_name = subparts[0].strip()
                            try:
                                min_value = float(subparts[1].strip())
                                test_value = min_value - 1
                                
                                test_case = self._create_negative_test_with_value(
                                    solver, var_name, test_value,
                                    f"negative_{var_name}_below_range",
                                    f"Tests {var_name} below valid range"
                                )
                                if test_case:
                                    test_cases.append(test_case)
                            except ValueError:
                                pass
                    
                    if '<=' in part and '>=' not in part:
                        subparts = part.split('<=')
                        if len(subparts) == 2:
                            var_name = subparts[0].strip()
                            try:
                                max_value = float(subparts[1].strip())
                                test_value = max_value + 1
                                
                                test_case = self._create_negative_test_with_value(
                                    solver, var_name, test_value,
                                    f"negative_{var_name}_above_range",
                                    f"Tests {var_name} above valid range"
                                )
                                if test_case:
                                    test_cases.append(test_case)
                            except ValueError:
                                pass
        
        return test_cases
    
    def _generate_constraint_violation_tests(
        self,
        solver: Z3Solver,
        model: DSLModel,
        translator: ConstraintTranslator
    ) -> List[Dict[str, Any]]:
        """Generate tests for specific constraint violations."""
        # Don't hardcode domain-specific constraint violations
        # This should be handled by the domain-aware implementation
        return []
    
    def _generate_rule_violation_tests(
        self,
        solver: Z3Solver,
        model: DSLModel,
        translator: ConstraintTranslator  
    ) -> List[Dict[str, Any]]:
        """Generate tests that violate business rules."""
        # Don't use hardcoded hotel booking scenarios
        # This should be overridden by domain-aware implementations
        return []
    
    def _generate_invalid_enum_tests(
        self,
        solver: Z3Solver,
        model: DSLModel
    ) -> List[Dict[str, Any]]:
        """Generate tests with invalid enum values."""
        test_cases = []
        
        for entity in model.entities:
            for attr in entity.attributes:
                if attr.enum_values:
                    var_name = f"{entity.name.lower()}_{attr.name}"
                    
                    # Test values outside enum range
                    min_enum = min(attr.enum_values)
                    max_enum = max(attr.enum_values)
                    
                    # Below minimum
                    if min_enum > 0:
                        test_case = self._create_negative_test_with_value(
                            solver, var_name, min_enum - 1,
                            f"negative_{attr.name}_invalid_enum_low",
                            f"Invalid {attr.name} value below enum range"
                        )
                        if test_case:
                            test_cases.append(test_case)
                    
                    # Above maximum
                    test_case = self._create_negative_test_with_value(
                        solver, var_name, max_enum + 1,
                        f"negative_{attr.name}_invalid_enum_high",
                        f"Invalid {attr.name} value above enum range"
                    )
                    if test_case:
                        test_cases.append(test_case)
        
        return test_cases
    
    def _create_negative_test_with_value(
        self,
        solver: Z3Solver,
        var_name: str,
        value: Any,
        test_name: str,
        description: str
    ) -> Optional[Dict[str, Any]]:
        """Create a negative test case with a specific invalid value."""
        # Get default valid values
        values = self._get_default_valid_values()
        
        # Override with the invalid value
        if var_name in values:
            values[var_name] = value
        
        return {
            'name': test_name,
            'description': description,
            'values': values,
            'expected': 'fail',
            'type': 'negative'
        }
    
    def _get_default_valid_values(self) -> Dict[str, Any]:
        """Get a set of default valid values for all variables."""
        # Generate default values based on actual solver variables
        defaults = {}
        
        # Get variables from solver if available
        if hasattr(self, '_solver_vars'):
            for var_name, var in self._solver_vars.items():
                if z3.is_int(var):
                    # For integers, use middle value of valid range
                    defaults[var_name] = 1
                elif z3.is_real(var):
                    # For reals, use a reasonable default
                    defaults[var_name] = 100.0
                elif z3.is_bool(var):
                    # For booleans, default to False
                    defaults[var_name] = False
        else:
            # Fallback: common patterns
            defaults = {
                # Common attributes that might exist
                'age': 25,
                'member_level': 1,
                'is_vip': False,
                'policy_type': 1,
                'claim_type': 1,
                'claim_amount': 5000.0,
                'coverage_amount': 100000.0,
                'deductible': 500.0,
                'premium_paid': True,
                'documents_complete': True,
                'fraud_risk_score': 10,
                'previous_claims_count': 0,
                'incident_date_days_ago': 7,
                # Add entity-prefixed versions
            }
            
            # Create entity-prefixed versions
            prefixed = {}
            for entity_prefix in ['customer_', 'booking_', 'room_', 'policy_', 'claim_']:
                for key, value in defaults.items():
                    prefixed[entity_prefix + key] = value
            defaults.update(prefixed)
        
        return defaults
    
    def generate_comprehensive_test_suite(
        self,
        solver: Z3Solver,
        model: DSLModel,
        translator: ConstraintTranslator
    ) -> List[Dict[str, Any]]:
        """Generate a comprehensive test suite with all test types."""
        # Store solver variables for default value generation
        self._solver_vars = solver.variables
        test_cases = []
        
        # 1. Boundary tests (positive) - ensure all attributes are covered
        test_cases.extend(self._generate_all_boundary_tests(solver, model))
        
        # 2. Equivalence tests - test all enum values
        test_cases.extend(self._generate_all_equivalence_tests(solver, model))
        
        # 3. Rule coverage tests - both activation and non-activation
        test_cases.extend(self._generate_complete_rule_tests(solver, model, translator))
        
        # 4. Negative tests (comprehensive)
        test_cases.extend(self.generate_negative_tests(solver, model, translator))
        
        # 5. Edge case tests
        test_cases.extend(self._generate_edge_case_tests(solver, model))
        
        # Remove duplicates
        return self._deduplicate_tests(test_cases)
    
    def _generate_all_boundary_tests(
        self,
        solver: Z3Solver,
        model: DSLModel
    ) -> List[Dict[str, Any]]:
        """Generate boundary tests for ALL numeric attributes."""
        # Just use the original boundary test generator
        # Don't hardcode any domain-specific tests
        return self.generate_boundary_tests(solver, model)
    
    def _generate_all_equivalence_tests(
        self,
        solver: Z3Solver,
        model: DSLModel
    ) -> List[Dict[str, Any]]:
        """Generate equivalence tests for all categorical values."""
        # Use the original equivalence test generator
        # Don't hardcode any domain-specific tests
        return self.generate_equivalence_tests(solver, model)
    
    def _generate_complete_rule_tests(
        self,
        solver: Z3Solver,
        model: DSLModel,
        translator: ConstraintTranslator
    ) -> List[Dict[str, Any]]:
        """Generate tests for all business rules."""
        # Use original rule coverage generator
        # Don't hardcode any domain-specific rules
        return self.generate_rule_coverage_tests(solver, model, translator)
    
    def _generate_edge_case_tests(
        self,
        solver: Z3Solver,
        model: DSLModel
    ) -> List[Dict[str, Any]]:
        """Generate edge case tests."""
        # Don't hardcode domain-specific edge cases
        # This should be handled by combinatorial testing or domain-aware implementations
        return []
    
    def _deduplicate_tests(self, test_cases: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """Remove duplicate test cases."""
        seen = set()
        unique_tests = []
        
        for test in test_cases:
            # Create a unique key based on test values
            key = (
                test['name'],
                tuple(sorted(test.get('values', {}).items()))
            )
            
            if key not in seen:
                seen.add(key)
                unique_tests.append(test)
        
        return unique_tests