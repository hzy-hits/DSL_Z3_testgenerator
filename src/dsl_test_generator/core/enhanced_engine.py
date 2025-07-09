"""Enhanced DSL test generation engine with full test coverage."""

from typing import List, Dict, Any, Optional

from .engine import DSLEngine
from .z3_solver import Z3Solver
from .constraint_translator import ConstraintTranslator
from ..generators.smart_test_generator import SmartTestGenerator
from ..types import DSLModel
from ..config import DSLEngineConfig, default_config


class EnhancedDSLEngine(DSLEngine):
    """Enhanced engine that generates comprehensive test suites including negative tests."""
    
    def __init__(self, config: Optional[DSLEngineConfig] = None):
        """Initialize enhanced engine with smart test generator."""
        super().__init__(config)
        # Replace the standard generator with smart one
        self.test_generator = SmartTestGenerator(self.config)
    
    def generate_tests(self, model: DSLModel) -> List[Dict[str, Any]]:
        """Generate comprehensive test cases from DSL model."""
        # Reset solver
        self.solver = Z3Solver(self.config)
        
        # Create variables
        self.solver.create_variables(model)
        
        # Create translator
        translator = ConstraintTranslator(
            self.solver.variables,
            self.solver.array_vars,
            self.solver.set_vars,
            self.config
        )
        
        # Add constraints (but allow them to be violated for negative tests)
        for constraint in model.constraints:
            z3_constraint = translator.translate_constraint(constraint)
            if z3_constraint is not None:
                self.solver.add_constraint(z3_constraint)
        
        # Add rules
        for rule in model.rules:
            z3_rule = translator.translate_rule(rule)
            if z3_rule is not None:
                self.solver.add_constraint(z3_rule)
        
        # Generate comprehensive test suite
        test_cases = self.test_generator.generate_comprehensive_test_suite(
            self.solver, model, translator
        )
        
        # Validate and fix test cases if business logic validation is enabled
        if self.config.test_generation.validate_business_logic:
            from ..validators import BusinessLogicValidator
            validator = BusinessLogicValidator(model, self.config)
            test_cases = validator.validate_test_suite(test_cases)
        
        return test_cases
    
    def generate_tests_with_extended_ranges(self, model: DSLModel) -> List[Dict[str, Any]]:
        """Generate tests with temporarily extended attribute ranges for negative tests."""
        # Create a copy of the model with extended ranges
        extended_model = self._extend_model_ranges(model)
        
        # Generate tests with extended model
        return self.generate_tests(extended_model)
    
    def _extend_model_ranges(self, model: DSLModel) -> DSLModel:
        """Create a copy of the model with SLIGHTLY extended attribute ranges for negative tests."""
        import copy
        extended_model = copy.deepcopy(model)
        
        # Only slightly extend ranges to allow just outside boundary tests
        for entity in extended_model.entities:
            for attr in entity.attributes:
                if attr.type.value == "integer":
                    # Only extend by small amounts for realistic negative tests
                    if attr.min_value is not None:
                        # Allow testing just below minimum
                        attr.min_value = attr.min_value - self.config.test_generation.negative_test_integer_extension
                    if attr.max_value is not None:
                        # Allow testing just above maximum
                        attr.max_value = attr.max_value + self.config.test_generation.negative_test_integer_extension
                
                elif attr.type.value == "real":
                    # Similar small extensions for real numbers
                    if attr.min_value is not None:
                        attr.min_value = attr.min_value - self.config.test_generation.negative_test_real_extension
                    if attr.max_value is not None:
                        attr.max_value = attr.max_value + self.config.test_generation.negative_test_real_extension
        
        return extended_model