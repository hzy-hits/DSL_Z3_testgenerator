"""Main DSL engine orchestrating test generation."""

from typing import Dict, List, Any, Optional
import itertools

from ..types import DSLModel, DSLType, TestRequirement
from ..generators import TestCaseGenerator
from .z3_solver import Z3Solver
from .constraint_translator import ConstraintTranslator
from ..config import DSLEngineConfig, default_config


class DSLEngine:
    """Main engine for DSL-based test generation."""
    
    def __init__(self, config: Optional[DSLEngineConfig] = None):
        self.config = config or default_config
        self.solver = Z3Solver(self.config)
        self.test_generator = TestCaseGenerator(self.config)
    
    def generate_tests(self, model: DSLModel) -> List[Dict[str, Any]]:
        """Generate comprehensive test cases from DSL model."""
        test_cases = []
        
        # Create variables
        self.solver.create_variables(model)
        
        # Create constraint translator
        translator = ConstraintTranslator(
            self.solver.variables,
            self.solver.array_vars,
            self.solver.set_vars,
            self.config
        )
        
        # Add constraints
        for constraint in model.constraints:
            z3_constraint = translator.translate_constraint(constraint)
            if z3_constraint is not None:
                self.solver.add_constraint(z3_constraint)
        
        # Add rules
        for rule in model.rules:
            z3_rule = translator.translate_rule(rule)
            if z3_rule is not None:
                self.solver.add_constraint(z3_rule)
        
        # Generate tests based on requirements
        if model.test_requirements:
            for req in model.test_requirements:
                cases = self._generate_for_requirement(req, model, translator)
                test_cases.extend(cases)
        else:
            # Default test generation strategy
            test_cases.extend(self._generate_boundary_tests(model))
            test_cases.extend(self._generate_rule_coverage_tests(model, translator))
            test_cases.extend(self._generate_collection_tests(model))
        
        # Validate and fix test cases if business logic validation is enabled
        if self.config.test_generation.validate_business_logic:
            from ..validators import BusinessLogicValidator
            validator = BusinessLogicValidator(model, self.config)
            test_cases = validator.validate_test_suite(test_cases)
        
        return self._deduplicate_tests(test_cases)
    
    def _generate_for_requirement(
        self, 
        req: TestRequirement, 
        model: DSLModel,
        translator: ConstraintTranslator
    ) -> List[Dict[str, Any]]:
        """Generate tests for specific requirement."""
        test_cases = []
        
        if req.type == "boundary":
            test_cases.extend(
                self.test_generator.generate_boundary_tests(
                    self.solver, model, req.focus
                )
            )
        elif req.type == "equivalence":
            test_cases.extend(
                self.test_generator.generate_equivalence_tests(
                    self.solver, model, req.focus
                )
            )
        elif req.type == "negative":
            test_cases.extend(
                self.test_generator.generate_negative_tests(
                    self.solver, model, translator, req.focus
                )
            )
        elif req.type == "collection":
            test_cases.extend(
                self.test_generator.generate_collection_tests(
                    self.solver, model, req.collection_tests
                )
            )
        elif req.type == "combinatorial":
            test_cases.extend(
                self.test_generator.generate_combinatorial_tests(
                    self.solver, model, req.combinations or 2, req.focus
                )
            )
        
        return test_cases
    
    def _generate_boundary_tests(self, model: DSLModel) -> List[Dict[str, Any]]:
        """Generate boundary value tests."""
        return self.test_generator.generate_boundary_tests(self.solver, model)
    
    def _generate_rule_coverage_tests(
        self, 
        model: DSLModel,
        translator: ConstraintTranslator
    ) -> List[Dict[str, Any]]:
        """Generate tests to cover all rules."""
        return self.test_generator.generate_rule_coverage_tests(
            self.solver, model, translator
        )
    
    def _generate_collection_tests(self, model: DSLModel) -> List[Dict[str, Any]]:
        """Generate tests for collection attributes."""
        collection_attrs = model.get_collection_attributes()
        if not collection_attrs:
            return []
        
        return self.test_generator.generate_collection_tests(
            self.solver, model, self.config.test_generation.collection_test_scenarios[:3]
        )
    
    def _deduplicate_tests(self, test_cases: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """Remove duplicate test cases while preserving test diversity."""
        seen = set()
        unique_tests = []
        
        for test in test_cases:
            # Include test type and name in the key to preserve different test purposes
            test_type = test.get('type', 'unknown')
            test_name = test.get('name', '')
            
            # For combinatorial tests, include the test name to preserve variations
            if test_type == 'combination' or 'combo' in test_name:
                # Use name as part of the key to keep all combinations
                test_key = (test_name, test_type)
            else:
                # For other tests, deduplicate based on values
                values_key = tuple(sorted(
                    (k, tuple(v) if isinstance(v, list) else v)
                    for k, v in test.get('values', {}).items()
                ))
                test_key = (values_key, test_type)
            
            if test_key not in seen:
                seen.add(test_key)
                unique_tests.append(test)
        
        return unique_tests