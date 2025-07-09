"""Main test case generator."""

from typing import Dict, List, Any, Optional
import z3

from ..types import DSLModel, DSLType, Attribute
from ..core.z3_solver import Z3Solver
from ..core.constraint_translator import ConstraintTranslator
from .collection_generator import CollectionTestGenerator
from ..config import DSLEngineConfig, default_config


class TestCaseGenerator:
    """Generate various types of test cases."""
    
    def __init__(self, config: Optional[DSLEngineConfig] = None):
        self.config = config or default_config
        self.collection_generator = CollectionTestGenerator()
    
    def generate_boundary_tests(
        self,
        solver: Z3Solver,
        model: DSLModel,
        focus: Optional[List[str]] = None
    ) -> List[Dict[str, Any]]:
        """Generate boundary value test cases."""
        test_cases = []
        
        # Get all attributes with their entity context
        for entity in model.entities:
            for attr in entity.attributes:
                # Check if this attribute should be tested
                if focus and attr.name not in focus:
                    continue
                
                # Use full variable name as used in solver
                var_name = f"{entity.name.lower()}_{attr.name}"
                
                if attr.type in (DSLType.INTEGER, DSLType.REAL):
                    # Min value test
                    if attr.min_value is not None:
                        test_cases.append(
                            self._generate_with_constraint(
                                solver,
                                f"{attr.name}_min_boundary",
                                {var_name: attr.min_value}
                            )
                        )
                    
                    # Max value test
                    if attr.max_value is not None:
                        test_cases.append(
                            self._generate_with_constraint(
                                solver,
                                f"{attr.name}_max_boundary",
                                {var_name: attr.max_value}
                            )
                        )
        
        return [tc for tc in test_cases if tc is not None]
    
    def generate_equivalence_tests(
        self,
        solver: Z3Solver,
        model: DSLModel,
        focus: Optional[List[str]] = None
    ) -> List[Dict[str, Any]]:
        """Generate equivalence class test cases."""
        test_cases = []
        
        # Get all attributes with their entity context
        for entity in model.entities:
            for attr in entity.attributes:
                # Check if this attribute should be tested
                if focus and attr.name not in focus:
                    continue
                
                # Use full variable name as used in solver
                var_name = f"{entity.name.lower()}_{attr.name}"
                
                if attr.enum_values:
                    # Test each enum value
                    for value in attr.enum_values:
                        test_cases.append(
                            self._generate_with_constraint(
                                solver,
                                f"{attr.name}_enum_{value}",
                                {var_name: value}
                            )
                        )
                elif attr.type in (DSLType.INTEGER, DSLType.REAL):
                    # Test typical values
                    if attr.min_value is not None and attr.max_value is not None:
                        mid_value = (attr.min_value + attr.max_value) // 2
                        test_cases.append(
                            self._generate_with_constraint(
                                solver,
                                f"{attr.name}_typical",
                                {var_name: mid_value}
                            )
                        )
        
        return [tc for tc in test_cases if tc is not None]
    
    def generate_negative_tests(
        self,
        solver: Z3Solver,
        model: DSLModel,
        translator: ConstraintTranslator,
        focus: Optional[List[str]] = None
    ) -> List[Dict[str, Any]]:
        """Generate negative test cases that violate constraints."""
        test_cases = []
        
        # For each constraint, try to violate it
        for i, constraint in enumerate(model.constraints):
            z3_constraint = translator.translate_constraint(constraint)
            if z3_constraint is None:
                continue
            
            # Temporarily negate the constraint
            solver.push()
            solver.add_constraint(z3.Not(z3_constraint))
            
            if solver.check():
                model_values = solver.get_model()
                values = solver.extract_values(model_values)
                
                test_cases.append({
                    'name': f'negative_constraint_{i}',
                    'description': f'Violates: {constraint.expression}',
                    'values': values,
                    'expected': 'fail',
                    'type': 'negative'
                })
            
            solver.pop()
        
        return test_cases
    
    def generate_rule_coverage_tests(
        self,
        solver: Z3Solver,
        model: DSLModel,
        translator: ConstraintTranslator
    ) -> List[Dict[str, Any]]:
        """Generate tests to cover all rules."""
        test_cases = []
        
        for rule in model.rules:
            # Test rule activation
            condition = translator._parse_expression(rule.condition)
            
            solver.push()
            solver.add_constraint(condition)
            
            if solver.check():
                model_values = solver.get_model()
                values = solver.extract_values(model_values)
                
                test_cases.append({
                    'name': f'rule_{rule.name}_activated',
                    'description': f'Activates rule: {rule.name}',
                    'values': values,
                    'expected': 'pass',
                    'type': 'rule_coverage',
                    'rule': rule.name
                })
            
            solver.pop()
            
            # Test rule not activated
            solver.push()
            solver.add_constraint(z3.Not(condition))
            
            if solver.check():
                model_values = solver.get_model()
                values = solver.extract_values(model_values)
                
                test_cases.append({
                    'name': f'rule_{rule.name}_not_activated',
                    'description': f'Does not activate rule: {rule.name}',
                    'values': values,
                    'expected': 'pass',
                    'type': 'rule_coverage',
                    'rule': rule.name
                })
            
            solver.pop()
        
        return test_cases
    
    def generate_collection_tests(
        self,
        solver: Z3Solver,
        model: DSLModel,
        test_types: Optional[List[str]] = None
    ) -> List[Dict[str, Any]]:
        """Generate tests for collections."""
        if test_types is None:
            test_types = ["empty", "single", "multiple", "boundary"]
        
        return self.collection_generator.generate_collection_tests(
            solver, model, test_types
        )
    
    def generate_combinatorial_tests(
        self,
        solver: Z3Solver,
        model: DSLModel,
        strength: int = 2,
        focus: Optional[List[str]] = None
    ) -> List[Dict[str, Any]]:
        """Generate combinatorial test cases."""
        test_cases = []
        attributes = model.get_all_attributes()
        
        if focus:
            attributes = [a for a in attributes if a.name in focus]
        
        # For simplicity, generate pairwise combinations for boolean attributes
        bool_attrs = [a for a in attributes if a.type == DSLType.BOOLEAN]
        
        if len(bool_attrs) >= strength:
            from itertools import combinations, product
            
            for attr_combo in combinations(bool_attrs, strength):
                for value_combo in product([True, False], repeat=strength):
                    constraints = {}
                    for attr, value in zip(attr_combo, value_combo):
                        constraints[attr.name] = value
                    
                    test_case = self._generate_with_constraint(
                        solver,
                        f"combo_{'_'.join(a.name for a in attr_combo)}",
                        constraints
                    )
                    if test_case:
                        test_cases.append(test_case)
        
        return test_cases
    
    def _generate_with_constraint(
        self,
        solver: Z3Solver,
        name: str,
        constraints: Dict[str, Any]
    ) -> Optional[Dict[str, Any]]:
        """Generate test case with specific constraints."""
        solver.push()
        
        # Add specific constraints
        for var_name, value in constraints.items():
            if var_name in solver.variables:
                solver.add_constraint(solver.variables[var_name] == value)
        
        if solver.check():
            model = solver.get_model()
            values = solver.extract_values(model)
            
            solver.pop()
            return {
                'name': name,
                'values': values,
                'constraints': constraints,
                'expected': 'pass',
                'type': 'generated'
            }
        
        solver.pop()
        return None