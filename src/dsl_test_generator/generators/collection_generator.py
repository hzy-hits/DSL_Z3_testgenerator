"""Specialized generator for collection test cases."""

from typing import Dict, List, Any, Optional
import z3

from ..types import DSLModel, DSLType
from ..core.z3_solver import Z3Solver


class CollectionTestGenerator:
    """Generate test cases for array and set types."""
    
    def generate_collection_tests(
        self,
        solver: Z3Solver,
        model: DSLModel,
        test_types: List[str]
    ) -> List[Dict[str, Any]]:
        """Generate various collection test cases."""
        test_cases = []
        collection_attrs = model.get_collection_attributes()
        
        for attr in collection_attrs:
            entity_name = None
            for entity in model.entities:
                if attr in entity.attributes:
                    entity_name = entity.name.lower()
                    break
            
            if not entity_name:
                continue
            
            var_name = f"{entity_name}_{attr.name}"
            
            if "empty" in test_types:
                test_cases.append(
                    self._generate_empty_collection(solver, var_name, attr)
                )
            
            if "single" in test_types:
                test_cases.append(
                    self._generate_single_element(solver, var_name, attr)
                )
            
            if "multiple" in test_types:
                test_cases.append(
                    self._generate_multiple_elements(solver, var_name, attr)
                )
            
            if "boundary" in test_types and attr.collection_info:
                if attr.collection_info.max_size:
                    test_cases.append(
                        self._generate_max_size(solver, var_name, attr)
                    )
            
            if "duplicates" in test_types and attr.type == DSLType.ARRAY:
                test_cases.append(
                    self._generate_with_duplicates(solver, var_name, attr)
                )
        
        return [tc for tc in test_cases if tc is not None]
    
    def _generate_empty_collection(
        self,
        solver: Z3Solver,
        var_name: str,
        attr
    ) -> Optional[Dict[str, Any]]:
        """Generate empty collection test."""
        solver.push()
        
        size_var = f"{var_name}_size"
        if size_var in solver.variables:
            solver.add_constraint(solver.variables[size_var] == 0)
        
        if solver.check():
            model = solver.get_model()
            values = solver.extract_values(model)
            
            solver.pop()
            return {
                'name': f'{var_name}_empty',
                'description': f'Empty {attr.type.value}',
                'values': values,
                'expected': 'pass',
                'type': 'collection_empty'
            }
        
        solver.pop()
        return None
    
    def _generate_single_element(
        self,
        solver: Z3Solver,
        var_name: str,
        attr
    ) -> Optional[Dict[str, Any]]:
        """Generate single element collection test."""
        solver.push()
        
        size_var = f"{var_name}_size"
        if size_var in solver.variables:
            solver.add_constraint(solver.variables[size_var] == 1)
        
        if solver.check():
            model = solver.get_model()
            values = solver.extract_values(model)
            
            solver.pop()
            return {
                'name': f'{var_name}_single',
                'description': f'Single element {attr.type.value}',
                'values': values,
                'expected': 'pass',
                'type': 'collection_single'
            }
        
        solver.pop()
        return None
    
    def _generate_multiple_elements(
        self,
        solver: Z3Solver,
        var_name: str,
        attr
    ) -> Optional[Dict[str, Any]]:
        """Generate multiple elements collection test."""
        solver.push()
        
        size_var = f"{var_name}_size"
        if size_var in solver.variables:
            # Use 3 elements as a reasonable default
            target_size = 3
            if attr.collection_info and attr.collection_info.max_size:
                target_size = min(3, attr.collection_info.max_size)
            
            solver.add_constraint(solver.variables[size_var] == target_size)
        
        if solver.check():
            model = solver.get_model()
            values = solver.extract_values(model)
            
            solver.pop()
            return {
                'name': f'{var_name}_multiple',
                'description': f'Multiple elements {attr.type.value}',
                'values': values,
                'expected': 'pass',
                'type': 'collection_multiple'
            }
        
        solver.pop()
        return None
    
    def _generate_max_size(
        self,
        solver: Z3Solver,
        var_name: str,
        attr
    ) -> Optional[Dict[str, Any]]:
        """Generate max size collection test."""
        if not attr.collection_info or not attr.collection_info.max_size:
            return None
        
        solver.push()
        
        size_var = f"{var_name}_size"
        if size_var in solver.variables:
            solver.add_constraint(
                solver.variables[size_var] == attr.collection_info.max_size
            )
        
        if solver.check():
            model = solver.get_model()
            values = solver.extract_values(model)
            
            solver.pop()
            return {
                'name': f'{var_name}_max_size',
                'description': f'Maximum size {attr.type.value}',
                'values': values,
                'expected': 'pass',
                'type': 'collection_boundary'
            }
        
        solver.pop()
        return None
    
    def _generate_with_duplicates(
        self,
        solver: Z3Solver,
        var_name: str,
        attr
    ) -> Optional[Dict[str, Any]]:
        """Generate array with duplicate elements."""
        if attr.type != DSLType.ARRAY:
            return None
        
        solver.push()
        
        size_var = f"{var_name}_size"
        if size_var in solver.variables and var_name in solver.array_vars:
            solver.add_constraint(solver.variables[size_var] >= 2)
            
            # Force first two elements to be equal
            array = solver.array_vars[var_name]
            solver.add_constraint(array[0] == array[1])
        
        if solver.check():
            model = solver.get_model()
            values = solver.extract_values(model)
            
            solver.pop()
            return {
                'name': f'{var_name}_duplicates',
                'description': f'Array with duplicate elements',
                'values': values,
                'expected': 'pass',
                'type': 'collection_duplicates'
            }
        
        solver.pop()
        return None