"""
Pairwise Testing Strategy for V2.0

Implements systematic combinatorial testing using pairwise (2-way) coverage.
This ensures all pairs of parameter values are tested at least once.
"""

from typing import List, Dict, Set, Tuple, Optional
from dataclasses import dataclass
from itertools import combinations, product
import logging

from ..core.models import (
    DSLModel, AttributeType, TestObjective, Attribute
)

logger = logging.getLogger(__name__)


@dataclass
class Parameter:
    """Parameter for pairwise testing"""
    name: str
    values: List[any]
    attribute: Attribute
    

@dataclass
class PairwiseTestCase:
    """A test case covering specific parameter pairs"""
    values: Dict[str, any]
    covered_pairs: Set[Tuple[str, any, str, any]]
    

class PairwiseTestPlanner:
    """
    Generates minimal test suite covering all parameter pairs.
    Based on the IPO (In-Parameter-Order) algorithm.
    """
    
    def __init__(self, model: DSLModel):
        self.model = model
        self.parameters = []
        self.test_cases = []
        
    def generate_pairwise_objectives(self, 
                                   focus_attributes: Optional[List[str]] = None,
                                   max_values_per_param: int = 3) -> List[TestObjective]:
        """
        Generate test objectives for pairwise coverage.
        
        Args:
            focus_attributes: Specific attributes to focus on (None = all)
            max_values_per_param: Maximum values to consider per parameter
            
        Returns:
            List of test objectives covering all pairs
        """
        # 1. Extract parameters and their values
        self._extract_parameters(focus_attributes, max_values_per_param)
        
        if len(self.parameters) < 2:
            logger.warning("Less than 2 parameters, pairwise testing not applicable")
            return []
            
        # 2. Generate all pairs that need coverage
        all_pairs = self._generate_all_pairs()
        logger.info(f"Total pairs to cover: {len(all_pairs)}")
        
        # 3. Build test cases using IPO algorithm
        test_cases = self._build_pairwise_test_suite(all_pairs)
        logger.info(f"Generated {len(test_cases)} test cases for pairwise coverage")
        
        # 4. Convert to test objectives
        objectives = []
        for i, test_case in enumerate(test_cases):
            objective = TestObjective(
                type="pairwise",
                target=f"pairwise_test_{i+1}",
                priority=8,  # High priority for combinatorial tests
                reason=f"Pairwise test covering {len(test_case.covered_pairs)} pairs",
                constraints=[f"{k} == {v}" for k, v in test_case.values.items()]
            )
            objectives.append(objective)
            
        return objectives
        
    def _extract_parameters(self, focus_attributes: Optional[List[str]], max_values: int):
        """Extract parameters and their representative values"""
        self.parameters = []
        
        attributes = self.model.get_all_attributes()
        if focus_attributes:
            attributes = [a for a in attributes if a.full_name in focus_attributes]
            
        for attr in attributes:
            values = self._get_parameter_values(attr, max_values)
            if len(values) > 1:  # Only include if multiple values
                self.parameters.append(Parameter(
                    name=attr.full_name,
                    values=values,
                    attribute=attr
                ))
                
    def _get_parameter_values(self, attr: Attribute, max_values: int) -> List[any]:
        """Get representative values for an attribute"""
        values = []
        
        if attr.enum_values:
            # For enums, use all values (up to max)
            values = attr.enum_values[:max_values]
            
        elif attr.type == AttributeType.BOOLEAN:
            values = [True, False]
            
        elif attr.type in [AttributeType.INTEGER, AttributeType.REAL]:
            # For numeric types, use boundary + middle values
            if attr.min_value is not None and attr.max_value is not None:
                values.append(attr.min_value)
                if max_values > 2:
                    # Add middle value
                    middle = (attr.min_value + attr.max_value) / 2
                    if attr.type == AttributeType.INTEGER:
                        middle = int(middle)
                    values.append(middle)
                values.append(attr.max_value)
            elif attr.min_value is not None:
                values = [attr.min_value, attr.min_value + 10]
            elif attr.max_value is not None:
                values = [attr.max_value - 10, attr.max_value]
            else:
                values = [0, 50, 100][:max_values]
                
        # Limit to max_values
        return values[:max_values]
        
    def _generate_all_pairs(self) -> Set[Tuple[str, any, str, any]]:
        """Generate all pairs that need to be covered"""
        all_pairs = set()
        
        # For each pair of parameters
        for i, param1 in enumerate(self.parameters):
            for j, param2 in enumerate(self.parameters[i+1:], i+1):
                # For each combination of their values
                for v1 in param1.values:
                    for v2 in param2.values:
                        pair = (param1.name, v1, param2.name, v2)
                        all_pairs.add(pair)
                        
        return all_pairs
        
    def _build_pairwise_test_suite(self, all_pairs: Set[Tuple]) -> List[PairwiseTestCase]:
        """Build minimal test suite covering all pairs using IPO algorithm"""
        uncovered_pairs = all_pairs.copy()
        test_cases = []
        
        # Initial test cases for first two parameters
        if len(self.parameters) >= 2:
            param1, param2 = self.parameters[:2]
            for v1 in param1.values:
                for v2 in param2.values:
                    test_case = PairwiseTestCase(
                        values={param1.name: v1, param2.name: v2},
                        covered_pairs=set()
                    )
                    # Update covered pairs
                    pair = (param1.name, v1, param2.name, v2)
                    test_case.covered_pairs.add(pair)
                    uncovered_pairs.discard(pair)
                    test_cases.append(test_case)
        
        # Extend with remaining parameters using IPO
        for param_idx in range(2, len(self.parameters)):
            param = self.parameters[param_idx]
            test_cases = self._extend_test_cases(test_cases, param, uncovered_pairs)
            
        # Add any remaining uncovered pairs
        while uncovered_pairs:
            # Create new test case for remaining pairs
            test_case = self._create_test_for_uncovered_pairs(uncovered_pairs)
            if test_case:
                test_cases.append(test_case)
            else:
                break  # No more pairs can be covered
                
        return test_cases
        
    def _extend_test_cases(self, test_cases: List[PairwiseTestCase], 
                          new_param: Parameter, 
                          uncovered_pairs: Set[Tuple]) -> List[PairwiseTestCase]:
        """Extend existing test cases with new parameter"""
        extended_cases = []
        
        for test_case in test_cases:
            # Find best value for new parameter that covers most uncovered pairs
            best_value = None
            best_coverage = set()
            
            for value in new_param.values:
                coverage = set()
                # Check which pairs this value would cover
                for existing_param, existing_value in test_case.values.items():
                    pair = (existing_param, existing_value, new_param.name, value)
                    reverse_pair = (new_param.name, value, existing_param, existing_value)
                    
                    if pair in uncovered_pairs:
                        coverage.add(pair)
                    elif reverse_pair in uncovered_pairs:
                        coverage.add(reverse_pair)
                        
                if len(coverage) > len(best_coverage):
                    best_value = value
                    best_coverage = coverage
                    
            # Extend test case with best value
            extended_case = PairwiseTestCase(
                values={**test_case.values, new_param.name: best_value},
                covered_pairs=test_case.covered_pairs.copy()
            )
            extended_case.covered_pairs.update(best_coverage)
            
            # Remove covered pairs from uncovered set
            for pair in best_coverage:
                uncovered_pairs.discard(pair)
                
            extended_cases.append(extended_case)
            
        return extended_cases
        
    def _create_test_for_uncovered_pairs(self, uncovered_pairs: Set[Tuple]) -> Optional[PairwiseTestCase]:
        """Create a new test case to cover remaining pairs"""
        if not uncovered_pairs:
            return None
            
        # Pick first uncovered pair
        first_pair = next(iter(uncovered_pairs))
        param1_name, value1, param2_name, value2 = first_pair
        
        # Create test case
        test_case = PairwiseTestCase(
            values={param1_name: value1, param2_name: value2},
            covered_pairs={first_pair}
        )
        uncovered_pairs.remove(first_pair)
        
        # Try to cover more pairs with other parameters
        for param in self.parameters:
            if param.name not in test_case.values:
                # Find value that covers most pairs
                best_value = param.values[0]
                best_coverage = set()
                
                for value in param.values:
                    coverage = set()
                    for existing_param, existing_value in test_case.values.items():
                        pair = (existing_param, existing_value, param.name, value)
                        reverse_pair = (param.name, value, existing_param, existing_value)
                        
                        if pair in uncovered_pairs:
                            coverage.add(pair)
                        elif reverse_pair in uncovered_pairs:
                            coverage.add(reverse_pair)
                            
                    if len(coverage) > len(best_coverage):
                        best_value = value
                        best_coverage = coverage
                        
                test_case.values[param.name] = best_value
                test_case.covered_pairs.update(best_coverage)
                
                for pair in best_coverage:
                    uncovered_pairs.discard(pair)
                    
        return test_case


class RuleCombinationAnalyzer:
    """Analyzes rule combinations for conflicts and interesting scenarios"""
    
    def __init__(self, model: DSLModel):
        self.model = model
        
    def analyze_rule_conflicts(self) -> List[Dict[str, any]]:
        """Find potential conflicts between rules"""
        conflicts = []
        
        for i, rule1 in enumerate(self.model.rules):
            for rule2 in self.model.rules[i+1:]:
                conflict = self._check_rule_conflict(rule1, rule2)
                if conflict:
                    conflicts.append(conflict)
                    
        return conflicts
        
    def _check_rule_conflict(self, rule1, rule2) -> Optional[Dict[str, any]]:
        """Check if two rules can conflict"""
        # Extract attributes from conditions and consequences
        rule1_attrs = self._extract_attributes(rule1.condition) | self._extract_attributes(rule1.consequence)
        rule2_attrs = self._extract_attributes(rule2.condition) | self._extract_attributes(rule2.consequence)
        
        # Check for shared attributes
        shared_attrs = rule1_attrs & rule2_attrs
        if not shared_attrs:
            return None
            
        # Simple conflict detection - if consequences set same attribute differently
        # This is a simplified version - real implementation would use Z3
        if shared_attrs:
            return {
                'rule1': rule1.name,
                'rule2': rule2.name,
                'shared_attributes': list(shared_attrs),
                'type': 'potential_conflict',
                'severity': 'medium'
            }
            
        return None
        
    def _extract_attributes(self, expression: str) -> Set[str]:
        """Extract attribute names from expression"""
        # Simple extraction - real implementation would use proper parsing
        attributes = set()
        for attr in self.model.get_all_attributes():
            if attr.full_name in expression:
                attributes.add(attr.full_name)
        return attributes