"""
Combination Engine for generating test parameter combinations
Supports full cartesian product and pairwise reduction
"""

import itertools
from typing import Dict, List, Any, Tuple, Set
from dataclasses import dataclass
from src.models.dsl_models import Model, Entity, Attribute, DSLType


@dataclass
class ParameterDomain:
    """Domain values for a parameter"""
    name: str
    values: List[Any]
    attribute: Attribute


@dataclass
class TestCombination:
    """A specific combination of parameter values"""
    values: Dict[str, Any]
    coverage_type: str  # 'full', 'pairwise', 'boundary'
    rationale: str


class CombinationEngine:
    """Generates parameter combinations for testing"""
    
    def __init__(self, model: Model):
        self.model = model
        
    def generate_combinations(self, entity: Entity, 
                            test_type: str = "combinatorial",
                            coverage_level: str = "pairwise") -> List[TestCombination]:
        """Generate test combinations based on requirements"""
        
        # Extract combinable parameters
        parameters = self._extract_combinable_parameters(entity)
        
        if not parameters:
            return []
        
        if coverage_level == "full":
            return self._generate_full_combinations(parameters)
        elif coverage_level == "pairwise":
            return self._generate_pairwise_combinations(parameters)
        else:
            return self._generate_minimal_combinations(parameters)
    
    def _extract_combinable_parameters(self, entity: Entity) -> List[ParameterDomain]:
        """Extract parameters suitable for combination testing"""
        parameters = []
        
        for attr in entity.attributes:
            if attr.type == DSLType.BOOLEAN:
                # Boolean parameters are perfect for combinations
                domain = ParameterDomain(
                    name=attr.name,
                    values=[True, False],
                    attribute=attr
                )
                parameters.append(domain)
                
            elif attr.type == DSLType.INTEGER and attr.min_value is not None and attr.max_value is not None:
                # For small integer ranges, include all values
                if attr.max_value - attr.min_value <= 5:
                    values = list(range(attr.min_value, attr.max_value + 1))
                else:
                    # For larger ranges, use boundary values and middle
                    values = [
                        attr.min_value,
                        attr.min_value + 1,
                        (attr.min_value + attr.max_value) // 2,
                        attr.max_value - 1,
                        attr.max_value
                    ]
                domain = ParameterDomain(
                    name=attr.name,
                    values=values,
                    attribute=attr
                )
                parameters.append(domain)
                
            elif attr.type in [DSLType.ARRAY, DSLType.SET] and attr.collection_info:
                # For collections, test different sizes
                values = []
                if attr.collection_info.min_size is not None:
                    values.append(attr.collection_info.min_size)
                if attr.collection_info.max_size is not None:
                    values.append(attr.collection_info.max_size)
                if len(values) < 2:
                    values.extend([0, 1, 3, 5])  # Common test sizes
                    
                domain = ParameterDomain(
                    name=f"{attr.name}_size",
                    values=sorted(list(set(values))),
                    attribute=attr
                )
                parameters.append(domain)
                
            elif attr.type == DSLType.STRING and attr.name.lower() in ["status", "state", "type"]:
                # Enumeration-like strings
                if "status" in attr.name.lower():
                    values = ["active", "inactive", "pending", "suspended"]
                elif "state" in attr.name.lower():
                    values = ["new", "in_progress", "completed", "failed"]
                else:
                    values = ["type_a", "type_b", "type_c"]
                    
                domain = ParameterDomain(
                    name=attr.name,
                    values=values[:3],  # Limit to 3 for combinations
                    attribute=attr
                )
                parameters.append(domain)
        
        return parameters
    
    def _generate_full_combinations(self, parameters: List[ParameterDomain]) -> List[TestCombination]:
        """Generate all possible combinations (Cartesian product)"""
        combinations = []
        
        # Extract value lists
        param_names = [p.name for p in parameters]
        param_values = [p.values for p in parameters]
        
        # Generate cartesian product
        for combo_values in itertools.product(*param_values):
            combo_dict = dict(zip(param_names, combo_values))
            
            # Create rationale
            rationale = f"Full combination: {', '.join(f'{k}={v}' for k, v in combo_dict.items())}"
            
            combination = TestCombination(
                values=combo_dict,
                coverage_type="full",
                rationale=rationale
            )
            combinations.append(combination)
        
        return combinations
    
    def _generate_pairwise_combinations(self, parameters: List[ParameterDomain]) -> List[TestCombination]:
        """Generate pairwise combinations using a greedy algorithm"""
        if len(parameters) < 2:
            return self._generate_full_combinations(parameters)
        
        combinations = []
        covered_pairs = set()
        
        # Track all pairs that need to be covered
        all_pairs = []
        for i in range(len(parameters)):
            for j in range(i + 1, len(parameters)):
                for val1 in parameters[i].values:
                    for val2 in parameters[j].values:
                        pair = (
                            (parameters[i].name, val1),
                            (parameters[j].name, val2)
                        )
                        all_pairs.append(pair)
        
        # Greedy algorithm to cover all pairs
        while len(covered_pairs) < len(all_pairs):
            best_combo = None
            best_new_pairs = 0
            
            # Try different combinations
            for _ in range(100):  # Limited attempts
                combo_dict = {}
                new_pairs = 0
                
                # Randomly select values
                for param in parameters:
                    import random
                    combo_dict[param.name] = random.choice(param.values)
                
                # Count new pairs covered
                for i in range(len(parameters)):
                    for j in range(i + 1, len(parameters)):
                        pair = (
                            (parameters[i].name, combo_dict[parameters[i].name]),
                            (parameters[j].name, combo_dict[parameters[j].name])
                        )
                        if pair not in covered_pairs:
                            new_pairs += 1
                
                if new_pairs > best_new_pairs:
                    best_combo = combo_dict
                    best_new_pairs = new_pairs
            
            if best_combo and best_new_pairs > 0:
                # Add this combination
                rationale = f"Pairwise combination covering {best_new_pairs} new pairs"
                combination = TestCombination(
                    values=best_combo,
                    coverage_type="pairwise",
                    rationale=rationale
                )
                combinations.append(combination)
                
                # Mark pairs as covered
                for i in range(len(parameters)):
                    for j in range(i + 1, len(parameters)):
                        pair = (
                            (parameters[i].name, best_combo[parameters[i].name]),
                            (parameters[j].name, best_combo[parameters[j].name])
                        )
                        covered_pairs.add(pair)
            else:
                break
        
        return combinations
    
    def _generate_minimal_combinations(self, parameters: List[ParameterDomain]) -> List[TestCombination]:
        """Generate minimal set of combinations for basic coverage"""
        combinations = []
        
        # Test 1: All minimum values
        min_combo = {}
        for param in parameters:
            min_combo[param.name] = param.values[0]
        
        combinations.append(TestCombination(
            values=min_combo,
            coverage_type="minimal",
            rationale="All parameters at minimum/first values"
        ))
        
        # Test 2: All maximum values
        max_combo = {}
        for param in parameters:
            max_combo[param.name] = param.values[-1]
        
        combinations.append(TestCombination(
            values=max_combo,
            coverage_type="minimal",
            rationale="All parameters at maximum/last values"
        ))
        
        # Test 3: Mixed values
        mixed_combo = {}
        for i, param in enumerate(parameters):
            # Alternate between min and max
            if i % 2 == 0:
                mixed_combo[param.name] = param.values[0]
            else:
                mixed_combo[param.name] = param.values[-1]
        
        combinations.append(TestCombination(
            values=mixed_combo,
            coverage_type="minimal",
            rationale="Mixed parameter values"
        ))
        
        return combinations
    
    def generate_boundary_combinations(self, entity: Entity) -> List[TestCombination]:
        """Generate combinations specifically for boundary testing"""
        combinations = []
        
        # Find attributes with boundaries
        boundary_attrs = []
        for attr in entity.attributes:
            if attr.type == DSLType.INTEGER and (attr.min_value is not None or attr.max_value is not None):
                boundary_attrs.append(attr)
            elif attr.is_collection() and attr.collection_info:
                if attr.collection_info.min_size is not None or attr.collection_info.max_size is not None:
                    boundary_attrs.append(attr)
        
        # Generate boundary combinations
        for attr in boundary_attrs:
            # Minimum boundary
            if attr.type == DSLType.INTEGER and attr.min_value is not None:
                combo = {attr.name: attr.min_value}
                combinations.append(TestCombination(
                    values=combo,
                    coverage_type="boundary",
                    rationale=f"Testing {attr.name} at minimum boundary ({attr.min_value})"
                ))
                
                # Just above minimum
                combo = {attr.name: attr.min_value + 1}
                combinations.append(TestCombination(
                    values=combo,
                    coverage_type="boundary",
                    rationale=f"Testing {attr.name} just above minimum ({attr.min_value + 1})"
                ))
            
            # Maximum boundary
            if attr.type == DSLType.INTEGER and attr.max_value is not None:
                combo = {attr.name: attr.max_value}
                combinations.append(TestCombination(
                    values=combo,
                    coverage_type="boundary",
                    rationale=f"Testing {attr.name} at maximum boundary ({attr.max_value})"
                ))
                
                # Just below maximum
                combo = {attr.name: attr.max_value - 1}
                combinations.append(TestCombination(
                    values=combo,
                    coverage_type="boundary",
                    rationale=f"Testing {attr.name} just below maximum ({attr.max_value - 1})"
                ))
            
            # Collection size boundaries
            if attr.is_collection() and attr.collection_info:
                if attr.collection_info.min_size is not None:
                    combo = {f"{attr.name}_size": attr.collection_info.min_size}
                    combinations.append(TestCombination(
                        values=combo,
                        coverage_type="boundary",
                        rationale=f"Testing {attr.name} at minimum size ({attr.collection_info.min_size})"
                    ))
                
                if attr.collection_info.max_size is not None:
                    combo = {f"{attr.name}_size": attr.collection_info.max_size}
                    combinations.append(TestCombination(
                        values=combo,
                        coverage_type="boundary",
                        rationale=f"Testing {attr.name} at maximum size ({attr.collection_info.max_size})"
                    ))
        
        return combinations