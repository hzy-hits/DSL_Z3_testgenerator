"""
Test Planning Strategy for V2.0

Creates minimal test plans based on DSL model analysis.
"""

from typing import List, Dict, Set, Optional
from dataclasses import dataclass
import logging

from ..core.models import (
    DSLModel, AttributeType, TestObjective, TestPlan,
    Constraint, Rule, TestHint
)
from .pairwise_test_planner import PairwiseTestPlanner, RuleCombinationAnalyzer


logger = logging.getLogger(__name__)


@dataclass
class CoverageRequirement:
    """What needs to be covered"""
    type: str  # constraint, rule, boundary, equivalence
    target: str  # specific item to cover
    priority: int
    reason: str


class TestPlanner:
    """Creates minimal test plan based on DSL model"""
    
    def __init__(self, model: DSLModel):
        self.model = model
        self.coverage_requirements = []
    
    def create_plan(self, 
                   coverage_goals: Optional[Dict[str, float]] = None,
                   max_tests: Optional[int] = None) -> TestPlan:
        """Create test plan with objectives"""
        # Analyze what needs to be tested
        self._analyze_coverage_requirements()
        
        # Create test objectives
        objectives = self._create_test_objectives()
        
        # Apply test hints
        objectives = self._apply_test_hints(objectives)
        
        # Minimize objectives
        objectives = self._minimize_objectives(objectives)
        
        # Apply max_tests limit if specified
        if max_tests and len(objectives) > max_tests:
            objectives = self._prioritize_objectives(objectives, max_tests)
        
        return TestPlan(
            objectives=objectives,
            coverage_goals=coverage_goals or {},
            max_tests=max_tests
        )
    
    def _analyze_coverage_requirements(self):
        """Analyze what needs to be covered"""
        self.coverage_requirements = []
        
        # 1. Constraint coverage
        for constraint in self.model.constraints:
            self.coverage_requirements.append(CoverageRequirement(
                type="constraint",
                target=constraint.expression,
                priority=8,
                reason=f"Cover constraint: {constraint.description or constraint.expression}"
            ))
        
        # 2. Rule coverage (both active and inactive)
        for rule in self.model.rules:
            # Active test
            self.coverage_requirements.append(CoverageRequirement(
                type="rule_active",
                target=rule.name,
                priority=9 + rule.priority,  # Higher priority rules get tested first
                reason=f"Test rule activation: {rule.name}"
            ))
            # Inactive test
            self.coverage_requirements.append(CoverageRequirement(
                type="rule_inactive",
                target=rule.name,
                priority=7 + rule.priority,
                reason=f"Test rule non-activation: {rule.name}"
            ))
        
        # 3. Boundary coverage
        for attr in self.model.get_all_attributes():
            if attr.type in [AttributeType.INTEGER, AttributeType.REAL]:
                if attr.min_value is not None:
                    self.coverage_requirements.append(CoverageRequirement(
                        type="boundary_min",
                        target=attr.full_name,
                        priority=7,
                        reason=f"Test minimum boundary: {attr.full_name} = {attr.min_value}"
                    ))
                if attr.max_value is not None:
                    self.coverage_requirements.append(CoverageRequirement(
                        type="boundary_max",
                        target=attr.full_name,
                        priority=7,
                        reason=f"Test maximum boundary: {attr.full_name} = {attr.max_value}"
                    ))
        
        # 4. Equivalence partitioning
        for attr in self.model.get_all_attributes():
            if attr.enum_values:
                # Test each enum value
                for value in attr.enum_values:
                    self.coverage_requirements.append(CoverageRequirement(
                        type="equivalence",
                        target=attr.full_name,
                        priority=6,
                        reason=f"Test enum value: {attr.full_name} = {value}"
                    ))
            elif attr.type in [AttributeType.INTEGER, AttributeType.REAL]:
                # Test middle value
                if attr.min_value is not None and attr.max_value is not None:
                    self.coverage_requirements.append(CoverageRequirement(
                        type="equivalence",
                        target=attr.full_name,
                        priority=5,
                        reason=f"Test typical value: {attr.full_name}"
                    ))
        
        # 5. State transition coverage
        for sm in self.model.state_machines:
            for transition in sm.transitions:
                if transition.condition.lower() != 'false':
                    # Valid transition test
                    self.coverage_requirements.append(CoverageRequirement(
                        type="state_transition_valid",
                        target=f"{sm.name}:{transition.name}",
                        priority=9,
                        reason=f"Test valid transition: {transition.from_state} -> {transition.to_state}"
                    ))
                else:
                    # Invalid transition test (explicitly forbidden)
                    self.coverage_requirements.append(CoverageRequirement(
                        type="state_transition_invalid",
                        target=f"{sm.name}:{transition.name}",
                        priority=8,
                        reason=f"Test forbidden transition: {transition.from_state} cannot go to {transition.to_state}"
                    ))
    
    def _create_test_objectives(self) -> List[TestObjective]:
        """Convert coverage requirements to test objectives"""
        objectives = []
        
        # Add pairwise testing objectives if there are multiple rules
        if len(self.model.rules) > 1:
            pairwise_planner = PairwiseTestPlanner(self.model)
            # Focus on attributes involved in rules
            rule_attributes = set()
            for rule in self.model.rules:
                # Extract attributes from conditions and consequences
                for attr in self.model.get_all_attributes():
                    if attr.full_name in rule.condition or attr.full_name in rule.consequence:
                        rule_attributes.add(attr.full_name)
            
            if len(rule_attributes) >= 2:
                pairwise_objectives = pairwise_planner.generate_pairwise_objectives(
                    focus_attributes=list(rule_attributes),
                    max_values_per_param=3
                )
                objectives.extend(pairwise_objectives)
                logger.info(f"Added {len(pairwise_objectives)} pairwise test objectives")
        
        for req in self.coverage_requirements:
            if req.type == "boundary_min":
                objectives.append(TestObjective(
                    type="boundary_min",
                    target=req.target,
                    priority=req.priority,
                    reason=req.reason
                ))
            
            elif req.type == "boundary_max":
                objectives.append(TestObjective(
                    type="boundary_max",
                    target=req.target,
                    priority=req.priority,
                    reason=req.reason
                ))
            
            elif req.type == "equivalence":
                # For enum values, add specific constraint
                attr = self.model.get_attribute_by_full_name(req.target)
                if attr and attr.enum_values:
                    # Extract value from reason (hacky but works for now)
                    for value in attr.enum_values:
                        if str(value) in req.reason:
                            objectives.append(TestObjective(
                                type="equivalence",
                                target=req.target,
                                priority=req.priority,
                                reason=req.reason,
                                constraints=[f"{req.target} == {value}"]
                            ))
                            break
                else:
                    objectives.append(TestObjective(
                        type="equivalence",
                        target=req.target,
                        priority=req.priority,
                        reason=req.reason
                    ))
            
            elif req.type == "rule_active":
                objectives.append(TestObjective(
                    type="rule_active",
                    target=req.target,
                    priority=req.priority,
                    reason=req.reason
                ))
            
            elif req.type == "rule_inactive":
                objectives.append(TestObjective(
                    type="rule_inactive",
                    target=req.target,
                    priority=req.priority,
                    reason=req.reason
                ))
        
        return objectives
    
    def _apply_test_hints(self, objectives: List[TestObjective]) -> List[TestObjective]:
        """Apply user-provided test hints"""
        for hint in self.model.test_hints:
            if hint.type == "focus":
                # Increase priority for focused items
                for obj in objectives:
                    if obj.target in hint.target:
                        obj.priority += 10
            
            elif hint.type == "ignore":
                # Remove ignored items
                objectives = [obj for obj in objectives 
                            if obj.target not in hint.target]
            
            elif hint.type == "combine":
                # This would require more complex handling
                # For now, just log it
                logger.info(f"Combine hint for {hint.target} - not implemented yet")
        
        return objectives
    
    def _minimize_objectives(self, objectives: List[TestObjective]) -> List[TestObjective]:
        """Remove redundant test objectives"""
        # Build coverage map
        coverage_map = self._build_coverage_map(objectives)
        
        # Use greedy set cover algorithm
        essential = []
        covered = set()
        remaining_objectives = objectives.copy()
        
        # Sort by priority (descending) and coverage (descending)
        remaining_objectives.sort(
            key=lambda obj: (obj.priority, len(coverage_map.get(obj, set()))),
            reverse=True
        )
        
        for obj in remaining_objectives:
            obj_coverage = coverage_map.get(obj, set())
            new_coverage = obj_coverage - covered
            
            if new_coverage:
                # This objective adds new coverage
                essential.append(obj)
                covered.update(obj_coverage)
        
        return essential
    
    def _build_coverage_map(self, objectives: List[TestObjective]) -> Dict[TestObjective, Set[str]]:
        """Build map of what each objective covers"""
        coverage_map = {}
        
        for obj in objectives:
            coverage = set()
            
            # Basic coverage - the target itself
            coverage.add(f"{obj.type}:{obj.target}")
            
            # Rule tests also cover involved attributes
            if obj.type in ["rule_active", "rule_inactive"]:
                rule = self.model.get_rule_by_name(obj.target)
                if rule:
                    # Extract attributes from rule (simplified)
                    for attr in self.model.get_all_attributes():
                        if attr.full_name in rule.condition or attr.full_name in rule.consequence:
                            coverage.add(f"attr:{attr.full_name}")
            
            # Boundary tests might cover constraints
            elif obj.type in ["boundary_min", "boundary_max"]:
                attr_name = obj.target
                for constraint in self.model.constraints:
                    if attr_name in constraint.expression:
                        coverage.add(f"constraint:{constraint.expression}")
            
            coverage_map[obj] = coverage
        
        return coverage_map
    
    def _prioritize_objectives(self, objectives: List[TestObjective], max_tests: int) -> List[TestObjective]:
        """Select top objectives by priority"""
        # Sort by priority descending
        objectives.sort(key=lambda obj: obj.priority, reverse=True)
        
        # Take top max_tests
        return objectives[:max_tests]


class CoverageAnalyzer:
    """Analyze test coverage"""
    
    def __init__(self, model: DSLModel):
        self.model = model
    
    def analyze_objective_coverage(self, objective: TestObjective) -> Set[str]:
        """Analyze what a test objective covers"""
        coverage = set()
        
        # Add the objective itself
        coverage.add(f"{objective.type}:{objective.target}")
        
        # Analyze based on type
        if objective.type == "rule_active":
            rule = self.model.get_rule_by_name(objective.target)
            if rule:
                coverage.add(f"rule_active:{rule.name}")
                # Add attributes involved in rule
                for attr in self.model.get_all_attributes():
                    if attr.full_name in rule.condition or attr.full_name in rule.consequence:
                        coverage.add(f"attribute:{attr.full_name}")
        
        elif objective.type == "rule_inactive":
            rule = self.model.get_rule_by_name(objective.target)
            if rule:
                coverage.add(f"rule_inactive:{rule.name}")
        
        elif objective.type in ["boundary_min", "boundary_max"]:
            coverage.add(f"boundary:{objective.target}")
            # Check which constraints this boundary test covers
            for constraint in self.model.constraints:
                if objective.target in constraint.expression:
                    coverage.add(f"constraint:{constraint.expression}")
        
        elif objective.type == "equivalence":
            coverage.add(f"equivalence:{objective.target}")
            # Add any specific value being tested
            for constraint_expr in objective.constraints:
                coverage.add(f"value_test:{constraint_expr}")
        
        return coverage
    
    def calculate_coverage_metrics(self, test_objectives: List[TestObjective]) -> Dict[str, float]:
        """Calculate coverage metrics for test objectives"""
        # Total items to cover
        total_constraints = len(self.model.constraints)
        total_rules = len(self.model.rules) * 2  # active + inactive
        total_boundaries = sum(
            2 for attr in self.model.get_all_attributes()
            if attr.type in [AttributeType.INTEGER, AttributeType.REAL]
            and (attr.min_value is not None or attr.max_value is not None)
        )
        
        # Covered items
        covered = set()
        for obj in test_objectives:
            covered.update(self.analyze_objective_coverage(obj))
        
        # Count covered items by type
        covered_constraints = sum(1 for item in covered if item.startswith("constraint:"))
        covered_rules = sum(1 for item in covered if item.startswith("rule_"))
        covered_boundaries = sum(1 for item in covered if item.startswith("boundary:"))
        
        return {
            "constraint_coverage": covered_constraints / total_constraints if total_constraints > 0 else 1.0,
            "rule_coverage": covered_rules / total_rules if total_rules > 0 else 1.0,
            "boundary_coverage": covered_boundaries / total_boundaries if total_boundaries > 0 else 1.0,
            "total_objectives": len(test_objectives),
            "unique_coverage_items": len(covered)
        }