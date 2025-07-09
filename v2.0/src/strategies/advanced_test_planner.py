"""
Advanced Test Planning Strategy for V2.0

Extends the basic test planner with combination analysis and intelligent test selection.
"""

from typing import List, Dict, Set, Optional
from dataclasses import dataclass
import logging
import random

from ..core.models import (
    DSLModel, AttributeType, TestObjective, TestPlan,
    Constraint, Rule, TestHint
)
from .test_planner import TestPlanner, CoverageRequirement
from .combination_analyzer import CombinationAnalyzer


logger = logging.getLogger(__name__)


class AdvancedTestPlanner(TestPlanner):
    """Advanced test planner with combination analysis"""
    
    def __init__(self, model: DSLModel, 
                 enable_combination_tests: bool = True,
                 enable_diverse_equivalence: bool = True):
        """
        Initialize advanced test planner.
        
        Args:
            model: DSL model
            enable_combination_tests: Enable combination testing
            enable_diverse_equivalence: Enable diverse equivalence tests
        """
        super().__init__(model)
        self.enable_combination_tests = enable_combination_tests
        self.enable_diverse_equivalence = enable_diverse_equivalence
        
    def _add_combination_test_requirements(self):
        """Add requirements for combination tests"""
        if not self.enable_combination_tests:
            return
            
        # Use combination analyzer
        analyzer = CombinationAnalyzer(self.model)
        
        # Add requirements for critical combinations
        suggestions = analyzer.suggest_critical_combinations()
        for suggestion in suggestions:
            if suggestion["type"] == "conflict_resolution":
                # Add high-priority test for conflicts
                self.coverage_requirements.append(CoverageRequirement(
                    type="conflict_test",
                    target="+".join(suggestion["rules"]),
                    priority=10,  # Highest priority
                    reason=f"Conflict test: {suggestion['description']}"
                ))
    
    def _create_test_objectives(self) -> List[TestObjective]:
        """Convert coverage requirements to test objectives - extended"""
        objectives = super()._create_test_objectives()
        
        # Add objectives for combination tests
        if self.enable_combination_tests:
            self._add_combination_objectives(objectives)
        
        return objectives
    
    def _add_combination_objectives(self, objectives: List[TestObjective]):
        """Add test objectives for rule combinations"""
        # Group objectives by type for combination planning
        conflict_reqs = [req for req in self.coverage_requirements 
                        if req.type == "conflict_test"]
        
        for req in conflict_reqs:
            rule_names = req.target.split('+')
            if len(rule_names) == 2:
                # Create objective that tries to activate both rules
                rule1 = self.model.rules.get(rule_names[0])
                rule2 = self.model.rules.get(rule_names[1])
                
                if rule1 and rule2:
                    # Combine conditions (this is simplified)
                    combined_constraints = []
                    
                    # Try to satisfy both conditions
                    combined_constraints.append(rule1.condition)
                    combined_constraints.append(rule2.condition)
                    
                    objectives.append(TestObjective(
                        type="combination",
                        target=req.target,
                        priority=req.priority,
                        reason=req.reason,
                        constraints=combined_constraints
                    ))
    
    def create_plan(self, coverage_goals: Dict[str, float]) -> TestPlan:
        """Create test plan with advanced features"""
        # First use basic planning
        plan = super().create_plan(coverage_goals)
        
        # Add combination test requirements
        self._add_combination_test_requirements()
        
        # Convert additional requirements to objectives
        additional_objectives = []
        for req in self.coverage_requirements:
            if req.type == "conflict_test":
                # These are handled specially
                continue
            
        # Add new objectives to plan
        if additional_objectives:
            plan = TestPlan(
                objectives=plan.objectives + additional_objectives,
                coverage_goals=plan.coverage_goals
            )
        
        return plan