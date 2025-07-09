"""
Main Test Generator for V2.0

Orchestrates the test generation process with correctness guarantees.
"""

from typing import List, Dict, Any, Optional, Set
import logging
from dataclasses import dataclass

from .models import (
    DSLModel, TestCase, TestPlan, TestObjective,
    CoverageReport
)
from ..layers.constraint_solver import Z3ConstraintSolver
from ..strategies.test_planner import TestPlanner, CoverageAnalyzer


logger = logging.getLogger(__name__)


@dataclass
class GenerationResult:
    """Result of test generation"""
    test_cases: List[TestCase]
    coverage_report: CoverageReport
    failed_objectives: List[TestObjective]
    warnings: List[str]


class TestGenerator:
    """Main test generation engine"""
    
    def __init__(self, 
                 minimize: bool = True,
                 verify_all: bool = True,
                 max_attempts: int = 3):
        """
        Initialize test generator.
        
        Args:
            minimize: Whether to minimize test set
            verify_all: Whether to verify all generated tests
            max_attempts: Maximum attempts to generate test for each objective
        """
        self.minimize = minimize
        self.verify_all = verify_all
        self.max_attempts = max_attempts
    
    def generate(self, 
                model: DSLModel,
                coverage_goals: Optional[Dict[str, float]] = None,
                max_tests: Optional[int] = None) -> GenerationResult:
        """
        Generate minimal test suite with correctness guarantee.
        
        Args:
            model: DSL model
            coverage_goals: Coverage goals (default: 100% for all)
            max_tests: Maximum number of tests to generate
            
        Returns:
            GenerationResult with test cases and coverage report
        """
        logger.info(f"Starting test generation for domain: {model.domain}")
        
        # Validate model
        errors = model.validate()
        if errors:
            logger.error(f"Model validation failed: {errors}")
            return GenerationResult(
                test_cases=[],
                coverage_report=CoverageReport(),
                failed_objectives=[],
                warnings=errors
            )
        
        # Check constraint consistency
        solver = Z3ConstraintSolver(model)
        if not solver.check_constraint_consistency():
            logger.error("Model constraints are inconsistent!")
            unsat_core = solver.get_unsat_core()
            return GenerationResult(
                test_cases=[],
                coverage_report=CoverageReport(),
                failed_objectives=[],
                warnings=[f"Inconsistent constraints: {unsat_core}"]
            )
        
        # Create test plan
        planner = TestPlanner(model)
        test_plan = planner.create_plan(coverage_goals, max_tests)
        logger.info(f"Created test plan with {len(test_plan.objectives)} objectives")
        
        # Generate test data for each objective
        test_cases = []
        failed_objectives = []
        warnings = []
        
        for i, objective in enumerate(test_plan.objectives):
            logger.debug(f"Processing objective {i+1}/{len(test_plan.objectives)}: {objective.reason}")
            
            # Try to generate test data
            test_data = None
            for attempt in range(self.max_attempts):
                test_data = solver.generate_test_data(objective)
                if test_data:
                    break
                logger.debug(f"Attempt {attempt+1} failed for {objective.type} {objective.target}")
            
            if test_data:
                # Create test case
                test_case = TestCase(
                    name=f"test_{i+1}_{objective.type}_{objective.target}",
                    objective=objective,
                    values=test_data,
                    expected="pass"
                )
                
                # Analyze coverage
                analyzer = CoverageAnalyzer(model)
                test_case.coverage = analyzer.analyze_objective_coverage(objective)
                
                # Verify if requested
                if self.verify_all:
                    is_valid = self._verify_test_case(test_case, model)
                    if not is_valid:
                        test_case.validation_errors.append("Failed post-generation verification")
                        warnings.append(f"Test {test_case.name} failed verification")
                
                test_cases.append(test_case)
            else:
                failed_objectives.append(objective)
                warnings.append(f"Could not generate test for: {objective.reason}")
        
        # Minimize test set if requested
        if self.minimize and test_cases:
            test_cases = self._minimize_test_set(test_cases, model)
            logger.info(f"Minimized test set to {len(test_cases)} tests")
        
        # Generate coverage report
        coverage_report = self._generate_coverage_report(test_cases, model)
        
        logger.info(f"Generated {len(test_cases)} tests with {len(failed_objectives)} failures")
        
        return GenerationResult(
            test_cases=test_cases,
            coverage_report=coverage_report,
            failed_objectives=failed_objectives,
            warnings=warnings
        )
    
    def _verify_test_case(self, test_case: TestCase, model: DSLModel) -> bool:
        """Verify test case against all constraints and rules"""
        solver = Z3ConstraintSolver(model)
        
        # Use solver's verification method
        return solver._verify_solution(test_case.values, test_case.objective)
    
    def _minimize_test_set(self, test_cases: List[TestCase], model: DSLModel) -> List[TestCase]:
        """Remove redundant tests while maintaining coverage"""
        if not test_cases:
            return []
        
        # Build coverage matrix
        coverage_matrix = {}
        all_covered_items = set()
        
        for test in test_cases:
            coverage_matrix[test.name] = test.coverage
            all_covered_items.update(test.coverage)
        
        # Greedy set cover
        essential_tests = []
        covered = set()
        
        # Sort by coverage size (descending) and priority
        sorted_tests = sorted(
            test_cases,
            key=lambda t: (len(t.coverage), t.objective.priority),
            reverse=True
        )
        
        for test in sorted_tests:
            new_coverage = test.coverage - covered
            if new_coverage:
                essential_tests.append(test)
                covered.update(test.coverage)
                
                # Check if we've covered everything
                if covered == all_covered_items:
                    break
        
        return essential_tests
    
    def _generate_coverage_report(self, test_cases: List[TestCase], model: DSLModel) -> CoverageReport:
        """Generate detailed coverage report"""
        report = CoverageReport()
        
        # Count totals
        report.total_constraints = len(model.constraints)
        report.total_rules = len(model.rules)
        report.total_boundaries = sum(
            1 for attr in model.get_all_attributes()
            if attr.min_value is not None or attr.max_value is not None
        )
        
        # Analyze coverage
        covered_constraints = set()
        covered_rules = set()
        covered_boundaries = set()
        
        for test in test_cases:
            report.add_test_coverage(test)
            
            for item in test.coverage:
                if item.startswith("constraint:"):
                    covered_constraints.add(item)
                elif item.startswith("rule_"):
                    covered_rules.add(item)
                elif item.startswith("boundary:"):
                    covered_boundaries.add(item)
        
        # Update counts
        report.covered_constraints = len(covered_constraints)
        report.covered_rules = len(covered_rules) // 2  # Divide by 2 as we count active/inactive separately
        report.covered_boundaries = len(covered_boundaries)
        
        return report


class TestValidator:
    """Validate generated test cases"""
    
    def __init__(self, model: DSLModel):
        self.model = model
        self.solver = Z3ConstraintSolver(model)
    
    def validate_test_case(self, test_case: TestCase) -> List[str]:
        """
        Validate a single test case.
        
        Returns:
            List of validation errors (empty if valid)
        """
        errors = []
        
        # Check all constraints
        for constraint in self.model.constraints:
            if not self.solver._evaluate_expression(constraint.expression, test_case.values):
                errors.append(f"Violates constraint: {constraint.expression}")
        
        # Check objective-specific requirements
        objective = test_case.objective
        
        if objective.type == "rule_active":
            rule = self.model.get_rule_by_name(objective.target)
            if rule:
                # Check condition is true
                if not self.solver._evaluate_expression(rule.condition, test_case.values):
                    errors.append(f"Rule '{rule.name}' condition not satisfied")
                # Check consequence is true
                if not self.solver._evaluate_expression(rule.consequence, test_case.values):
                    errors.append(f"Rule '{rule.name}' consequence not satisfied")
        
        elif objective.type == "rule_inactive":
            rule = self.model.get_rule_by_name(objective.target)
            if rule:
                # Check condition is false
                if self.solver._evaluate_expression(rule.condition, test_case.values):
                    errors.append(f"Rule '{rule.name}' should not be activated")
        
        elif objective.type == "boundary_min":
            attr = self.model.get_attribute_by_full_name(objective.target)
            if attr and attr.min_value is not None:
                value = test_case.values.get(attr.full_name)
                if value != attr.min_value:
                    errors.append(f"{attr.full_name} should be at minimum ({attr.min_value}), got {value}")
        
        elif objective.type == "boundary_max":
            attr = self.model.get_attribute_by_full_name(objective.target)
            if attr and attr.max_value is not None:
                value = test_case.values.get(attr.full_name)
                if value != attr.max_value:
                    errors.append(f"{attr.full_name} should be at maximum ({attr.max_value}), got {value}")
        
        return errors
    
    def validate_all_tests(self, test_cases: List[TestCase]) -> Dict[str, List[str]]:
        """
        Validate all test cases.
        
        Returns:
            Dictionary mapping test names to validation errors
        """
        results = {}
        
        for test in test_cases:
            errors = self.validate_test_case(test)
            if errors:
                results[test.name] = errors
        
        return results