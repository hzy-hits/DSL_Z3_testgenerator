"""
Quality Scorer for evaluating generated test cases
"""

from typing import List, Dict, Any
from src.models.dsl_models import Model


class QualityScorer:
    """Evaluates the quality of generated test cases"""
    
    def evaluate_test_suite(self, tests: List[Any], model: Model) -> Dict[str, Any]:
        """Evaluate a complete test suite"""
        
        # Initialize metrics
        metrics = {
            "total_tests": len(tests),
            "concrete_value_score": 0.0,
            "coverage_score": 0.0,
            "diversity_score": 0.0,
            "rationale_score": 0.0,
            "executability_score": 0.0
        }
        
        # 1. Concrete Value Score - Are values specific and usable?
        concrete_count = 0
        for test in tests:
            if self._has_concrete_values(test.concrete_input):
                concrete_count += 1
        metrics["concrete_value_score"] = (concrete_count / len(tests)) * 10 if tests else 0
        
        # 2. Coverage Score - What percentage of model elements are tested?
        coverage = self._calculate_coverage(tests, model)
        metrics["coverage_score"] = coverage * 10
        
        # 3. Diversity Score - Are test types well distributed?
        diversity = self._calculate_diversity(tests)
        metrics["diversity_score"] = diversity * 10
        
        # 4. Rationale Score - Do tests explain why they exist?
        rationale_count = sum(1 for test in tests if test.rationale and len(test.rationale) > 20)
        metrics["rationale_score"] = (rationale_count / len(tests)) * 10 if tests else 0
        
        # 5. Executability Score - Can tests be run directly?
        exec_count = sum(1 for test in tests if self._is_executable(test))
        metrics["executability_score"] = (exec_count / len(tests)) * 10 if tests else 0
        
        # Calculate overall score
        overall_score = (
            metrics["concrete_value_score"] * 0.3 +
            metrics["coverage_score"] * 0.25 +
            metrics["diversity_score"] * 0.15 +
            metrics["rationale_score"] * 0.15 +
            metrics["executability_score"] * 0.15
        )
        
        return {
            "overall_score": round(overall_score, 1),
            "metrics": metrics,
            "test_count": len(tests),
            "recommendations": self._generate_recommendations(metrics)
        }
    
    def _has_concrete_values(self, input_data: Dict[str, Any]) -> bool:
        """Check if input has concrete values (not abstract descriptions)"""
        for key, value in input_data.items():
            # Check for abstract patterns like "size" or "_count"
            if isinstance(key, str) and ("_size" in key or "_count" in key):
                # This is abstract if it's just a number
                if isinstance(value, int) and key.replace("_size", "").replace("_count", "") not in input_data:
                    return False
            
            # Check for concrete collections
            if isinstance(value, list) and len(value) > 0:
                # Good - has actual elements
                continue
            elif isinstance(value, dict) and value:
                # Good - has nested data
                continue
        
        return True
    
    def _calculate_coverage(self, tests: List[Any], model: Model) -> float:
        """Calculate test coverage of model elements"""
        covered_entities = set()
        covered_rules = set()
        covered_constraints = set()
        
        for test in tests:
            # Extract covered elements
            for point in test.coverage_points:
                if point.startswith("entity:"):
                    covered_entities.add(point.split(":")[1])
                elif point.startswith("rule:"):
                    covered_rules.add(point.split(":")[1])
            
            for constraint in test.constraints_tested:
                covered_constraints.add(constraint)
        
        # Calculate coverage ratios
        entity_coverage = len(covered_entities) / len(model.entities) if model.entities else 1.0
        rule_coverage = len(covered_rules) / len(model.rules) if model.rules else 1.0
        constraint_coverage = len(covered_constraints) / len(model.constraints) if model.constraints else 1.0
        
        # Weighted average
        return (entity_coverage * 0.4 + rule_coverage * 0.3 + constraint_coverage * 0.3)
    
    def _calculate_diversity(self, tests: List[Any]) -> float:
        """Calculate diversity of test types"""
        type_counts = {}
        for test in tests:
            type_counts[test.test_type] = type_counts.get(test.test_type, 0) + 1
        
        # Ideal distribution
        ideal_types = ["functional", "boundary", "negative", "rule", "constraint", "combinatorial", "scenario"]
        
        # How many types are covered?
        types_covered = len([t for t in ideal_types if t in type_counts])
        type_coverage = types_covered / len(ideal_types)
        
        # How balanced is the distribution?
        if len(type_counts) > 1:
            counts = list(type_counts.values())
            avg_count = sum(counts) / len(counts)
            variance = sum((c - avg_count) ** 2 for c in counts) / len(counts)
            balance_score = 1 / (1 + variance / (avg_count ** 2)) if avg_count > 0 else 0
        else:
            balance_score = 0.5
        
        return (type_coverage * 0.6 + balance_score * 0.4)
    
    def _is_executable(self, test: Any) -> bool:
        """Check if test has enough information to be executable"""
        # Must have concrete input
        if not test.concrete_input:
            return False
        
        # Must have expected result
        if not test.expected_result:
            return False
        
        # Input should have actual values, not just descriptions
        return self._has_concrete_values(test.concrete_input)
    
    def _generate_recommendations(self, metrics: Dict[str, float]) -> List[str]:
        """Generate improvement recommendations based on metrics"""
        recommendations = []
        
        if metrics["concrete_value_score"] < 8:
            recommendations.append("Improve concrete value generation - avoid abstract descriptions")
        
        if metrics["coverage_score"] < 7:
            recommendations.append("Increase test coverage - ensure all entities, rules, and constraints are tested")
        
        if metrics["diversity_score"] < 6:
            recommendations.append("Add more test type variety - include boundary, negative, and scenario tests")
        
        if metrics["rationale_score"] < 7:
            recommendations.append("Enhance test rationales - explain why each test is important")
        
        if metrics["executability_score"] < 8:
            recommendations.append("Ensure all tests have executable data - no abstract placeholders")
        
        if not recommendations:
            recommendations.append("Excellent test suite quality - maintain current standards")
        
        return recommendations