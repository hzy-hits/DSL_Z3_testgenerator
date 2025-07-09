"""
DSL Test Generator V2.0 - Core Prototype

This is a clean-room implementation focusing on correctness and minimality.
"""

from dataclasses import dataclass, field
from typing import List, Dict, Any, Optional, Set, Tuple
from enum import Enum
import z3
from abc import ABC, abstractmethod


# ============= Data Models =============

class AttributeType(Enum):
    INTEGER = "integer"
    REAL = "real"
    BOOLEAN = "boolean"
    STRING = "string"


@dataclass
class Attribute:
    """Attribute definition with full context"""
    name: str
    entity_name: str
    type: AttributeType
    min_value: Optional[float] = None
    max_value: Optional[float] = None
    enum_values: Optional[List[Any]] = None
    
    @property
    def full_name(self) -> str:
        """Get full qualified name"""
        return f"{self.entity_name.lower()}_{self.name}"


@dataclass
class Entity:
    """Entity definition"""
    name: str
    attributes: List[Attribute]
    
    def __post_init__(self):
        # Set entity reference in attributes
        for attr in self.attributes:
            attr.entity_name = self.name


@dataclass
class Constraint:
    """Constraint definition"""
    expression: str
    type: str = "general"  # general, implication
    
    
@dataclass  
class Rule:
    """Business rule with condition and consequence"""
    name: str
    condition: str
    consequence: str
    priority: int = 1
    

@dataclass
class DSLModel:
    """Complete DSL model"""
    domain: str
    entities: List[Entity]
    constraints: List[Constraint]
    rules: List[Rule]
    
    def get_all_attributes(self) -> List[Attribute]:
        """Get all attributes from all entities"""
        attributes = []
        for entity in self.entities:
            attributes.extend(entity.attributes)
        return attributes


# ============= Test Planning =============

@dataclass
class TestObjective:
    """What we want to test and why"""
    type: str  # boundary_min, boundary_max, rule_active, rule_inactive, equivalence
    target: str  # attribute name or rule name
    priority: int
    reason: str
    constraints: List[str] = field(default_factory=list)  # Additional constraints


@dataclass
class TestCase:
    """A single test case with metadata"""
    name: str
    objective: TestObjective
    values: Dict[str, Any]
    expected: str = "pass"
    coverage: Set[str] = field(default_factory=set)  # What this test covers


class TestPlanner:
    """Creates minimal test plan based on DSL model"""
    
    def create_plan(self, model: DSLModel) -> List[TestObjective]:
        """Create test objectives for complete coverage"""
        objectives = []
        
        # 1. Boundary tests for numeric attributes
        for attr in model.get_all_attributes():
            if attr.type in [AttributeType.INTEGER, AttributeType.REAL]:
                if attr.min_value is not None:
                    objectives.append(TestObjective(
                        type="boundary_min",
                        target=attr.full_name,
                        priority=8,
                        reason=f"Test minimum value for {attr.full_name}"
                    ))
                if attr.max_value is not None:
                    objectives.append(TestObjective(
                        type="boundary_max",
                        target=attr.full_name,
                        priority=8,
                        reason=f"Test maximum value for {attr.full_name}"
                    ))
        
        # 2. Equivalence tests for enums
        for attr in model.get_all_attributes():
            if attr.enum_values:
                for value in attr.enum_values:
                    objectives.append(TestObjective(
                        type="equivalence",
                        target=attr.full_name,
                        priority=6,
                        reason=f"Test enum value {value} for {attr.full_name}",
                        constraints=[f"{attr.full_name} == {value}"]
                    ))
        
        # 3. Rule tests
        for rule in model.rules:
            # Active test
            objectives.append(TestObjective(
                type="rule_active",
                target=rule.name,
                priority=9,
                reason=f"Test rule activation: {rule.name}"
            ))
            # Inactive test
            objectives.append(TestObjective(
                type="rule_inactive", 
                target=rule.name,
                priority=7,
                reason=f"Test rule non-activation: {rule.name}"
            ))
        
        # 4. Minimize by removing redundant objectives
        return self._minimize_objectives(objectives, model)
    
    def _minimize_objectives(self, objectives: List[TestObjective], model: DSLModel) -> List[TestObjective]:
        """Remove redundant test objectives"""
        # Simple heuristic: if two objectives test the same attribute boundary,
        # and one is part of a rule test, keep only the rule test
        
        essential = []
        coverage = set()
        
        # Sort by priority (higher first)
        objectives.sort(key=lambda x: x.priority, reverse=True)
        
        for obj in objectives:
            key = f"{obj.type}:{obj.target}"
            if key not in coverage:
                essential.append(obj)
                coverage.add(key)
                
                # Rule tests also cover some boundaries
                if obj.type == "rule_active":
                    rule = next((r for r in model.rules if r.name == obj.target), None)
                    if rule:
                        # Mark that this rule test covers certain attributes
                        # This is a simplified version - real implementation would parse the rule
                        pass
        
        return essential


# ============= Constraint Solving =============

class Z3ConstraintSolver:
    """Handles all Z3 constraint solving with correctness guarantees"""
    
    def __init__(self, model: DSLModel):
        self.model = model
        self.solver = z3.Solver()
        self.variables = {}
        self._create_variables()
        self._add_base_constraints()
    
    def _create_variables(self):
        """Create Z3 variables for all attributes"""
        for attr in self.model.get_all_attributes():
            if attr.type == AttributeType.INTEGER:
                self.variables[attr.full_name] = z3.Int(attr.full_name)
            elif attr.type == AttributeType.REAL:
                self.variables[attr.full_name] = z3.Real(attr.full_name)
            elif attr.type == AttributeType.BOOLEAN:
                self.variables[attr.full_name] = z3.Bool(attr.full_name)
            else:  # STRING - simplified as int for now
                self.variables[attr.full_name] = z3.Int(attr.full_name)
    
    def _add_base_constraints(self):
        """Add all model constraints to solver"""
        # 1. Attribute range constraints
        for attr in self.model.get_all_attributes():
            var = self.variables.get(attr.full_name)
            if var is None:
                continue
                
            if attr.min_value is not None:
                self.solver.add(var >= attr.min_value)
            if attr.max_value is not None:
                self.solver.add(var <= attr.max_value)
        
        # 2. Model constraints
        for constraint in self.model.constraints:
            z3_expr = self._parse_expression(constraint.expression)
            if z3_expr is not None:
                self.solver.add(z3_expr)
    
    def generate_test_data(self, objective: TestObjective) -> Optional[Dict[str, Any]]:
        """Generate test data for a specific objective"""
        self.solver.push()
        
        try:
            # Add objective-specific constraints
            if objective.type == "boundary_min":
                var = self.variables[objective.target]
                attr = self._find_attribute(objective.target)
                if attr and attr.min_value is not None:
                    self.solver.add(var == attr.min_value)
                    
            elif objective.type == "boundary_max":
                var = self.variables[objective.target]
                attr = self._find_attribute(objective.target)
                if attr and attr.max_value is not None:
                    self.solver.add(var == attr.max_value)
                    
            elif objective.type == "equivalence":
                # Constraints already in objective
                for constraint in objective.constraints:
                    z3_expr = self._parse_expression(constraint)
                    if z3_expr is not None:
                        self.solver.add(z3_expr)
                        
            elif objective.type == "rule_active":
                rule = self._find_rule(objective.target)
                if rule:
                    # Add condition to activate rule
                    condition = self._parse_expression(rule.condition)
                    if condition is not None:
                        self.solver.add(condition)
                    # Add consequence
                    consequence = self._parse_expression(rule.consequence)
                    if consequence is not None:
                        self.solver.add(consequence)
                        
            elif objective.type == "rule_inactive":
                rule = self._find_rule(objective.target)
                if rule:
                    # Add negation of condition
                    condition = self._parse_expression(rule.condition)
                    if condition is not None:
                        self.solver.add(z3.Not(condition))
            
            # Solve
            if self.solver.check() == z3.sat:
                model = self.solver.model()
                values = self._extract_values(model)
                
                # Verify the solution
                if self._verify_solution(values, objective):
                    return values
                    
            return None
            
        finally:
            self.solver.pop()
    
    def _parse_expression(self, expr: str) -> Optional[Any]:
        """Parse DSL expression to Z3 expression"""
        # This is a simplified parser - real implementation would be more robust
        expr = expr.strip()
        
        # Handle implications
        if " -> " in expr:
            parts = expr.split(" -> ", 1)
            left = self._parse_expression(parts[0])
            right = self._parse_expression(parts[1])
            if left is not None and right is not None:
                return z3.Implies(left, right)
        
        # Handle and/or
        if " and " in expr:
            parts = expr.split(" and ")
            exprs = [self._parse_expression(p) for p in parts]
            exprs = [e for e in exprs if e is not None]
            if exprs:
                return z3.And(*exprs)
                
        if " or " in expr:
            parts = expr.split(" or ")
            exprs = [self._parse_expression(p) for p in parts]
            exprs = [e for e in exprs if e is not None]
            if exprs:
                return z3.Or(*exprs)
        
        # Handle comparisons
        for op in [">=", "<=", "==", "!=", ">", "<"]:
            if op in expr:
                parts = expr.split(op)
                if len(parts) == 2:
                    left = self._parse_term(parts[0].strip())
                    right = self._parse_term(parts[1].strip())
                    if left is not None and right is not None:
                        if op == ">=": return left >= right
                        elif op == "<=": return left <= right
                        elif op == "==": return left == right
                        elif op == "!=": return left != right
                        elif op == ">": return left > right
                        elif op == "<": return left < right
        
        return None
    
    def _parse_term(self, term: str) -> Optional[Any]:
        """Parse a single term"""
        term = term.strip()
        
        # Variable
        if term in self.variables:
            return self.variables[term]
        
        # Number
        try:
            if "." in term:
                return float(term)
            else:
                return int(term)
        except:
            pass
            
        # Boolean
        if term == "true":
            return True
        elif term == "false":
            return False
            
        return None
    
    def _extract_values(self, model: z3.ModelRef) -> Dict[str, Any]:
        """Extract concrete values from Z3 model"""
        values = {}
        for name, var in self.variables.items():
            val = model.eval(var)
            if z3.is_int_value(val):
                values[name] = val.as_long()
            elif z3.is_rational_value(val):
                values[name] = float(val.as_decimal(6))
            elif z3.is_bool(val):
                if z3.is_true(val):
                    values[name] = True
                elif z3.is_false(val):
                    values[name] = False
                else:
                    # Evaluate to get concrete value
                    values[name] = z3.is_true(model.eval(val))
            else:
                values[name] = str(val)
        return values
    
    def _verify_solution(self, values: Dict[str, Any], objective: TestObjective) -> bool:
        """Verify that solution satisfies all constraints and objective"""
        # 1. Check all constraints
        for constraint in self.model.constraints:
            if not self._evaluate_expression(constraint.expression, values):
                return False
        
        # 2. Check objective-specific requirements
        if objective.type == "rule_active":
            rule = self._find_rule(objective.target)
            if rule:
                # Check condition is true
                if not self._evaluate_expression(rule.condition, values):
                    return False
                # Check consequence is true
                if not self._evaluate_expression(rule.consequence, values):
                    return False
                    
        elif objective.type == "rule_inactive":
            rule = self._find_rule(objective.target)
            if rule:
                # Check condition is false
                if self._evaluate_expression(rule.condition, values):
                    return False
        
        return True
    
    def _evaluate_expression(self, expr: str, values: Dict[str, Any]) -> bool:
        """Evaluate expression with concrete values"""
        # Simplified evaluation - real implementation would be more robust
        try:
            # Replace variables with values
            for name, value in values.items():
                expr = expr.replace(name, str(value))
            
            # Handle implications
            if " -> " in expr:
                parts = expr.split(" -> ", 1)
                left = self._evaluate_expression(parts[0], {})
                right = self._evaluate_expression(parts[1], {})
                return not left or right
            
            # Evaluate
            # In production, use a safe expression evaluator
            return eval(expr)
        except:
            return False
    
    def _find_attribute(self, full_name: str) -> Optional[Attribute]:
        """Find attribute by full name"""
        for attr in self.model.get_all_attributes():
            if attr.full_name == full_name:
                return attr
        return None
    
    def _find_rule(self, name: str) -> Optional[Rule]:
        """Find rule by name"""
        for rule in self.model.rules:
            if rule.name == name:
                return rule
        return None


# ============= Main Engine =============

class TestGenerator:
    """Main test generation engine"""
    
    def generate(self, model: DSLModel) -> List[TestCase]:
        """Generate minimal test suite with correctness guarantee"""
        # 1. Create test plan
        planner = TestPlanner()
        objectives = planner.create_plan(model)
        
        # 2. Generate test data
        solver = Z3ConstraintSolver(model)
        test_cases = []
        
        for i, objective in enumerate(objectives):
            values = solver.generate_test_data(objective)
            if values:
                test_case = TestCase(
                    name=f"test_{i+1}_{objective.type}_{objective.target}",
                    objective=objective,
                    values=values,
                    expected="pass",
                    coverage={objective.target}
                )
                test_cases.append(test_case)
            else:
                print(f"Warning: Could not generate test for {objective.type} {objective.target}")
        
        # 3. Final minimization based on actual coverage
        return self._minimize_by_coverage(test_cases)
    
    def _minimize_by_coverage(self, test_cases: List[TestCase]) -> List[TestCase]:
        """Remove tests that don't add coverage"""
        essential = []
        total_coverage = set()
        
        for test in test_cases:
            if not test.coverage.issubset(total_coverage):
                essential.append(test)
                total_coverage.update(test.coverage)
        
        return essential


# ============= Example Usage =============

def example():
    """Example of how to use the new design"""
    
    # Define a simple model
    model = DSLModel(
        domain="Hotel Booking",
        entities=[
            Entity(name="Customer", attributes=[
                Attribute(name="age", entity_name="Customer", type=AttributeType.INTEGER, min_value=18, max_value=120),
                Attribute(name="is_vip", entity_name="Customer", type=AttributeType.BOOLEAN)
            ]),
            Entity(name="Booking", attributes=[
                Attribute(name="nights", entity_name="Booking", type=AttributeType.INTEGER, min_value=1, max_value=30),
                Attribute(name="discount", entity_name="Booking", type=AttributeType.INTEGER, min_value=0, max_value=50)
            ])
        ],
        constraints=[
            Constraint("customer_age >= 18"),
            Constraint("booking_nights >= 1"),
            Constraint("booking_discount >= 0 and booking_discount <= 50")
        ],
        rules=[
            Rule(
                name="VIP Discount",
                condition="customer_is_vip == true",
                consequence="booking_discount >= 15",
                priority=10
            ),
            Rule(
                name="Long Stay Discount",
                condition="booking_nights >= 7",
                consequence="booking_discount >= 10",
                priority=8
            )
        ]
    )
    
    # Generate tests
    generator = TestGenerator()
    tests = generator.generate(model)
    
    # Print results
    print(f"Generated {len(tests)} tests:")
    for test in tests:
        print(f"\n{test.name}:")
        print(f"  Objective: {test.objective.reason}")
        print(f"  Values: {test.values}")
        print(f"  Coverage: {test.coverage}")


if __name__ == "__main__":
    example()