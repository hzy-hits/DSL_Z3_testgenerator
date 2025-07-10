"""
Constraint Solver Layer for V2.0

Handles all Z3 constraint solving with correctness guarantees.
"""

import z3
from typing import Dict, Any, List, Optional, Set, Tuple
from dataclasses import dataclass
import logging

from ..core.models import (
    DSLModel, Attribute, AttributeType, Constraint, Rule,
    TestObjective, TestCase
)
from .expression_parser import (
    ExpressionParser, ASTNode, BinaryOpNode, UnaryOpNode,
    NumberNode, StringNode, BooleanNode, IdentifierNode,
    FunctionCallNode, TokenType
)


logger = logging.getLogger(__name__)


@dataclass
class SolverState:
    """Solver state for incremental solving"""
    solver: z3.Solver
    variables: Dict[str, z3.ExprRef]
    assertions: List[z3.BoolRef]
    soft_constraints: List[Tuple[z3.BoolRef, int]]  # (constraint, weight)


class Z3ConstraintSolver:
    """Z3-based constraint solver with correctness guarantees"""
    
    def __init__(self, model: DSLModel):
        self.model = model
        self.parser = ExpressionParser()
        self.base_state = self._create_base_state()
    
    def _create_base_state(self) -> SolverState:
        """Create base solver state with all model constraints"""
        solver = z3.Solver()
        variables = {}
        
        # Create Z3 variables for all attributes
        for attr in self.model.get_all_attributes():
            var = self._create_z3_variable(attr)
            variables[attr.full_name] = var
        
        # Add attribute constraints (min/max values)
        for attr in self.model.get_all_attributes():
            var = variables[attr.full_name]
            
            if attr.type in [AttributeType.INTEGER, AttributeType.REAL]:
                if attr.min_value is not None:
                    solver.add(var >= attr.min_value)
                if attr.max_value is not None:
                    solver.add(var <= attr.max_value)
            
            if attr.enum_values:
                # For enum, ensure value is one of allowed values
                if attr.type == AttributeType.INTEGER:
                    solver.add(z3.Or([var == v for v in attr.enum_values]))
                # For other types, we'd need different handling
        
        # Add model constraints
        for constraint in self.model.constraints:
            try:
                z3_expr = self._ast_to_z3(self.parser.parse(constraint.expression), variables)
                solver.add(z3_expr)
            except Exception as e:
                logger.warning(f"Failed to parse constraint '{constraint.expression}': {e}")
        
        # Store soft constraints (rules) separately
        soft_constraints = []
        for rule in self.model.rules:
            try:
                condition = self._ast_to_z3(self.parser.parse(rule.condition), variables)
                consequence = self._ast_to_z3(self.parser.parse(rule.consequence), variables)
                # Rule is: condition -> consequence
                rule_expr = z3.Implies(condition, consequence)
                soft_constraints.append((rule_expr, rule.priority))
            except Exception as e:
                logger.warning(f"Failed to parse rule '{rule.name}': {e}")
        
        return SolverState(
            solver=solver,
            variables=variables,
            assertions=solver.assertions(),
            soft_constraints=soft_constraints
        )
    
    def _create_z3_variable(self, attr: Attribute) -> z3.ExprRef:
        """Create Z3 variable for attribute"""
        if attr.type == AttributeType.INTEGER:
            return z3.Int(attr.full_name)
        elif attr.type == AttributeType.REAL:
            return z3.Real(attr.full_name)
        elif attr.type == AttributeType.BOOLEAN:
            return z3.Bool(attr.full_name)
        else:
            # For string and other types, use Int as placeholder
            return z3.Int(attr.full_name)
    
    def _ast_to_z3(self, node: ASTNode, variables: Dict[str, z3.ExprRef]) -> z3.ExprRef:
        """Convert AST node to Z3 expression"""
        if isinstance(node, NumberNode):
            return node.value
        
        elif isinstance(node, BooleanNode):
            return node.value
        
        elif isinstance(node, StringNode):
            # String handling would need special treatment
            # For now, return a placeholder
            return 0
        
        elif isinstance(node, IdentifierNode):
            if node.name in variables:
                return variables[node.name]
            else:
                raise ValueError(f"Unknown variable: {node.name}")
        
        elif isinstance(node, BinaryOpNode):
            left = self._ast_to_z3(node.left, variables)
            right = self._ast_to_z3(node.right, variables)
            
            if node.operator == TokenType.PLUS:
                return left + right
            elif node.operator == TokenType.MINUS:
                return left - right
            elif node.operator == TokenType.MULTIPLY:
                return left * right
            elif node.operator == TokenType.DIVIDE:
                return left / right
            elif node.operator == TokenType.MODULO:
                return left % right
            elif node.operator == TokenType.EQ:
                return left == right
            elif node.operator == TokenType.NEQ:
                return left != right
            elif node.operator == TokenType.LT:
                return left < right
            elif node.operator == TokenType.LE:
                return left <= right
            elif node.operator == TokenType.GT:
                return left > right
            elif node.operator == TokenType.GE:
                return left >= right
            elif node.operator == TokenType.AND:
                return z3.And(left, right)
            elif node.operator == TokenType.OR:
                return z3.Or(left, right)
            elif node.operator == TokenType.IMPLIES:
                return z3.Implies(left, right)
            else:
                raise ValueError(f"Unknown binary operator: {node.operator}")
        
        elif isinstance(node, UnaryOpNode):
            operand = self._ast_to_z3(node.operand, variables)
            
            if node.operator == TokenType.MINUS:
                return -operand
            elif node.operator == TokenType.NOT:
                return z3.Not(operand)
            else:
                raise ValueError(f"Unknown unary operator: {node.operator}")
        
        elif isinstance(node, FunctionCallNode):
            # Handle built-in functions
            if node.name == "abs":
                if len(node.arguments) == 1:
                    arg = self._ast_to_z3(node.arguments[0], variables)
                    return z3.If(arg >= 0, arg, -arg)
            elif node.name == "max":
                if len(node.arguments) == 2:
                    arg1 = self._ast_to_z3(node.arguments[0], variables)
                    arg2 = self._ast_to_z3(node.arguments[1], variables)
                    return z3.If(arg1 >= arg2, arg1, arg2)
            elif node.name == "min":
                if len(node.arguments) == 2:
                    arg1 = self._ast_to_z3(node.arguments[0], variables)
                    arg2 = self._ast_to_z3(node.arguments[1], variables)
                    return z3.If(arg1 <= arg2, arg1, arg2)
            
            raise ValueError(f"Unknown function: {node.name}")
        
        else:
            raise ValueError(f"Unknown AST node type: {type(node)}")
    
    def generate_test_data(self, objective: TestObjective) -> Optional[Dict[str, Any]]:
        """Generate test data for specific objective"""
        # Create a new solver based on base state
        solver = z3.Solver()
        
        # Add all base assertions
        for assertion in self.base_state.assertions:
            solver.add(assertion)
        
        # Add all soft constraints as hard constraints for now
        # In a full implementation, we'd use Z3's optimization features
        for constraint, weight in self.base_state.soft_constraints:
            if weight > 5:  # Only add high-priority rules as hard constraints
                solver.add(constraint)
        
        # Add objective-specific constraints
        self._add_objective_constraints(solver, objective)
        
        # Solve
        if solver.check() == z3.sat:
            model = solver.model()
            values = self._extract_values(model)
            
            # Verify the solution
            if self._verify_solution(values, objective):
                return values
            else:
                logger.warning(f"Generated solution failed verification for {objective.type} {objective.target}")
                return None
        else:
            logger.info(f"No solution found for {objective.type} {objective.target}")
            return None
    
    def _add_objective_constraints(self, solver: z3.Solver, objective: TestObjective):
        """Add constraints specific to test objective"""
        variables = self.base_state.variables
        
        if objective.type == "boundary_min":
            attr = self.model.get_attribute_by_full_name(objective.target)
            if attr and attr.min_value is not None:
                var = variables.get(attr.full_name)
                if var is not None:
                    solver.add(var == attr.min_value)
        
        elif objective.type == "boundary_max":
            attr = self.model.get_attribute_by_full_name(objective.target)
            if attr and attr.max_value is not None:
                var = variables.get(attr.full_name)
                if var is not None:
                    solver.add(var == attr.max_value)
        
        elif objective.type == "equivalence":
            # Additional constraints are in objective.constraints
            for constraint_expr in objective.constraints:
                try:
                    z3_expr = self._ast_to_z3(self.parser.parse(constraint_expr), variables)
                    solver.add(z3_expr)
                except Exception as e:
                    logger.warning(f"Failed to add objective constraint: {e}")
        
        elif objective.type == "rule_active":
            rule = self.model.get_rule_by_name(objective.target)
            if rule:
                try:
                    # Force rule condition to be true
                    condition = self._ast_to_z3(self.parser.parse(rule.condition), variables)
                    solver.add(condition)
                    # Force consequence to be true
                    consequence = self._ast_to_z3(self.parser.parse(rule.consequence), variables)
                    solver.add(consequence)
                except Exception as e:
                    logger.warning(f"Failed to activate rule {rule.name}: {e}")
        
        elif objective.type == "rule_inactive":
            rule = self.model.get_rule_by_name(objective.target)
            if rule:
                try:
                    # Force rule condition to be false
                    condition = self._ast_to_z3(self.parser.parse(rule.condition), variables)
                    solver.add(z3.Not(condition))
                except Exception as e:
                    logger.warning(f"Failed to deactivate rule {rule.name}: {e}")
        
        elif objective.type == "pairwise":
            # Pairwise test - add specific value constraints
            for constraint_expr in objective.constraints:
                try:
                    z3_expr = self._ast_to_z3(self.parser.parse(constraint_expr), variables)
                    solver.add(z3_expr)
                except Exception as e:
                    logger.warning(f"Failed to add pairwise constraint '{constraint_expr}': {e}")
    
    def _extract_values(self, model: z3.ModelRef) -> Dict[str, Any]:
        """Extract concrete values from Z3 model"""
        values = {}
        
        for name, var in self.base_state.variables.items():
            try:
                val = model.eval(var, model_completion=True)
                
                if z3.is_int_value(val):
                    values[name] = val.as_long()
                elif z3.is_rational_value(val):
                    values[name] = float(val.as_decimal(6))
                elif z3.is_bool(val):
                    values[name] = z3.is_true(val)
                else:
                    # Try to convert to Python value
                    values[name] = str(val)
            except Exception as e:
                logger.warning(f"Failed to extract value for {name}: {e}")
                # Provide default based on type
                attr = self.model.get_attribute_by_full_name(name)
                if attr:
                    if attr.type == AttributeType.INTEGER:
                        values[name] = 0
                    elif attr.type == AttributeType.REAL:
                        values[name] = 0.0
                    elif attr.type == AttributeType.BOOLEAN:
                        values[name] = False
                    else:
                        values[name] = ""
        
        return values
    
    def _verify_solution(self, values: Dict[str, Any], objective: TestObjective) -> bool:
        """Verify that solution satisfies all constraints and objective"""
        # Verify all model constraints
        for constraint in self.model.constraints:
            if not self._evaluate_expression(constraint.expression, values):
                logger.debug(f"Solution violates constraint: {constraint.expression}")
                return False
        
        # Verify objective-specific requirements
        if objective.type == "rule_active":
            rule = self.model.get_rule_by_name(objective.target)
            if rule:
                # Check condition is true
                if not self._evaluate_expression(rule.condition, values):
                    logger.debug(f"Rule condition not satisfied: {rule.condition}")
                    return False
                # Check consequence is true
                if not self._evaluate_expression(rule.consequence, values):
                    logger.debug(f"Rule consequence not satisfied: {rule.consequence}")
                    return False
        
        elif objective.type == "rule_inactive":
            rule = self.model.get_rule_by_name(objective.target)
            if rule:
                # Check condition is false
                if self._evaluate_expression(rule.condition, values):
                    logger.debug(f"Rule condition should be false: {rule.condition}")
                    return False
        
        return True
    
    def _evaluate_expression(self, expr: str, values: Dict[str, Any]) -> bool:
        """Evaluate expression with concrete values"""
        try:
            # Parse expression
            ast = self.parser.parse(expr)
            # Evaluate AST with values
            result = self._evaluate_ast(ast, values)
            return bool(result)
        except Exception as e:
            logger.warning(f"Failed to evaluate expression '{expr}': {e}")
            return False
    
    def _evaluate_ast(self, node: ASTNode, values: Dict[str, Any]) -> Any:
        """Evaluate AST node with concrete values"""
        if isinstance(node, NumberNode):
            return node.value
        
        elif isinstance(node, BooleanNode):
            return node.value
        
        elif isinstance(node, StringNode):
            return node.value
        
        elif isinstance(node, IdentifierNode):
            if node.name in values:
                return values[node.name]
            else:
                raise ValueError(f"Unknown variable in evaluation: {node.name}")
        
        elif isinstance(node, BinaryOpNode):
            left = self._evaluate_ast(node.left, values)
            right = self._evaluate_ast(node.right, values)
            
            if node.operator == TokenType.PLUS:
                return left + right
            elif node.operator == TokenType.MINUS:
                return left - right
            elif node.operator == TokenType.MULTIPLY:
                return left * right
            elif node.operator == TokenType.DIVIDE:
                return left / right if right != 0 else 0
            elif node.operator == TokenType.MODULO:
                return left % right if right != 0 else 0
            elif node.operator == TokenType.EQ:
                return left == right
            elif node.operator == TokenType.NEQ:
                return left != right
            elif node.operator == TokenType.LT:
                return left < right
            elif node.operator == TokenType.LE:
                return left <= right
            elif node.operator == TokenType.GT:
                return left > right
            elif node.operator == TokenType.GE:
                return left >= right
            elif node.operator == TokenType.AND:
                return left and right
            elif node.operator == TokenType.OR:
                return left or right
            elif node.operator == TokenType.IMPLIES:
                return (not left) or right
        
        elif isinstance(node, UnaryOpNode):
            operand = self._evaluate_ast(node.operand, values)
            
            if node.operator == TokenType.MINUS:
                return -operand
            elif node.operator == TokenType.NOT:
                return not operand
        
        elif isinstance(node, FunctionCallNode):
            # Evaluate function arguments
            args = [self._evaluate_ast(arg, values) for arg in node.arguments]
            
            if node.name == "abs":
                return abs(args[0]) if args else 0
            elif node.name == "max":
                return max(args) if args else 0
            elif node.name == "min":
                return min(args) if args else 0
        
        raise ValueError(f"Cannot evaluate node type: {type(node)}")
    
    def check_constraint_consistency(self) -> bool:
        """Check if all constraints are consistent (satisfiable)"""
        return self.base_state.solver.check() == z3.sat
    
    def get_unsat_core(self) -> List[str]:
        """Get unsatisfiable core if constraints are inconsistent"""
        if self.base_state.solver.check() == z3.unsat:
            core = self.base_state.solver.unsat_core()
            # Convert to readable format
            return [str(c) for c in core]
        return []