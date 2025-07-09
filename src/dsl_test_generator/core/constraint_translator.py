"""Translate DSL constraints to Z3 expressions with collection support."""

import re
from typing import Any, Dict, List, Optional
import z3

from ..types import DSLModel, Constraint, Rule
from ..config import DSLEngineConfig, default_config


class ConstraintTranslator:
    """Translate DSL constraints to Z3 expressions."""
    
    def __init__(self, variables: Dict[str, Any], array_vars: Dict[str, Any], set_vars: Dict[str, Any], 
                 config: Optional[DSLEngineConfig] = None):
        self.variables = variables
        self.array_vars = array_vars
        self.set_vars = set_vars
        self.config = config or default_config
        
        # Define operators from config
        self.operators = {}
        for dsl_op, z3_op_name in self.config.operators.logical_operators.items():
            if z3_op_name == 'And':
                self.operators[dsl_op] = z3.And
            elif z3_op_name == 'Or':
                self.operators[dsl_op] = z3.Or
            elif z3_op_name == 'Not':
                self.operators[dsl_op] = z3.Not
            elif z3_op_name == 'Implies':
                self.operators[dsl_op] = z3.Implies
    
    def translate_constraint(self, constraint: Constraint) -> Optional[Any]:
        """Translate a constraint to Z3 expression."""
        try:
            result = self._parse_expression(constraint.expression)
            # Ensure we return a boolean expression
            if result is None:
                return None
            # If it's already a Z3 expression, return it
            if hasattr(result, 'sort') and hasattr(result.sort(), 'is_bool'):
                if result.sort().is_bool():
                    return result
            # If it's a Python bool, convert to Z3
            if isinstance(result, bool):
                return z3.BoolVal(result)
            # Otherwise, we have a problem
            print(f"Warning: Constraint '{constraint.expression}' did not produce a boolean expression")
            return None
        except Exception as e:
            print(f"Warning: Failed to translate constraint '{constraint.expression}': {e}")
            return None
    
    def translate_rule(self, rule: Rule) -> Optional[Any]:
        """Translate a rule to Z3 expression."""
        try:
            condition = self._parse_expression(rule.condition)
            
            if rule.implies:
                consequence = self._parse_expression(rule.implies)
                return z3.Implies(condition, consequence)
            
            # For action-based rules, we just check the condition
            return condition
        except Exception as e:
            print(f"Warning: Failed to translate rule '{rule.name}': {e}")
            return None
    
    def _parse_expression(self, expr: str) -> Any:
        """Parse and translate expression to Z3."""
        expr = expr.strip()
        
        # Handle collection operations (but not within comparisons)
        if ' in ' in expr and not any(op in expr for op in ['>=', '<=', '==', '!=', '>', '<']):
            return self._parse_membership(expr)
        elif ' contains ' in expr and not any(op in expr for op in ['>=', '<=', '==', '!=', '>', '<']):
            return self._parse_contains(expr)
        elif ' subset ' in expr:
            return self._parse_subset(expr)
        
        # Handle implication operator first (->)
        if ' -> ' in expr:
            parts = expr.split(' -> ', 1)
            if len(parts) == 2:
                left = self._parse_expression(parts[0])
                right = self._parse_expression(parts[1])
                return z3.Implies(left, right)
        
        # Handle logical operators
        for op_str, op_func in self.operators.items():
            if f' {op_str} ' in expr:
                parts = expr.split(f' {op_str} ', 1)
                if len(parts) == 2:
                    left = self._parse_expression(parts[0])
                    right = self._parse_expression(parts[1])
                    return op_func(left, right)
        
        # Handle comparisons
        comparison_ops = ['>=', '<=', '==', '!=', '>', '<']
        for op in comparison_ops:
            if op in expr:
                parts = expr.split(op, 1)
                if len(parts) == 2:
                    left = self._parse_term(parts[0].strip())
                    right = self._parse_term(parts[1].strip())
                    
                    if op == '>=':
                        return left >= right
                    elif op == '<=':
                        return left <= right
                    elif op == '==':
                        return left == right
                    elif op == '!=':
                        return left != right
                    elif op == '>':
                        return left > right
                    elif op == '<':
                        return left < right
        
        # Handle parentheses
        if expr.startswith('(') and expr.endswith(')'):
            return self._parse_expression(expr[1:-1])
        
        # Handle negation
        if expr.startswith('not '):
            return z3.Not(self._parse_expression(expr[4:]))
        
        # Single term
        return self._parse_term(expr)
    
    def _parse_term(self, term: str) -> Any:
        """Parse a single term."""
        term = term.strip()
        
        # Handle size() function calls
        if term.startswith('size(') or term.startswith('length('):
            return self._parse_size(term)
        
        # Boolean literals
        if term.lower() == 'true':
            return True
        elif term.lower() == 'false':
            return False
        
        # Numeric literals
        try:
            if '.' in term:
                return float(term)
            else:
                return int(term)
        except ValueError:
            pass
        
        # String literals
        if term.startswith('"') and term.endswith('"'):
            return term[1:-1]
        
        # Variables - exact match first
        if term in self.variables:
            return self.variables[term]
        
        # Array/set references
        if '[' in term and ']' in term:
            return self._parse_array_access(term)
        
        # Try to find exact suffix match (e.g., 'age' matches 'customer_age')
        # This handles cases where DSL uses short names but variables have entity prefixes
        for var_name in self.variables:
            if var_name.endswith('_' + term):
                return self.variables[var_name]
        
        raise ValueError(f"Unknown term: {term}")
    
    def _parse_membership(self, expr: str) -> Any:
        """Parse membership expression (element in collection)."""
        parts = expr.split(' in ', 1)
        if len(parts) != 2:
            raise ValueError(f"Invalid membership expression: {expr}")
        
        element_str = parts[0].strip()
        collection_name = parts[1].strip()
        
        # For string elements in sets, we need to handle them specially
        # For now, use integer encoding for strings
        if element_str.startswith('"') and element_str.endswith('"'):
            # Hash the string to get an integer representation
            element = abs(hash(element_str[1:-1])) % self.config.test_generation.string_hash_modulo
        else:
            element = self._parse_term(element_str)
        
        if collection_name in self.set_vars:
            # For sets: check if element is in set
            return self.set_vars[collection_name][element]
        elif collection_name in self.array_vars:
            # For arrays: check if element exists in array
            size_var = self.variables.get(f"{collection_name}_size", 0)
            array = self.array_vars[collection_name]
            
            # Check if element equals any array element within bounds
            conditions = []
            for i in range(self.config.test_generation.array_membership_check_limit):  # Check first N positions
                conditions.append(
                    z3.And(i < size_var, array[i] == element)
                )
            return z3.Or(conditions)
        
        raise ValueError(f"Unknown collection: {collection_name}")
    
    def _parse_contains(self, expr: str) -> Any:
        """Parse contains expression (collection contains element)."""
        parts = expr.split(' contains ', 1)
        if len(parts) != 2:
            raise ValueError(f"Invalid contains expression: {expr}")
        
        collection_name = parts[0].strip()
        element = self._parse_term(parts[1].strip())
        
        if collection_name in self.set_vars:
            return self.set_vars[collection_name][element]
        elif collection_name in self.array_vars:
            size_var = self.variables.get(f"{collection_name}_size", 0)
            array = self.array_vars[collection_name]
            
            conditions = []
            for i in range(self.config.test_generation.array_membership_check_limit):  # Check first N positions
                conditions.append(
                    z3.And(i < size_var, array[i] == element)
                )
            return z3.Or(conditions)
        
        raise ValueError(f"Unknown collection: {collection_name}")
    
    def _parse_size(self, expr: str) -> Any:
        """Parse size/length expression."""
        # This should return just the size variable reference, not a boolean
        # The comparison will be handled by the parent expression parser
        
        # Extract collection name from size(collection) or collection.size
        match = re.match(r'(?:size|length)\s*\(\s*(\w+)\s*\)', expr)
        if match:
            collection_name = match.group(1)
        else:
            match = re.match(r'(\w+)\s*\.\s*(?:size|length)', expr)
            if match:
                collection_name = match.group(1)
            else:
                raise ValueError(f"Invalid size expression: {expr}")
        
        # Look for the size variable with various prefixes
        # Try exact match first
        size_var_name = f"{collection_name}_size"
        if size_var_name in self.variables:
            return self.variables[size_var_name]
        
        # Try with entity prefix
        for var_name in self.variables:
            if var_name.endswith(f"_{collection_name}_size"):
                return self.variables[var_name]
        
        raise ValueError(f"Unknown collection size: {collection_name}")
    
    def _parse_subset(self, expr: str) -> Any:
        """Parse subset expression."""
        parts = expr.split(' subset ', 1)
        if len(parts) != 2:
            raise ValueError(f"Invalid subset expression: {expr}")
        
        set1_name = parts[0].strip()
        set2_name = parts[1].strip()
        
        if set1_name in self.set_vars and set2_name in self.set_vars:
            # For all elements, if in set1 then in set2
            conditions = []
            for i in range(self.config.test_generation.set_domain_check_limit):  # Check domain
                conditions.append(
                    z3.Implies(
                        self.set_vars[set1_name][i],
                        self.set_vars[set2_name][i]
                    )
                )
            return z3.And(conditions)
        
        raise ValueError(f"Unknown sets: {set1_name}, {set2_name}")
    
    def _parse_array_access(self, term: str) -> Any:
        """Parse array access like array[index]."""
        match = re.match(r'(\w+)\[(\w+|\d+)\]', term)
        if not match:
            raise ValueError(f"Invalid array access: {term}")
        
        array_name = match.group(1)
        index = match.group(2)
        
        if array_name in self.array_vars:
            if index.isdigit():
                return self.array_vars[array_name][int(index)]
            elif index in self.variables:
                return self.array_vars[array_name][self.variables[index]]
        
        raise ValueError(f"Unknown array access: {term}")