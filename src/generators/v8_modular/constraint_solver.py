"""
Constraint Solver Module - V8
集成Z3 SMT求解器，提供高级约束求解能力
"""

import z3
import random
from typing import Any, Dict, List, Optional, Set, Tuple, Union
from datetime import datetime, timedelta
import logging
from .expression_parser import ExpressionParser

logger = logging.getLogger(__name__)


class ConstraintSolver:
    """
    高级约束求解器，使用Z3 SMT求解器
    """
    
    def __init__(self, timeout_ms: int = 5000):
        self.parser = ExpressionParser()
        self.timeout_ms = timeout_ms
        self.solver = z3.Solver()
        self.solver.set("timeout", timeout_ms)
        self.variables = {}
        self.constraints = []
        
    def solve(self, constraints: List[str], variables: Dict[str, Dict[str, Any]], 
              num_solutions: int = 1) -> List[Dict[str, Any]]:
        """
        求解约束系统，返回满足所有约束的解
        
        Args:
            constraints: 约束表达式列表
            variables: 变量定义 {name: {type: 'int'/'string'/'bool', range: [min, max]}}
            num_solutions: 需要的解的数量
            
        Returns:
            满足约束的解列表
        """
        try:
            # 重置求解器
            self.solver.reset()
            self.variables.clear()
            self.constraints.clear()
            
            # 创建Z3变量
            self._create_z3_variables(variables)
            
            # 添加约束
            for constraint in constraints:
                self._add_constraint(constraint)
            
            # 求解
            solutions = []
            for i in range(num_solutions):
                if self.solver.check() == z3.sat:
                    model = self.solver.model()
                    solution = self._extract_solution(model)
                    solutions.append(solution)
                    
                    # 添加排除当前解的约束，以获得不同的解
                    if i < num_solutions - 1:
                        self._exclude_solution(model)
                else:
                    break
            
            return solutions if solutions else [self._get_default_solution(variables)]
            
        except Exception as e:
            logger.warning(f"Z3 solver failed: {e}")
            return [self._get_default_solution(variables)]
    
    def check_constraint_satisfaction(self, constraint: str, values: Dict[str, Any]) -> bool:
        """
        检查给定值是否满足约束
        
        Args:
            constraint: 约束表达式
            values: 变量值字典
            
        Returns:
            是否满足约束
        """
        try:
            ast = self.parser.parse(constraint)
            result = self.parser.evaluate(ast, values)
            return bool(result)
        except Exception as e:
            logger.warning(f"Failed to check constraint '{constraint}': {e}")
            return True  # 默认满足
    
    def find_constraint_violations(self, constraints: List[str], 
                                  values: Dict[str, Any]) -> List[str]:
        """
        找出被违反的约束
        
        Args:
            constraints: 约束列表
            values: 变量值字典
            
        Returns:
            被违反的约束列表
        """
        violations = []
        for constraint in constraints:
            if not self.check_constraint_satisfaction(constraint, values):
                violations.append(constraint)
        return violations
    
    def generate_boundary_values(self, constraint: str, 
                               variables: Dict[str, Dict[str, Any]]) -> List[Dict[str, Any]]:
        """
        生成边界值测试用例
        
        Args:
            constraint: 约束表达式
            variables: 变量定义
            
        Returns:
            边界值测试用例列表
        """
        boundary_cases = []
        
        try:
            # 解析约束获取比较操作
            ast = self.parser.parse(constraint)
            comparisons = self._extract_comparisons(ast)
            
            for comp in comparisons:
                var_name = comp['variable']
                op = comp['operator']
                value = comp['value']
                
                if var_name in variables:
                    var_info = variables[var_name]
                    
                    # 生成边界值
                    if op in ['>', '>=']:
                        # 刚好满足的值
                        boundary_cases.append({var_name: value if op == '>=' else value + 1})
                        # 刚好不满足的值
                        boundary_cases.append({var_name: value - 1 if op == '>=' else value})
                        
                    elif op in ['<', '<=']:
                        # 刚好满足的值
                        boundary_cases.append({var_name: value if op == '<=' else value - 1})
                        # 刚好不满足的值
                        boundary_cases.append({var_name: value + 1 if op == '<=' else value})
                        
                    elif op == '==':
                        # 相等和不等的值
                        boundary_cases.append({var_name: value})
                        boundary_cases.append({var_name: value + 1})
                        boundary_cases.append({var_name: value - 1})
                        
        except Exception as e:
            logger.warning(f"Failed to generate boundary values: {e}")
        
        # 补充其他变量的默认值
        complete_cases = []
        for case in boundary_cases:
            complete_case = self._get_default_solution(variables)
            complete_case.update(case)
            complete_cases.append(complete_case)
        
        return complete_cases
    
    def generate_constraint_covering_tests(self, constraints: List[str],
                                         variables: Dict[str, Dict[str, Any]]) -> List[Dict[str, Any]]:
        """
        生成覆盖所有约束的测试用例
        
        Args:
            constraints: 约束列表
            variables: 变量定义
            
        Returns:
            覆盖约束的测试用例列表
        """
        test_cases = []
        
        # 1. 全部满足的用例
        all_satisfied = self.solve(constraints, variables, num_solutions=3)
        test_cases.extend(all_satisfied)
        
        # 2. 逐个违反的用例
        for i, constraint in enumerate(constraints):
            # 除了当前约束，其他都满足
            other_constraints = constraints[:i] + constraints[i+1:]
            negated_constraint = self._negate_constraint(constraint)
            
            if negated_constraint:
                violated_cases = self.solve(
                    other_constraints + [negated_constraint], 
                    variables, 
                    num_solutions=1
                )
                test_cases.extend(violated_cases)
        
        # 3. 边界值用例
        for constraint in constraints:
            boundary_cases = self.generate_boundary_values(constraint, variables)
            test_cases.extend(boundary_cases[:2])  # 每个约束取2个边界值
        
        return self._deduplicate_test_cases(test_cases)
    
    # Private methods
    def _create_z3_variables(self, variables: Dict[str, Dict[str, Any]]):
        """创建Z3变量"""
        for name, info in variables.items():
            var_type = info.get('type', 'int')
            
            if var_type == 'int':
                var = z3.Int(name)
                self.variables[name] = var
                
                # 添加范围约束
                if 'range' in info:
                    min_val, max_val = info['range']
                    self.solver.add(var >= min_val)
                    self.solver.add(var <= max_val)
                    
            elif var_type == 'bool':
                var = z3.Bool(name)
                self.variables[name] = var
                
            elif var_type == 'string':
                # Z3对字符串支持有限，使用枚举代替
                var = z3.Int(name)  # 用整数表示字符串选项
                self.variables[name] = var
                
                if 'options' in info:
                    self.solver.add(var >= 0)
                    self.solver.add(var < len(info['options']))
    
    def _add_constraint(self, constraint: str):
        """添加约束到求解器"""
        try:
            z3_constraint = self._convert_to_z3(constraint)
            if z3_constraint is not None:
                self.solver.add(z3_constraint)
                self.constraints.append(constraint)
        except Exception as e:
            logger.warning(f"Failed to add constraint '{constraint}': {e}")
    
    def _convert_to_z3(self, constraint: str) -> Optional[z3.BoolRef]:
        """将约束表达式转换为Z3表达式"""
        try:
            ast = self.parser.parse(constraint)
            return self._ast_to_z3(ast)
        except Exception as e:
            logger.warning(f"Failed to convert constraint to Z3: {e}")
            return None
    
    def _ast_to_z3(self, ast: Dict[str, Any]) -> Optional[z3.BoolRef]:
        """将AST转换为Z3表达式"""
        node_type = ast.get('type')
        
        if node_type == 'binary':
            left = self._ast_to_z3(ast['left'])
            right = self._ast_to_z3(ast['right'])
            op = ast['operator']
            
            if left is None or right is None:
                return None
            
            if op == '>':
                return left > right
            elif op == '<':
                return left < right
            elif op == '>=':
                return left >= right
            elif op == '<=':
                return left <= right
            elif op == '==':
                return left == right
            elif op == '!=':
                return left != right
            elif op == 'and':
                return z3.And(left, right)
            elif op == 'or':
                return z3.Or(left, right)
            elif op == '=>':
                return z3.Implies(left, right)
            elif op == '+':
                return left + right
            elif op == '-':
                return left - right
            elif op == '*':
                return left * right
            elif op == '/':
                return left / right
                
        elif node_type == 'unary':
            operand = self._ast_to_z3(ast['operand'])
            if ast['operator'] == 'not' and operand is not None:
                return z3.Not(operand)
                
        elif node_type == 'identifier':
            name = ast['value']
            if name in self.variables:
                return self.variables[name]
            # 尝试解析为entity_attribute格式
            parts = name.split('_')
            if len(parts) > 1:
                attr_name = '_'.join(parts[1:])
                if attr_name in self.variables:
                    return self.variables[attr_name]
                    
        elif node_type == 'number':
            return ast['value']
            
        elif node_type == 'boolean':
            return ast['value']
            
        elif node_type == 'function_call':
            # 简化处理，暂不支持复杂函数
            return None
            
        return None
    
    def _extract_solution(self, model: z3.ModelRef) -> Dict[str, Any]:
        """从Z3模型中提取解"""
        solution = {}
        
        for name, var in self.variables.items():
            try:
                value = model[var]
                if value is not None:
                    # 转换Z3值为Python值
                    if z3.is_int(var):
                        solution[name] = value.as_long()
                    elif z3.is_bool(var):
                        solution[name] = bool(value)
                    else:
                        solution[name] = str(value)
            except:
                # 如果变量在模型中未定义，使用默认值
                pass
        
        return solution
    
    def _exclude_solution(self, model: z3.ModelRef):
        """添加约束排除当前解"""
        exclusion = []
        for name, var in self.variables.items():
            try:
                value = model[var]
                if value is not None:
                    exclusion.append(var != value)
            except:
                pass
        
        if exclusion:
            self.solver.add(z3.Or(exclusion))
    
    def _get_default_solution(self, variables: Dict[str, Dict[str, Any]]) -> Dict[str, Any]:
        """生成默认解"""
        solution = {}
        
        for name, info in variables.items():
            var_type = info.get('type', 'int')
            
            if var_type == 'int':
                if 'range' in info:
                    min_val, max_val = info['range']
                    solution[name] = random.randint(min_val, max_val)
                else:
                    solution[name] = random.randint(1, 100)
                    
            elif var_type == 'bool':
                solution[name] = random.choice([True, False])
                
            elif var_type == 'string':
                if 'options' in info:
                    solution[name] = random.choice(info['options'])
                else:
                    solution[name] = f"{name}_value"
                    
            elif var_type == 'float':
                if 'range' in info:
                    min_val, max_val = info['range']
                    solution[name] = round(random.uniform(min_val, max_val), 2)
                else:
                    solution[name] = round(random.uniform(0, 100), 2)
        
        return solution
    
    def _extract_comparisons(self, ast: Dict[str, Any]) -> List[Dict[str, Any]]:
        """从AST中提取比较操作"""
        comparisons = []
        
        if ast.get('type') == 'binary' and ast.get('operator') in ['>', '<', '>=', '<=', '==', '!=']:
            left = ast['left']
            right = ast['right']
            
            # 简化处理：假设左边是变量，右边是值
            if left.get('type') == 'identifier' and right.get('type') == 'number':
                comparisons.append({
                    'variable': left['value'],
                    'operator': ast['operator'],
                    'value': right['value']
                })
        
        # 递归处理
        for key in ['left', 'right', 'operand']:
            if key in ast and isinstance(ast[key], dict):
                comparisons.extend(self._extract_comparisons(ast[key]))
        
        return comparisons
    
    def _negate_constraint(self, constraint: str) -> Optional[str]:
        """对约束取反"""
        try:
            # 简单的取反规则
            negation_map = {
                '>': '<=',
                '<': '>=',
                '>=': '<',
                '<=': '>',
                '==': '!=',
                '!=': '=='
            }
            
            for op, neg_op in negation_map.items():
                if f' {op} ' in constraint:
                    return constraint.replace(f' {op} ', f' {neg_op} ')
            
            # 对于复杂约束，添加not
            return f"not ({constraint})"
            
        except Exception:
            return None
    
    def _deduplicate_test_cases(self, test_cases: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """去除重复的测试用例"""
        seen = set()
        unique_cases = []
        
        for case in test_cases:
            # 创建可哈希的表示
            case_tuple = tuple(sorted((k, v) for k, v in case.items()))
            if case_tuple not in seen:
                seen.add(case_tuple)
                unique_cases.append(case)
        
        return unique_cases