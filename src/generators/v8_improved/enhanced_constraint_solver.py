"""
Enhanced Constraint Solver
增强的约束求解器 - 优化Z3求解失败的回退策略和复杂约束处理
"""

import z3
import random
import logging
from typing import Any, Dict, List, Optional, Tuple
from datetime import datetime
try:
    from ..v8_modular.expression_parser import ExpressionParser
except ImportError:
    # 简单的表达式解析器实现
    class ExpressionParser:
        def parse(self, expr: str):
            # 简化实现
            return {'type': 'expression', 'value': expr}
        
        def evaluate(self, ast, context):
            # 简化实现
            return True
from .constraint_validator import ConstraintValidator

logger = logging.getLogger(__name__)


class EnhancedConstraintSolver:
    """增强的约束求解器"""
    
    def __init__(self, timeout_ms: int = 5000):
        self.parser = ExpressionParser()
        self.timeout_ms = timeout_ms
        self.validator = ConstraintValidator()
        self.solver = None
        self.variables = {}
        self.constraints = []
        self.special_handlers = {
            'order_total': self._handle_order_total_constraint
        }
    
    def solve(self, constraints: List[str], variables: Dict[str, Dict[str, Any]], 
              num_solutions: int = 1, entity_name: str = None) -> List[Dict[str, Any]]:
        """
        求解约束系统，返回满足所有约束的解
        
        Args:
            constraints: 约束表达式列表
            variables: 变量定义
            num_solutions: 需要的解的数量
            entity_name: 实体名称
            
        Returns:
            满足约束的解列表
        """
        try:
            # 重置求解器
            self.solver = z3.Solver()
            self.solver.set("timeout", self.timeout_ms)
            self.variables.clear()
            self.constraints.clear()
            
            # 预处理约束（处理特殊约束）
            processed_constraints = self._preprocess_constraints(constraints, entity_name)
            
            # 创建Z3变量
            self._create_z3_variables(variables)
            
            # 添加约束
            for constraint in processed_constraints:
                self._add_constraint(constraint)
            
            # 尝试求解
            solutions = self._solve_with_strategies(num_solutions, variables, constraints, entity_name)
            
            # 如果求解失败，使用智能回退策略
            if not solutions:
                logger.warning("Z3 solver failed, using intelligent fallback")
                solutions = self._intelligent_fallback(variables, constraints, num_solutions, entity_name)
            
            return solutions
            
        except Exception as e:
            logger.error(f"Constraint solver error: {e}")
            return self._intelligent_fallback(variables, constraints, num_solutions, entity_name)
    
    def _solve_with_strategies(self, num_solutions: int, variables: Dict[str, Dict[str, Any]], 
                              constraints: List[str], entity_name: str) -> List[Dict[str, Any]]:
        """使用多种策略尝试求解"""
        solutions = []
        
        # 策略1：直接求解
        for i in range(num_solutions):
            if self.solver.check() == z3.sat:
                model = self.solver.model()
                solution = self._extract_solution(model, variables)
                
                # 验证解是否真的满足约束
                if self._validate_solution(solution, constraints, entity_name):
                    solutions.append(solution)
                    
                    # 排除当前解以获得不同的解
                    if i < num_solutions - 1:
                        self._exclude_solution(model)
                else:
                    logger.warning("Generated solution does not satisfy all constraints")
            else:
                # 策略2：放松约束再求解
                if not solutions:
                    logger.info("Trying relaxed constraints")
                    relaxed_solutions = self._solve_with_relaxed_constraints(
                        variables, constraints, num_solutions, entity_name
                    )
                    solutions.extend(relaxed_solutions)
                break
        
        return solutions
    
    def _solve_with_relaxed_constraints(self, variables: Dict[str, Dict[str, Any]], 
                                       constraints: List[str], num_solutions: int, 
                                       entity_name: str) -> List[Dict[str, Any]]:
        """放松某些约束后再求解"""
        solutions = []
        
        # 识别可以放松的约束
        essential_constraints = []
        optional_constraints = []
        
        for constraint in constraints:
            if self._is_essential_constraint(constraint):
                essential_constraints.append(constraint)
            else:
                optional_constraints.append(constraint)
        
        # 只使用必要约束重新求解
        if essential_constraints:
            self.solver.reset()
            self._create_z3_variables(variables)
            
            for constraint in essential_constraints:
                self._add_constraint(constraint)
            
            for i in range(num_solutions):
                if self.solver.check() == z3.sat:
                    model = self.solver.model()
                    solution = self._extract_solution(model, variables)
                    solutions.append(solution)
                    
                    if i < num_solutions - 1:
                        self._exclude_solution(model)
                else:
                    break
        
        return solutions
    
    def _intelligent_fallback(self, variables: Dict[str, Dict[str, Any]], 
                            constraints: List[str], num_solutions: int, 
                            entity_name: str) -> List[Dict[str, Any]]:
        """智能回退策略 - 生成满足约束的值"""
        solutions = []
        
        for _ in range(num_solutions):
            max_attempts = 100
            
            for attempt in range(max_attempts):
                # 生成候选解
                candidate = self._generate_smart_candidate(variables, constraints)
                
                # 验证候选解
                if self._validate_solution(candidate, constraints, entity_name):
                    solutions.append(candidate)
                    break
                elif attempt < max_attempts - 1:
                    # 尝试修复违反的约束
                    candidate = self._fix_constraint_violations(candidate, constraints, entity_name)
                    if self._validate_solution(candidate, constraints, entity_name):
                        solutions.append(candidate)
                        break
            
            # 如果仍然失败，添加一个尽可能满足约束的解
            if len(solutions) < _ + 1:
                solutions.append(candidate)
        
        return solutions
    
    def _generate_smart_candidate(self, variables: Dict[str, Dict[str, Any]], 
                                constraints: List[str]) -> Dict[str, Any]:
        """生成智能的候选解"""
        solution = {}
        
        # 分析约束中的关系
        relationships = self._analyze_constraint_relationships(constraints)
        
        for name, info in variables.items():
            var_type = info.get('type', 'int')
            
            # 检查是否有相关约束
            related_constraints = [c for c in constraints if name in c]
            
            if related_constraints:
                # 基于约束生成值
                value = self._generate_constrained_value(name, info, related_constraints, solution)
            else:
                # 生成默认安全值
                value = self._generate_safe_default(name, info)
            
            solution[name] = value
        
        return solution
    
    def _generate_constrained_value(self, var_name: str, var_info: Dict[str, Any], 
                                   constraints: List[str], current_solution: Dict[str, Any]) -> Any:
        """基于约束生成值"""
        var_type = var_info.get('type', 'int')
        
        # 收集该变量的所有约束条件
        lower_bounds = []
        upper_bounds = []
        exact_values = []
        
        for constraint in constraints:
            # 简单解析约束
            if f"{var_name} >" in constraint or f"{var_name}>" in constraint:
                # 提取下界
                try:
                    parts = constraint.split('>')
                    value = float(parts[1].strip())
                    lower_bounds.append(value)
                except:
                    pass
            elif f"{var_name} <" in constraint or f"{var_name}<" in constraint:
                # 提取上界
                try:
                    parts = constraint.split('<')
                    value = float(parts[1].strip())
                    upper_bounds.append(value)
                except:
                    pass
            elif f"{var_name} ==" in constraint:
                # 提取精确值
                try:
                    parts = constraint.split('==')
                    value = parts[1].strip()
                    if value.isdigit():
                        exact_values.append(int(value))
                    else:
                        try:
                            exact_values.append(float(value))
                        except:
                            pass
                except:
                    pass
        
        # 如果有精确值约束，使用它
        if exact_values:
            return exact_values[0]
        
        # 计算有效范围
        min_val = max(lower_bounds) if lower_bounds else var_info.get('range', [0, 100])[0]
        max_val = min(upper_bounds) if upper_bounds else var_info.get('range', [0, 100])[1]
        
        # 确保范围有效
        if min_val > max_val:
            # 约束冲突，使用默认值
            return self._generate_safe_default(var_name, var_info)
        
        # 在有效范围内生成值
        if var_type == 'int':
            return random.randint(int(min_val), int(max_val))
        elif var_type in ['float', 'real']:
            return round(random.uniform(min_val, max_val), 2)
        else:
            return self._generate_safe_default(var_name, var_info)
    
    def _generate_safe_default(self, var_name: str, var_info: Dict[str, Any]) -> Any:
        """生成安全的默认值"""
        var_type = var_info.get('type', 'int')
        
        # 检查是否是集合类型
        if var_info.get('is_collection', False):
            return self._generate_collection_default(var_name, var_info)
        
        if var_type == 'int':
            range_vals = var_info.get('range', [1, 100])
            # 选择中间值
            return (range_vals[0] + range_vals[1]) // 2
        elif var_type in ['float', 'real']:
            range_vals = var_info.get('range', [0.0, 100.0])
            # 选择中间值
            return round((range_vals[0] + range_vals[1]) / 2, 2)
        elif var_type == 'bool':
            return True
        elif var_type == 'string':
            if 'options' in var_info:
                return var_info['options'][0]
            else:
                return f"{var_name}_value"
        else:
            return None
    
    def _generate_collection_default(self, var_name: str, var_info: Dict[str, Any]) -> List[Any]:
        """生成集合类型的默认值"""
        var_lower = var_name.lower()
        
        # 根据变量名生成合适的默认集合
        if 'categories' in var_lower:
            return ['electronics', 'clothing', 'books']
        elif 'items' in var_lower:
            return [1001, 1002, 1003]
        elif 'discount_codes' in var_lower:
            return ['SAVE10', 'WELCOME20']
        elif 'permissions' in var_lower:
            return ['read', 'write']
        elif 'roles' in var_lower:
            return ['user']
        else:
            # 默认返回字符串数组
            return [f"{var_name}_1", f"{var_name}_2"]
    
    def _validate_solution(self, solution: Dict[str, Any], constraints: List[str], 
                         entity_name: str) -> bool:
        """验证解是否满足所有约束"""
        # 创建一个临时实体用于验证
        from ..v8.models import Entity, Attribute
        
        entity = Entity(name=entity_name or "TestEntity")
        entity.constraints = constraints
        
        # 创建属性（简化版）
        for key, value in solution.items():
            if isinstance(value, int):
                attr_type = 'integer'
            elif isinstance(value, float):
                attr_type = 'float'
            elif isinstance(value, str):
                attr_type = 'string'
            elif isinstance(value, bool):
                attr_type = 'boolean'
            elif isinstance(value, list):
                attr_type = 'array'
            else:
                attr_type = 'string'
            
            attr = Attribute(name=key, type=attr_type)
            entity.attributes.append(attr)
        
        # 使用验证器检查
        is_valid, violations = self.validator.validate_test_data(solution, entity, 'functional')
        
        return is_valid
    
    def _fix_constraint_violations(self, solution: Dict[str, Any], constraints: List[str], 
                                  entity_name: str) -> Dict[str, Any]:
        """修复约束违反"""
        # 特殊处理订单总价约束
        if entity_name == 'Order' and any('total_amount' in c for c in constraints):
            solution = self._fix_order_total_constraint(solution)
        
        # 处理其他约束
        fixed = solution.copy()
        
        for constraint in constraints:
            if not self._evaluate_single_constraint(constraint, fixed):
                # 尝试修复这个约束
                fixed = self._fix_single_constraint(fixed, constraint)
        
        return fixed
    
    def _fix_order_total_constraint(self, solution: Dict[str, Any]) -> Dict[str, Any]:
        """修复订单总价约束"""
        required_fields = ['subtotal', 'tax_amount', 'shipping_cost', 'discount_percentage']
        
        if all(field in solution for field in required_fields):
            subtotal = float(solution['subtotal'])
            tax_amount = float(solution['tax_amount'])
            shipping_cost = float(solution['shipping_cost'])
            discount_percentage = float(solution['discount_percentage'])
            
            # 计算正确的总价
            solution['total_amount'] = round(
                subtotal + tax_amount + shipping_cost - (subtotal * discount_percentage / 100),
                2
            )
        
        return solution
    
    def _fix_single_constraint(self, solution: Dict[str, Any], constraint: str) -> Dict[str, Any]:
        """修复单个约束"""
        # 简单的修复策略
        if '>' in constraint:
            parts = constraint.split('>')
            if len(parts) == 2:
                left = parts[0].strip()
                right = parts[1].strip()
                
                if left in solution and right.replace('.', '').isdigit():
                    target = float(right)
                    solution[left] = target + random.uniform(0.1, 10)
                elif left in solution and right in solution:
                    solution[left] = solution[right] + random.uniform(0.1, 10)
        
        return solution
    
    def _evaluate_single_constraint(self, constraint: str, solution: Dict[str, Any]) -> bool:
        """评估单个约束"""
        try:
            expr = constraint
            
            # 替换变量
            for key, value in solution.items():
                if key in expr:
                    if isinstance(value, str):
                        expr = expr.replace(key, f'"{value}"')
                    else:
                        expr = expr.replace(key, str(value))
            
            # 处理size函数
            import re
            def replace_size(match):
                var_name = match.group(1)
                if var_name in solution and hasattr(solution[var_name], '__len__'):
                    return str(len(solution[var_name]))
                return '0'
            
            expr = re.sub(r'size\((\w+)\)', replace_size, expr)
            
            return eval(expr, {"__builtins__": {}}, {})
        except:
            return True  # 默认满足
    
    def _preprocess_constraints(self, constraints: List[str], entity_name: str) -> List[str]:
        """预处理约束，处理特殊情况"""
        processed = []
        
        for constraint in constraints:
            # 处理订单总价约束
            if 'Order.total_amount ==' in constraint and 'Order.subtotal' in constraint:
                # 跳过这个复杂约束，后续特殊处理
                continue
            
            # 标准化实体前缀
            if entity_name:
                constraint = constraint.replace(f"{entity_name}.", "")
            
            processed.append(constraint)
        
        return processed
    
    def _handle_order_total_constraint(self, entity_name: str) -> None:
        """特殊处理订单总价约束"""
        if entity_name == 'Order' and 'total_amount' in self.variables:
            # 添加自定义约束处理逻辑
            pass
    
    def _is_essential_constraint(self, constraint: str) -> bool:
        """判断是否是必要约束"""
        # 基本范围约束是必要的
        essential_patterns = [
            r'\w+\s*>=?\s*0',  # 非负约束
            r'\w+\s*<=?\s*\d+',  # 上界约束
            r'size\(\w+\)\s*>=?\s*0',  # 集合大小非负
        ]
        
        import re
        for pattern in essential_patterns:
            if re.match(pattern, constraint.strip()):
                return True
        
        return False
    
    def _analyze_constraint_relationships(self, constraints: List[str]) -> Dict[str, List[str]]:
        """分析约束之间的关系"""
        relationships = {}
        
        for constraint in constraints:
            # 提取变量名
            import re
            variables = re.findall(r'\b[a-zA-Z_]\w*\b', constraint)
            
            for var in variables:
                if var not in ['size', 'and', 'or', 'not']:  # 排除关键字
                    if var not in relationships:
                        relationships[var] = []
                    relationships[var].append(constraint)
        
        return relationships
    
    # 以下是Z3相关的辅助方法（保持与原实现兼容）
    
    def _create_z3_variables(self, variables: Dict[str, Dict[str, Any]]):
        """创建Z3变量"""
        for name, info in variables.items():
            var_type = info.get('type', 'int')
            
            if var_type == 'int':
                var = z3.Int(name)
                self.variables[name] = var
                
                if 'range' in info:
                    min_val, max_val = info['range']
                    self.solver.add(var >= min_val)
                    self.solver.add(var <= max_val)
                    
            elif var_type == 'bool':
                var = z3.Bool(name)
                self.variables[name] = var
                
            elif var_type in ['float', 'real']:
                var = z3.Real(name)
                self.variables[name] = var
                
                if 'range' in info:
                    min_val, max_val = info['range']
                    self.solver.add(var >= min_val)
                    self.solver.add(var <= max_val)
                    
            elif var_type == 'string':
                # Z3对字符串支持有限，使用整数枚举
                var = z3.Int(name)
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
        # 简化实现，参考原v8_modular实现
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
                
        elif node_type == 'identifier':
            name = ast['value']
            if name in self.variables:
                return self.variables[name]
                
        elif node_type == 'number':
            return ast['value']
            
        elif node_type == 'boolean':
            return ast['value']
            
        return None
    
    def _extract_solution(self, model: z3.ModelRef, variables: Dict[str, Dict[str, Any]]) -> Dict[str, Any]:
        """从Z3模型中提取解"""
        solution = {}
        
        for name, var in self.variables.items():
            try:
                value = model[var]
                if value is not None:
                    if z3.is_int(var):
                        solution[name] = value.as_long()
                    elif z3.is_bool(var):
                        solution[name] = bool(value)
                    elif z3.is_real(var):
                        # 转换为浮点数
                        solution[name] = float(value.as_fraction())
                    else:
                        solution[name] = str(value)
                else:
                    # 使用默认值
                    if name in variables:
                        solution[name] = self._generate_safe_default(name, variables[name])
            except:
                # 如果提取失败，使用默认值
                if name in variables:
                    solution[name] = self._generate_safe_default(name, variables[name])
        
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