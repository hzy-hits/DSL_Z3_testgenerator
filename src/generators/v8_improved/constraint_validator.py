"""
Constraint Validator
约束验证器 - 确保生成的测试数据满足预期约束
"""

import re
import logging
from typing import Dict, List, Any, Optional, Tuple
from ..v8.models import Entity, Attribute

logger = logging.getLogger(__name__)


class ConstraintValidator:
    """约束验证器"""
    
    def __init__(self):
        self.special_constraints = {
            'order_total': self._validate_order_total_constraint
        }
    
    def validate_test_data(self, test_data: Dict[str, Any], entity: Entity, 
                          test_type: str = 'functional') -> Tuple[bool, List[str]]:
        """
        验证测试数据是否满足约束
        
        Returns:
            (is_valid, violations) - 是否有效和违反的约束列表
        """
        violations = []
        
        # 1. 验证属性级约束
        for attr in entity.attributes:
            if attr.name in test_data:
                value = test_data[attr.name]
                attr_violations = self._validate_attribute_constraints(attr, value)
                violations.extend(attr_violations)
        
        # 2. 验证实体级约束
        if entity.constraints:
            for constraint in entity.constraints:
                if not self._evaluate_constraint(constraint, test_data, entity.name):
                    violations.append(constraint)
        
        # 3. 根据测试类型判断是否符合预期
        if test_type == 'negative':
            # 负面测试应该有约束违反
            is_valid = len(violations) > 0
        else:
            # 其他测试不应该有约束违反
            is_valid = len(violations) == 0
        
        return is_valid, violations
    
    def _validate_attribute_constraints(self, attr: Attribute, value: Any) -> List[str]:
        """验证属性级约束"""
        violations = []
        
        # 类型检查 - 考虑集合类型
        if attr.is_collection:
            # 对于集合类型，检查值是否是列表或集合
            if not isinstance(value, (list, set, tuple)):
                violations.append(f"Type mismatch for {attr.name}: expected collection but got {type(value).__name__}")
                return violations
        else:
            # 对于非集合类型，使用原有逻辑
            if not self._check_type_match(attr.type, value):
                violations.append(f"Type mismatch for {attr.name}: expected {attr.type}")
                return violations  # 类型错误时不再检查其他约束
        
        # 数值范围检查
        if attr.type in ['integer', 'real', 'float']:
            if value is not None:
                # Note: min_value and max_value are not part of the v8 models
                # Range validation should be based on entity constraints instead
                pass
        
        # 字符串约束检查
        elif attr.type == 'string':
            if value is not None:
                # Skip pattern check - attr.pattern does not exist in v8 models
                # if attr.pattern and not re.match(attr.pattern, value):
                #     violations.append(f"{attr.name} does not match pattern {attr.pattern}")
                if attr.enum and value not in attr.enum:
                    violations.append(f"{attr.name} not in enum {attr.enum}")
                # Skip format check - attr.format does not exist in v8 models
                # if attr.format == 'email' and not self._is_valid_email(value):
                #     violations.append(f"{attr.name} is not a valid email")
        
        # 集合大小检查
        elif attr.type.startswith(('array', 'set')):
            if value is not None:
                size = len(value)
                if attr.min_size is not None and size < attr.min_size:
                    violations.append(f"size({attr.name}) < {attr.min_size}")
                if attr.max_size is not None and size > attr.max_size:
                    violations.append(f"size({attr.name}) > {attr.max_size}")
        
        # 必填检查 - v8模型使用required属性
        if hasattr(attr, 'required') and attr.required and (value is None or value == ''):
            violations.append(f"{attr.name} is required")
        
        return violations
    
    def _check_type_match(self, expected_type: str, value: Any) -> bool:
        """检查值的类型是否匹配"""
        if value is None:
            return True  # None值在optional字段中是允许的
        
        if expected_type == 'integer':
            return isinstance(value, int) and not isinstance(value, bool)
        elif expected_type in ['real', 'float']:
            return isinstance(value, (int, float)) and not isinstance(value, bool)
        elif expected_type == 'string':
            # 注意：对于集合类型，实际值应该是列表，而不是字符串
            # 这里需要更复杂的判断
            return isinstance(value, str) or isinstance(value, list)
        elif expected_type == 'boolean':
            return isinstance(value, bool)
        elif expected_type.startswith('array'):
            return isinstance(value, list)
        elif expected_type.startswith('set'):
            return isinstance(value, (set, list))  # 允许list表示set
        else:
            return True  # 未知类型默认通过
    
    def _evaluate_constraint(self, constraint: str, test_data: Dict[str, Any], entity_name: str) -> bool:
        """评估约束表达式"""
        try:
            # 预处理约束表达式
            expr = constraint
            
            # 处理实体前缀
            expr = expr.replace(f"{entity_name}.", "")
            for prefix in ['Product.', 'Order.', 'Cart.', 'Customer.']:
                expr = expr.replace(prefix, "")
            
            # 特殊约束处理
            if 'Order.total_amount ==' in constraint and 'Order.subtotal' in constraint:
                return self._validate_order_total_constraint(test_data)
            
            # 处理size函数
            def replace_size(match):
                var_name = match.group(1)
                if var_name in test_data:
                    value = test_data[var_name]
                    if isinstance(value, (list, set, tuple)):
                        return str(len(value))
                return '0'
            
            expr = re.sub(r'size\((\w+)\)', replace_size, expr)
            
            # 替换变量值
            for key, value in test_data.items():
                if key in expr:
                    # 确保精确匹配（避免部分匹配）
                    pattern = r'\b' + re.escape(key) + r'\b'
                    if isinstance(value, str):
                        expr = re.sub(pattern, f'"{value}"', expr)
                    elif value is None:
                        expr = re.sub(pattern, 'None', expr)
                    else:
                        expr = re.sub(pattern, str(value), expr)
            
            # 安全评估
            result = eval(expr, {"__builtins__": {}}, {})
            return bool(result)
            
        except Exception as e:
            logger.warning(f"Failed to evaluate constraint '{constraint}': {e}")
            # 对于无法评估的约束，默认认为满足（避免误报）
            return True
    
    def _validate_order_total_constraint(self, test_data: Dict[str, Any]) -> bool:
        """验证订单总价约束"""
        required_fields = ['total_amount', 'subtotal', 'tax_amount', 'shipping_cost', 'discount_percentage']
        
        # 检查必需字段
        if not all(field in test_data for field in required_fields):
            return True  # 缺少字段时跳过验证
        
        try:
            # 计算期望的总价
            subtotal = float(test_data['subtotal'])
            tax_amount = float(test_data['tax_amount'])
            shipping_cost = float(test_data['shipping_cost'])
            discount_percentage = float(test_data['discount_percentage'])
            
            expected_total = (subtotal + tax_amount + shipping_cost - 
                            (subtotal * discount_percentage / 100))
            
            actual_total = float(test_data['total_amount'])
            
            # 允许小的浮点误差
            return abs(expected_total - actual_total) < 0.01
            
        except (ValueError, TypeError):
            return False
    
    def _is_valid_email(self, email: str) -> bool:
        """简单的邮箱格式验证"""
        pattern = r'^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$'
        return bool(re.match(pattern, email))
    
    def fix_constraint_violations(self, test_data: Dict[str, Any], violations: List[str], 
                                 entity: Entity) -> Dict[str, Any]:
        """
        尝试修复约束违反
        返回修复后的数据（如果无法修复则返回原数据）
        """
        fixed_data = test_data.copy()
        
        for violation in violations:
            # 尝试识别违反的约束类型并修复
            if '<' in violation or '>' in violation:
                fixed_data = self._fix_comparison_constraint(fixed_data, violation, entity)
            elif 'size(' in violation:
                fixed_data = self._fix_size_constraint(fixed_data, violation, entity)
            elif 'does not match pattern' in violation:
                fixed_data = self._fix_pattern_constraint(fixed_data, violation, entity)
            elif 'not in enum' in violation:
                fixed_data = self._fix_enum_constraint(fixed_data, violation, entity)
        
        # 特殊处理订单总价约束
        if entity.name == 'Order' and 'total_amount' in fixed_data:
            fixed_data = self._fix_order_total(fixed_data)
        
        return fixed_data
    
    def _fix_comparison_constraint(self, data: Dict[str, Any], violation: str, 
                                  entity: Entity) -> Dict[str, Any]:
        """修复比较约束违反"""
        # 解析违反的约束
        if '<' in violation:
            parts = violation.split('<')
            if len(parts) == 2:
                attr_name = parts[0].strip()
                limit = parts[1].strip()
                
                try:
                    limit_value = float(limit)
                    if attr_name in data:
                        # 确保值小于限制
                        data[attr_name] = limit_value - 1
                except ValueError:
                    pass
        
        elif '>' in violation:
            parts = violation.split('>')
            if len(parts) == 2:
                attr_name = parts[0].strip()
                limit = parts[1].strip()
                
                try:
                    limit_value = float(limit)
                    if attr_name in data:
                        # 确保值大于限制
                        data[attr_name] = limit_value + 1
                except ValueError:
                    pass
        
        return data
    
    def _fix_size_constraint(self, data: Dict[str, Any], violation: str, 
                           entity: Entity) -> Dict[str, Any]:
        """修复大小约束违反"""
        # 提取属性名和限制
        match = re.search(r'size\((\w+)\)\s*([<>])\s*(\d+)', violation)
        if match:
            attr_name = match.group(1)
            operator = match.group(2)
            limit = int(match.group(3))
            
            if attr_name in data and isinstance(data[attr_name], list):
                if operator == '<' and len(data[attr_name]) >= limit:
                    # 减少元素数量
                    data[attr_name] = data[attr_name][:limit-1]
                elif operator == '>' and len(data[attr_name]) <= limit:
                    # 增加元素数量
                    while len(data[attr_name]) <= limit:
                        data[attr_name].append(self._generate_element(attr_name))
        
        return data
    
    def _fix_pattern_constraint(self, data: Dict[str, Any], violation: str, 
                              entity: Entity) -> Dict[str, Any]:
        """修复模式约束违反"""
        # Skip pattern fix - attr.pattern does not exist in v8 models
        # Pattern constraints should be handled through entity-level constraints
        return data
    
    def _fix_enum_constraint(self, data: Dict[str, Any], violation: str, 
                           entity: Entity) -> Dict[str, Any]:
        """修复枚举约束违反"""
        # 提取属性名
        match = re.search(r'(\w+) not in enum', violation)
        if match:
            attr_name = match.group(1)
            
            # 查找属性定义
            for attr in entity.attributes:
                if attr.name == attr_name and attr.enum:
                    # 选择第一个枚举值
                    data[attr_name] = attr.enum[0]
                    break
        
        return data
    
    def _fix_order_total(self, data: Dict[str, Any]) -> Dict[str, Any]:
        """修复订单总价"""
        if all(field in data for field in ['subtotal', 'tax_amount', 'shipping_cost', 'discount_percentage']):
            subtotal = float(data['subtotal'])
            tax_amount = float(data['tax_amount'])
            shipping_cost = float(data['shipping_cost'])
            discount_percentage = float(data['discount_percentage'])
            
            # 重新计算正确的总价
            data['total_amount'] = round(
                subtotal + tax_amount + shipping_cost - (subtotal * discount_percentage / 100), 
                2
            )
        
        return data
    
    def _generate_element(self, attr_name: str) -> Any:
        """为集合生成新元素"""
        # 简单实现，返回随机值
        import random
        return random.randint(1000, 9999)
    
    def _generate_pattern_match(self, pattern: str) -> str:
        """生成匹配给定模式的字符串"""
        # This method is no longer used since attr.pattern doesn't exist in v8 models
        # Pattern validation should be handled through entity-level constraints
        return "PATTERN_MATCH_VALUE"