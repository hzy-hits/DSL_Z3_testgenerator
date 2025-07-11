"""
Improved Negative Test Strategy
改进的负面测试策略 - 生成违反约束的值而非错误类型
"""

import random
import logging
from typing import List, Dict, Any, Optional
from ..v8.models import Entity, Test, Attribute
from ..v8.value_generator import ValueGenerator
from ..v8.constraint_handler import ConstraintHandler

logger = logging.getLogger(__name__)


class ImprovedNegativeTestStrategy:
    """改进的负面测试策略"""
    
    def __init__(self, value_generator: ValueGenerator, constraint_handler: ConstraintHandler):
        self.value_generator = value_generator
        self.constraint_handler = constraint_handler
    
    def generate(self, entity: Entity, count: int = 2) -> List[Test]:
        """生成负面测试用例"""
        tests = []
        
        # 1. 为每个属性生成违反约束的测试
        for attr in entity.attributes[:count]:
            test = self._generate_constraint_violation_test(entity, attr)
            if test:
                tests.append(test)
        
        # 2. 生成违反全局约束的测试
        if entity.constraints:
            for constraint in entity.constraints[:max(1, count - len(tests))]:
                test = self._generate_global_constraint_violation(entity, constraint)
                if test:
                    tests.append(test)
        
        return tests[:count]
    
    def _generate_constraint_violation_test(self, entity: Entity, attribute: Attribute) -> Optional[Test]:
        """为特定属性生成违反约束的测试"""
        test_data = {}
        
        # 先生成其他属性的有效值
        for attr in entity.attributes:
            if attr.name != attribute.name:
                test_data[attr.name] = self.value_generator.generate(entity.name, attr)
        
        # 为目标属性生成违反约束的值
        violation_value = self._generate_violation_value(attribute)
        if violation_value is not None:
            test_data[attribute.name] = violation_value
            
            return Test(
                test_name=f"{entity.name}_{attribute.name}_constraint_violation",
                test_type="negative",
                description=f"Test constraint violation for {attribute.name}",
                test_data=test_data,
                expected_result="fail",
                constraint=f"Violates {attribute.name} constraints",
                expected_error=f"Constraint violation on {attribute.name}",
                priority=7
            )
        
        return None
    
    def _generate_violation_value(self, attribute: Attribute) -> Any:
        """生成违反属性约束的值（类型正确）"""
        if attribute.type == "integer":
            # 对于整数类型，生成超出范围的值
            # Generate negative value to test boundary
            return -random.randint(1, 100)
        
        elif attribute.type == "real" or attribute.type == "float":
            # 对于浮点数类型
            # Generate negative value to test boundary
            return -random.uniform(0.01, 100.0)
        
        elif attribute.type == "string":
            # 对于字符串类型
            # Note: pattern and format are not part of v8 models
            if attribute.enum:
                # 返回不在枚举中的值
                return "NOT_IN_ENUM_" + str(random.randint(1, 100))
            else:
                # 返回空字符串（如果不允许）
                return ""
        
        elif attribute.type.startswith("array"):
            # 对于数组类型
            if attribute.min_size is not None and attribute.min_size > 0:
                # 返回空数组（违反最小大小约束）
                return []
            elif attribute.max_size is not None:
                # 返回超过最大大小的数组
                return list(range(attribute.max_size + 5))
            else:
                return []
        
        elif attribute.type.startswith("set"):
            # 对于集合类型
            if attribute.min_size is not None and attribute.min_size > 0:
                return set()  # 空集合
            elif attribute.max_size is not None:
                # 超过最大大小的集合
                return set(range(attribute.max_size + 5))
            else:
                return set()
        
        elif attribute.type == "boolean":
            # 布尔类型没有"违反"的值，返回None表示跳过
            return None
        
        else:
            # 默认返回None
            return None
    
    def _generate_global_constraint_violation(self, entity: Entity, constraint: str) -> Optional[Test]:
        """生成违反全局约束的测试"""
        test_data = {}
        
        # 先生成基本有效值
        for attr in entity.attributes:
            test_data[attr.name] = self.value_generator.generate(entity.name, attr)
        
        # 尝试修改值以违反约束
        modified_data = self._modify_to_violate_constraint(test_data, constraint, entity)
        
        if modified_data and not self.constraint_handler.evaluate(constraint, modified_data):
            return Test(
                test_name=f"{entity.name}_violate_{self._constraint_to_name(constraint)}",
                test_type="negative",
                description=f"Test violation of constraint: {constraint}",
                test_data=modified_data,
                expected_result="fail",
                constraint=constraint,
                expected_error=f"Constraint violation: {constraint}",
                priority=7
            )
        
        return None
    
    def _modify_to_violate_constraint(self, data: Dict[str, Any], constraint: str, entity: Entity) -> Dict[str, Any]:
        """修改数据以违反特定约束"""
        # 复制数据以避免修改原始数据
        modified = data.copy()
        
        # 解析约束并尝试违反它
        if '>' in constraint and '=' not in constraint:
            # 处理 x > y 形式的约束
            parts = constraint.split('>')
            if len(parts) == 2:
                left = parts[0].strip()
                right = parts[1].strip()
                
                # 尝试让 left <= right
                if left in modified and right.replace('.', '').replace('_', '').isdigit():
                    try:
                        target = float(right)
                        modified[left] = target - random.uniform(0.1, 10)
                    except:
                        pass
                elif left in modified and right in modified:
                    # 字段间比较
                    if isinstance(modified[right], (int, float)):
                        modified[left] = modified[right] - random.uniform(0.1, 10)
        
        elif '>=' in constraint:
            # 处理 x >= y 形式的约束
            parts = constraint.split('>=')
            if len(parts) == 2:
                left = parts[0].strip()
                right = parts[1].strip()
                
                # 尝试让 left < right
                if left in modified and right.replace('.', '').replace('_', '').isdigit():
                    try:
                        target = float(right)
                        modified[left] = target - random.uniform(0.1, 10)
                    except:
                        pass
        
        elif '<' in constraint and '=' not in constraint:
            # 处理 x < y 形式的约束
            parts = constraint.split('<')
            if len(parts) == 2:
                left = parts[0].strip()
                right = parts[1].strip()
                
                # 尝试让 left >= right
                if left in modified and right.replace('.', '').replace('_', '').isdigit():
                    try:
                        target = float(right)
                        modified[left] = target + random.uniform(0.1, 10)
                    except:
                        pass
        
        elif '<=' in constraint:
            # 处理 x <= y 形式的约束
            parts = constraint.split('<=')
            if len(parts) == 2:
                left = parts[0].strip()
                right = parts[1].strip()
                
                # 尝试让 left > right
                if left in modified and right.replace('.', '').replace('_', '').isdigit():
                    try:
                        target = float(right)
                        modified[left] = target + random.uniform(0.1, 10)
                    except:
                        pass
        
        elif '==' in constraint:
            # 处理相等约束
            parts = constraint.split('==')
            if len(parts) == 2:
                left = parts[0].strip()
                right = parts[1].strip()
                
                if left in modified:
                    # 修改为不等的值
                    if isinstance(modified[left], (int, float)):
                        modified[left] = modified[left] + random.uniform(1, 10)
                    elif isinstance(modified[left], str):
                        modified[left] = modified[left] + "_modified"
                    elif isinstance(modified[left], bool):
                        modified[left] = not modified[left]
        
        return modified
    
    def _constraint_to_name(self, constraint: str) -> str:
        """将约束转换为合法的测试名称"""
        # 移除特殊字符
        name = constraint.replace(' ', '_').replace('>', 'gt').replace('<', 'lt')
        name = name.replace('=', 'eq').replace('(', '').replace(')', '')
        name = name.replace('.', '_').replace('+', 'plus').replace('-', 'minus')
        name = name.replace('*', 'mult').replace('/', 'div')
        
        # 限制长度
        if len(name) > 50:
            name = name[:50]
        
        return name