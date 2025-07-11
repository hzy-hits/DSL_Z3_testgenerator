"""
Improved Boundary Test Strategy
改进的边界值测试策略 - 确保边界值满足其他约束
"""

import logging
from typing import List, Dict, Any, Optional
from ..v8.models import Entity, Test, Attribute
from ..v8.value_generator import ValueGenerator
from ..v8.constraint_handler import ConstraintHandler
from .constraint_validator import ConstraintValidator

logger = logging.getLogger(__name__)


class ImprovedBoundaryTestStrategy:
    """改进的边界值测试策略"""
    
    def __init__(self, value_generator: ValueGenerator, constraint_handler: ConstraintHandler):
        self.value_generator = value_generator
        self.constraint_handler = constraint_handler
        self.validator = ConstraintValidator()
    
    def generate(self, entity: Entity, count: int = 5) -> List[Test]:
        """生成边界值测试用例"""
        tests = []
        
        # 为每个有边界的属性生成测试
        boundary_attributes = [attr for attr in entity.attributes 
                             if self._has_boundaries(attr)]
        
        for attr in boundary_attributes[:count]:
            # 生成最小值边界测试
            min_test = self._generate_min_boundary_test(entity, attr)
            if min_test:
                tests.append(min_test)
            
            # 生成最大值边界测试
            max_test = self._generate_max_boundary_test(entity, attr)
            if max_test:
                tests.append(max_test)
            
            # 生成边界附近的测试
            near_boundary_test = self._generate_near_boundary_test(entity, attr)
            if near_boundary_test:
                tests.append(near_boundary_test)
        
        # 生成集合边界测试
        collection_attributes = [attr for attr in entity.attributes 
                               if attr.type.startswith(('array', 'set'))]
        
        for attr in collection_attributes[:max(1, count - len(tests))]:
            # 空集合测试
            empty_test = self._generate_empty_collection_test(entity, attr)
            if empty_test:
                tests.append(empty_test)
            
            # 最大集合测试
            max_collection_test = self._generate_max_collection_test(entity, attr)
            if max_collection_test:
                tests.append(max_collection_test)
        
        return tests[:count]
    
    def _has_boundaries(self, attr: Attribute) -> bool:
        """检查属性是否有边界"""
        return (attr.type in ['integer', 'real', 'float'] or
                attr.is_collection or
                attr.min_size is not None or attr.max_size is not None)
    
    def _generate_min_boundary_test(self, entity: Entity, attribute: Attribute) -> Optional[Test]:
        """生成最小值边界测试"""
        # Generate minimum boundary test based on type
        if attribute.type not in ['integer', 'real', 'float']:
            return None
        
        test_data = self._generate_base_test_data(entity, exclude_attr=attribute.name)
        
        # Set minimum boundary value based on type and constraints
        if attribute.type == 'integer':
            # Special handling for ID fields - minimum should be 1
            if 'id' in attribute.name.lower():
                test_data[attribute.name] = 1
            else:
                test_data[attribute.name] = 0
        elif attribute.type in ['real', 'float']:
            # Special handling for price fields - minimum should be 0.01
            if 'price' in attribute.name.lower():
                test_data[attribute.name] = 0.01
            else:
                test_data[attribute.name] = 0.0
        
        # 验证并修复约束违反
        test_data = self._ensure_constraints_satisfied(test_data, entity)
        
        return Test(
            test_name=f"{entity.name}_{attribute.name}_min_boundary",
            test_type="boundary",
            description=f"Test minimum boundary for {attribute.name}",
            test_data=test_data,
            expected_result="pass",
            priority=9
        )
    
    def _generate_max_boundary_test(self, entity: Entity, attribute: Attribute) -> Optional[Test]:
        """生成最大值边界测试"""
        # Generate maximum boundary test based on type
        if attribute.type not in ['integer', 'real', 'float']:
            return None
        
        test_data = self._generate_base_test_data(entity, exclude_attr=attribute.name)
        
        # Set maximum boundary value based on type
        if attribute.type == 'integer':
            test_data[attribute.name] = 999999
        elif attribute.type in ['real', 'float']:
            test_data[attribute.name] = 999999.99
        
        # 验证并修复约束违反
        test_data = self._ensure_constraints_satisfied(test_data, entity)
        
        return Test(
            test_name=f"{entity.name}_{attribute.name}_max_boundary",
            test_type="boundary",
            description=f"Test maximum boundary for {attribute.name}",
            test_data=test_data,
            expected_result="pass",
            priority=9
        )
    
    def _generate_near_boundary_test(self, entity: Entity, attribute: Attribute) -> Optional[Test]:
        """生成边界附近的测试"""
        test_data = self._generate_base_test_data(entity, exclude_attr=attribute.name)
        
        # 选择一个接近边界但满足约束的值
        # Generate near-boundary value based on type
        if attribute.type == 'integer':
            near_value = 1  # Near minimum boundary
        elif attribute.type in ['real', 'float']:
            near_value = 0.01  # Near minimum boundary
        else:
            return None
        
        test_data[attribute.name] = near_value
        
        # 验证并修复约束违反
        test_data = self._ensure_constraints_satisfied(test_data, entity)
        
        return Test(
            test_name=f"{entity.name}_{attribute.name}_near_boundary",
            test_type="boundary",
            description=f"Test near boundary value for {attribute.name}",
            test_data=test_data,
            expected_result="pass",
            priority=8
        )
    
    def _generate_empty_collection_test(self, entity: Entity, attribute: Attribute) -> Optional[Test]:
        """生成空集合测试"""
        # 检查是否允许空集合
        if attribute.min_size is not None and attribute.min_size > 0:
            return None  # 不允许空集合，跳过此测试
        
        test_data = self._generate_base_test_data(entity, exclude_attr=attribute.name)
        
        # 设置空集合
        if attribute.type.startswith('array'):
            test_data[attribute.name] = []
        elif attribute.type.startswith('set'):
            test_data[attribute.name] = set()
        
        # 验证并修复约束违反
        test_data = self._ensure_constraints_satisfied(test_data, entity)
        
        return Test(
            test_name=f"{entity.name}_{attribute.name}_empty_collection",
            test_type="boundary",
            description=f"Test empty collection for {attribute.name}",
            test_data=test_data,
            expected_result="pass",
            priority=8
        )
    
    def _generate_max_collection_test(self, entity: Entity, attribute: Attribute) -> Optional[Test]:
        """生成最大集合测试"""
        if attribute.max_size is None:
            return None
        
        test_data = self._generate_base_test_data(entity, exclude_attr=attribute.name)
        
        # 生成最大大小的集合
        if attribute.type.startswith('array'):
            # 根据元素类型生成数组
            element_type = attribute.type.replace('array[', '').replace(']', '')
            test_data[attribute.name] = self._generate_array_elements(element_type, attribute.max_size)
        elif attribute.type.startswith('set'):
            # 根据元素类型生成集合
            element_type = attribute.type.replace('set[', '').replace(']', '')
            test_data[attribute.name] = list(set(self._generate_array_elements(element_type, attribute.max_size)))
        
        # 验证并修复约束违反
        test_data = self._ensure_constraints_satisfied(test_data, entity)
        
        return Test(
            test_name=f"{entity.name}_{attribute.name}_max_collection",
            test_type="boundary",
            description=f"Test maximum collection size for {attribute.name}",
            test_data=test_data,
            expected_result="pass",
            priority=8
        )
    
    def _generate_base_test_data(self, entity: Entity, exclude_attr: Optional[str] = None) -> Dict[str, Any]:
        """生成基础测试数据（排除指定属性）"""
        test_data = {}
        
        for attr in entity.attributes:
            if attr.name != exclude_attr:
                # 生成满足约束的中间值
                test_data[attr.name] = self._generate_safe_value(entity.name, attr)
        
        return test_data
    
    def _generate_safe_value(self, entity_name: str, attr: Attribute) -> Any:
        """生成安全的中间值（避免边界）"""
        if attr.type == "integer":
            min_val = 1
            max_val = 100
            # 选择中间值
            return (min_val + max_val) // 2
        
        elif attr.type in ["real", "float"]:
            min_val = 0.0
            max_val = 100.0
            # 选择中间值
            return round((min_val + max_val) / 2, 2)
        
        elif attr.type == "string":
            # 检查是否实际上是集合类型
            if attr.is_collection:
                # 这应该是一个集合，调用集合生成
                return self._generate_collection_safe_value(attr, entity_name)
            elif attr.enum:
                return attr.enum[0]
            # Note: format and pattern are not part of v8 models
            # elif attr.format == "email":
            #     return "test@example.com"
            # elif attr.pattern:
            #     return self._generate_pattern_match(attr.pattern)
            else:
                return f"{attr.name}_value"
        
        elif attr.type.startswith("array"):
            min_size = attr.min_size if attr.min_size is not None else 1
            max_size = attr.max_size if attr.max_size is not None else 5
            # 选择中间大小
            size = (min_size + max_size) // 2
            element_type = attr.type.replace('array[', '').replace(']', '')
            return self._generate_array_elements(element_type, size)
        
        elif attr.type.startswith("set"):
            min_size = attr.min_size if attr.min_size is not None else 1
            max_size = attr.max_size if attr.max_size is not None else 5
            # 选择中间大小
            size = (min_size + max_size) // 2
            element_type = attr.type.replace('set[', '').replace(']', '')
            return list(set(self._generate_array_elements(element_type, size)))
        
        elif attr.type == "boolean":
            return True
        
        else:
            # 检查是否是集合类型
            if attr.is_collection:
                return self._generate_collection_safe_value(attr, entity_name)
            else:
                # 使用默认值生成器
                return self.value_generator.generate(entity_name, attr)
    
    def _generate_collection_safe_value(self, attr: Attribute, entity_name: str) -> List[Any]:
        """生成安全的集合值"""
        # 确定安全的中间大小
        min_size = attr.min_size if attr.min_size is not None else 1
        max_size = attr.max_size if attr.max_size is not None else 5
        safe_size = (min_size + max_size) // 2
        
        # 确保至少有一个元素（对于某些约束）
        if 'categories' in attr.name.lower() and safe_size == 0:
            safe_size = 1
        
        # 根据属性名生成合适的集合
        attr_lower = attr.name.lower()
        
        if 'categories' in attr_lower:
            all_categories = ['electronics', 'clothing', 'books', 'home', 'sports']
            return all_categories[:safe_size]
        elif 'items' in attr_lower:
            return [1000 + i for i in range(safe_size)]
        elif 'discount_codes' in attr_lower:
            codes = ['SAVE10', 'WELCOME20', 'VIP15']
            return codes[:safe_size]
        else:
            return [f"{attr.name}_{i+1}" for i in range(safe_size)]
    
    def _generate_array_elements(self, element_type: str, size: int) -> List[Any]:
        """生成数组元素"""
        elements = []
        
        for i in range(size):
            if element_type == "integer":
                elements.append(1000 + i)
            elif element_type == "string":
                elements.append(f"item_{i+1}")
            elif element_type in ["real", "float"]:
                elements.append(round(10.0 + i * 0.5, 2))
            else:
                elements.append(f"element_{i+1}")
        
        return elements
    
    def _generate_pattern_match(self, pattern: str) -> str:
        """生成匹配模式的字符串"""
        # 简单实现
        if pattern == r"^[A-Z]{3}-[0-9]{6}$":
            return "ABC-123456"
        elif pattern == r"^ORD-[0-9]{10}$":
            return "ORD-1234567890"
        else:
            return "PATTERN_VALUE"
    
    def _ensure_constraints_satisfied(self, test_data: Dict[str, Any], entity: Entity) -> Dict[str, Any]:
        """确保测试数据满足所有约束"""
        # 验证约束
        is_valid, violations = self.validator.validate_test_data(test_data, entity, 'boundary')
        
        if not is_valid and violations:
            # 尝试修复约束违反
            test_data = self.validator.fix_constraint_violations(test_data, violations, entity)
            
            # 再次验证
            is_valid, violations = self.validator.validate_test_data(test_data, entity, 'boundary')
            
            if not is_valid:
                logger.warning(f"Unable to fix all constraint violations for {entity.name}: {violations}")
        
        return test_data