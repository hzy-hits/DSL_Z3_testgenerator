"""
Type-Aware Value Generator
类型感知的值生成器 - 正确处理所有类型，特别是集合类型
"""

import random
import logging
from typing import Any, Dict, List, Optional, Union
from ..v8.models import Attribute, Entity
from ..v8.value_generator import ValueGenerator

logger = logging.getLogger(__name__)


class TypeAwareValueGenerator:
    """类型感知的值生成器"""
    
    def __init__(self):
        # 使用原始值生成器作为基础
        self.base_generator = ValueGenerator()
        
    def generate_value(self, entity: Entity, attr: Attribute, 
                      context: Dict[str, Any] = None) -> Any:
        """生成满足类型要求的值"""
        
        # 首先尝试使用基础生成器
        try:
            value = self.base_generator.generate(entity.name, attr, context)
            
            # 验证生成的值类型是否正确
            if self._is_type_correct(value, attr):
                return value
            else:
                logger.warning(f"Base generator returned wrong type for {attr.name}, regenerating")
                return self._generate_typed_value(entity, attr, context)
                
        except Exception as e:
            logger.warning(f"Base generator failed for {attr.name}: {e}")
            return self._generate_typed_value(entity, attr, context)
    
    def _is_type_correct(self, value: Any, attr: Attribute) -> bool:
        """检查值的类型是否正确"""
        if attr.is_collection:
            return isinstance(value, (list, set, tuple))
        elif attr.type in ['integer', 'int']:
            return isinstance(value, int) and not isinstance(value, bool)
        elif attr.type in ['float', 'real', 'double']:
            return isinstance(value, (int, float)) and not isinstance(value, bool)
        elif attr.type == 'string':
            return isinstance(value, str)
        elif attr.type in ['boolean', 'bool']:
            return isinstance(value, bool)
        else:
            return True
    
    def _generate_typed_value(self, entity: Entity, attr: Attribute, 
                            context: Dict[str, Any] = None) -> Any:
        """根据类型生成值"""
        
        # 处理集合类型
        if attr.is_collection:
            return self._generate_collection_value(entity, attr, context)
        
        # 处理基本类型
        if attr.type in ['integer', 'int']:
            return self._generate_integer_value(entity, attr, context)
        elif attr.type in ['float', 'real', 'double']:
            return self._generate_float_value(entity, attr, context)
        elif attr.type == 'string':
            return self._generate_string_value(entity, attr, context)
        elif attr.type in ['boolean', 'bool']:
            return random.choice([True, False])
        else:
            # 默认返回字符串
            return f"{attr.name}_value"
    
    def _generate_collection_value(self, entity: Entity, attr: Attribute, 
                                  context: Dict[str, Any] = None) -> List[Any]:
        """生成集合值"""
        # 确定集合大小
        min_size = attr.min_size if attr.min_size is not None else 1
        max_size = attr.max_size if attr.max_size is not None else 5
        
        # 确保最小大小不为0（除非明确允许空集合）
        if min_size == 0 and 'categories' in attr.name.lower():
            min_size = 1  # categories通常需要至少一个元素
        
        size = random.randint(min_size, max_size)
        
        # 根据属性名生成合适的集合
        attr_lower = attr.name.lower()
        
        if 'categories' in attr_lower:
            # 产品类别
            all_categories = ['electronics', 'clothing', 'books', 'home', 'sports', 
                            'toys', 'food', 'beauty', 'automotive', 'health']
            size = min(size, len(all_categories))
            return random.sample(all_categories, size)
            
        elif 'items' in attr_lower:
            # 购物车商品ID
            return [random.randint(1001, 1020) for _ in range(size)]
            
        elif 'discount_codes' in attr_lower:
            # 折扣码
            all_codes = ['SAVE10', 'WELCOME20', 'VIP15', 'SUMMER25', 'BULK15', 
                        'FLASH50', 'NEWUSER', 'LOYALTY30']
            size = min(size, len(all_codes))
            return random.sample(all_codes, size)
            
        elif 'permissions' in attr_lower:
            # 权限列表
            all_perms = ['read', 'write', 'delete', 'admin', 'execute', 'modify']
            size = min(size, len(all_perms))
            return random.sample(all_perms, size)
            
        elif 'roles' in attr_lower:
            # 角色列表
            all_roles = ['user', 'admin', 'moderator', 'guest', 'developer']
            size = min(size, len(all_roles))
            return random.sample(all_roles, size)
            
        else:
            # 默认生成字符串数组
            return [f"{attr.name}_{i+1}" for i in range(size)]
    
    def _generate_integer_value(self, entity: Entity, attr: Attribute, 
                              context: Dict[str, Any] = None) -> int:
        """生成整数值"""
        attr_lower = attr.name.lower()
        
        # ID类型特殊处理
        if 'id' in attr_lower:
            # 确保ID大于0
            if 'product' in entity.name.lower():
                return random.randint(1001, 2000)
            elif 'order' in entity.name.lower():
                return random.randint(10001, 20000)
            elif 'user' in entity.name.lower() or 'customer' in entity.name.lower():
                return random.randint(1, 1000)
            else:
                return random.randint(1, 9999)
        
        # 年龄
        elif 'age' in attr_lower:
            return random.randint(18, 80)
        
        # 数量
        elif 'quantity' in attr_lower or 'count' in attr_lower:
            return random.randint(1, 100)
        
        # 百分比
        elif 'percentage' in attr_lower or 'percent' in attr_lower:
            return random.randint(0, 100)
        
        # 价格（整数形式）
        elif 'price' in attr_lower or 'cost' in attr_lower or 'amount' in attr_lower:
            return random.randint(10, 1000)
        
        # 默认
        else:
            return random.randint(1, 100)
    
    def _generate_float_value(self, entity: Entity, attr: Attribute, 
                            context: Dict[str, Any] = None) -> float:
        """生成浮点数值"""
        attr_lower = attr.name.lower()
        
        # 价格相关
        if 'price' in attr_lower or 'cost' in attr_lower or 'amount' in attr_lower:
            return round(random.uniform(0.99, 999.99), 2)
        
        # 税率
        elif 'tax' in attr_lower:
            return round(random.uniform(0.0, 0.25), 2)
        
        # 评分
        elif 'rating' in attr_lower or 'score' in attr_lower:
            return round(random.uniform(1.0, 5.0), 1)
        
        # 默认
        else:
            return round(random.uniform(0.0, 100.0), 2)
    
    def _generate_string_value(self, entity: Entity, attr: Attribute, 
                             context: Dict[str, Any] = None) -> str:
        """生成字符串值"""
        attr_lower = attr.name.lower()
        
        # 邮箱
        if 'email' in attr_lower:
            domains = ['example.com', 'test.com', 'demo.org', 'sample.net']
            return f"user{random.randint(1, 100)}@{random.choice(domains)}"
        
        # 名称
        elif 'name' in attr_lower:
            if 'user' in attr_lower or 'customer' in attr_lower:
                first_names = ['John', 'Jane', 'Bob', 'Alice', 'Charlie', 'Emma']
                last_names = ['Smith', 'Johnson', 'Williams', 'Brown', 'Jones']
                return f"{random.choice(first_names)} {random.choice(last_names)}"
            else:
                return f"{attr.name}_{random.randint(1, 100)}"
        
        # 地址
        elif 'address' in attr_lower:
            streets = ['Main St', 'Oak Ave', 'Park Blvd', 'First St', 'Elm St']
            return f"{random.randint(1, 999)} {random.choice(streets)}, City, State {random.randint(10000, 99999)}"
        
        # 状态
        elif 'status' in attr_lower:
            return random.choice(['active', 'inactive', 'pending'])
        
        # SKU
        elif 'sku' in attr_lower:
            letters = ''.join(random.choices('ABCDEFGHIJKLMNOPQRSTUVWXYZ', k=3))
            numbers = ''.join(random.choices('0123456789', k=6))
            return f"{letters}-{numbers}"
        
        # 默认
        else:
            return f"{attr.name}_value_{random.randint(1, 100)}"
    
    def generate_for_constraints(self, entity: Entity, attr: Attribute, 
                               constraints: List[str]) -> Any:
        """生成满足约束的值"""
        # 先尝试普通生成
        value = self.generate_value(entity, attr)
        
        # TODO: 检查约束并调整值
        # 这里可以集成约束检查逻辑
        
        return value
    
    def generate_boundary_value(self, entity: Entity, attr: Attribute, 
                              boundary_type: str = 'min') -> Any:
        """生成边界值"""
        if attr.is_collection:
            # 集合边界
            if boundary_type == 'min':
                size = attr.min_size if attr.min_size is not None else 0
            else:
                size = attr.max_size if attr.max_size is not None else 10
            
            # 生成指定大小的集合
            if size == 0:
                return []
            else:
                # 使用普通生成但指定大小
                temp_attr = Attribute(
                    name=attr.name,
                    type=attr.type,
                    is_collection=True,
                    min_size=size,
                    max_size=size
                )
                return self._generate_collection_value(entity, temp_attr)
        
        elif attr.type in ['integer', 'int']:
            # 整数边界
            if boundary_type == 'min':
                # 对于ID等字段，最小值是1
                if 'id' in attr.name.lower():
                    return 1
                else:
                    return 0
            else:
                return 999999
        
        elif attr.type in ['float', 'real', 'double']:
            # 浮点数边界
            if boundary_type == 'min':
                # 价格等通常最小值是0.01
                if 'price' in attr.name.lower():
                    return 0.01
                else:
                    return 0.0
            else:
                return 999999.99
        
        else:
            # 其他类型使用普通生成
            return self.generate_value(entity, attr)