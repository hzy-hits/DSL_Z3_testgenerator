"""
Semantic Value Generator Module
语义感知的值生成器 - 根据属性名称语义自动生成合理的值
"""

import re
import random
from typing import Any, Dict, List, Optional
from .value_generator import ValueGenerator
from .models import Attribute


class SemanticValueGenerator(ValueGenerator):
    """语义感知的值生成器"""
    
    def __init__(self):
        super().__init__()
        # 定义语义模式和对应的生成策略
        self.semantic_patterns = {
            # 距离相关
            'distance': self._generate_distance_value,
            'radius': self._generate_distance_value,
            'range': self._generate_distance_value,
            
            # 时间相关
            'time': self._generate_time_value,
            'duration': self._generate_duration_value,
            'hours': self._generate_hours_value,
            'minutes': self._generate_minutes_value,
            'seconds': self._generate_seconds_value,
            'days': self._generate_days_value,
            
            # 计数相关
            'count': self._generate_count_value,
            'number': self._generate_count_value,
            'quantity': self._generate_count_value,
            'amount': self._generate_amount_value,
            
            # 状态相关
            'status': self._generate_status_value,
            'state': self._generate_status_value,
            'type': self._generate_type_value,
            'category': self._generate_type_value,
            'level': self._generate_level_value,
            'grade': self._generate_level_value,
            
            # 标识相关
            'id': self._generate_id_value,
            'code': self._generate_code_value,
            'key': self._generate_key_value,
            
            # 百分比相关
            'rate': self._generate_rate_value,
            'ratio': self._generate_rate_value,
            'percentage': self._generate_percentage_value,
            'percent': self._generate_percentage_value,
            
            # 金额相关
            'price': self._generate_price_value,
            'cost': self._generate_price_value,
            'fee': self._generate_price_value,
            'balance': self._generate_balance_value,
            
            # 技能/能力相关
            'skill': self._generate_boolean_value,
            'ability': self._generate_boolean_value,
            'capability': self._generate_boolean_value,
            'permission': self._generate_boolean_value,
            
            # 可用性相关
            'available': self._generate_boolean_value,
            'active': self._generate_boolean_value,
            'enabled': self._generate_boolean_value,
            'valid': self._generate_boolean_value,
            
            # 位置相关
            'location': self._generate_location_value,
            'position': self._generate_position_value,
            'coordinate': self._generate_coordinate_value,
            
            # 大小相关
            'size': self._generate_size_value,
            'length': self._generate_length_value,
            'width': self._generate_width_value,
            'height': self._generate_height_value,
            'weight': self._generate_weight_value,
            
            # 年龄相关
            'age': self._generate_age_value,
            
            # 评分相关
            'score': self._generate_score_value,
            'rating': self._generate_rating_value,
            'points': self._generate_points_value,
        }
    
    def generate(self, entity_name: str, attr: Attribute, context: Dict[str, Any] = None) -> Any:
        """根据语义生成属性值"""
        # 首先检查是否有枚举值
        if attr.enum:
            return random.choice(attr.enum)
        
        # 尝试语义匹配
        attr_lower = attr.name.lower()
        
        # 精确匹配
        for pattern, generator in self.semantic_patterns.items():
            if pattern in attr_lower:
                value = generator(attr, context)
                # 确保值在min/max范围内
                return self._constrain_value(value, attr)
        
        # 如果没有语义匹配，使用父类的默认生成
        return super().generate(entity_name, attr, context)
    
    def _constrain_value(self, value: Any, attr: Attribute) -> Any:
        """确保生成的值在属性的min/max约束范围内"""
        if hasattr(attr, 'min') and attr.min is not None and value < attr.min:
            value = attr.min
        if hasattr(attr, 'max') and attr.max is not None and value > attr.max:
            value = attr.max
        return value
    
    # 距离相关生成器
    def _generate_distance_value(self, attr: Attribute, context: Dict[str, Any] = None) -> float:
        """生成距离值"""
        attr_lower = attr.name.lower()
        
        # 根据属性名中的关键词调整生成策略
        if 'straight' in attr_lower or 'direct' in attr_lower:
            # 直线距离通常较短
            base_ranges = [(0.5, 5.0), (5.1, 15.0), (15.1, 30.0)]
        elif 'navigation' in attr_lower or 'route' in attr_lower:
            # 导航距离通常比直线距离长1.2-1.5倍
            if context and any('distance' in k for k in context.keys()):
                # 如果有其他距离参考，基于它生成
                ref_distance = next(v for k, v in context.items() if 'distance' in k and isinstance(v, (int, float)))
                return round(ref_distance * random.uniform(1.2, 1.5), 2)
            base_ranges = [(0.6, 6.0), (6.1, 20.0), (20.1, 40.0)]
        else:
            # 一般距离
            base_ranges = [(0.1, 10.0), (10.1, 50.0), (50.1, 100.0)]
        
        # 随机选择一个范围
        selected_range = random.choice(base_ranges)
        return round(random.uniform(selected_range[0], selected_range[1]), 2)
    
    # 时间相关生成器
    def _generate_time_value(self, attr: Attribute, context: Dict[str, Any] = None) -> float:
        """生成时间值"""
        # 默认生成0-24小时范围
        return round(random.uniform(0, 24), 2)
    
    def _generate_duration_value(self, attr: Attribute, context: Dict[str, Any] = None) -> float:
        """生成持续时间"""
        attr_lower = attr.name.lower()
        if 'service' in attr_lower:
            # 服务时长通常1-8小时
            durations = [1.0, 1.5, 2.0, 2.5, 3.0, 4.0, 5.0, 6.0, 8.0]
            return random.choice(durations)
        else:
            return round(random.uniform(0.5, 4.0), 1)
    
    def _generate_hours_value(self, attr: Attribute, context: Dict[str, Any] = None) -> float:
        """生成小时数"""
        attr_lower = attr.name.lower()
        if 'until' in attr_lower or 'before' in attr_lower:
            # 距离某事件的时间，生成更多样的值
            ranges = [(0.5, 2.0), (2.1, 6.0), (6.1, 24.0), (24.1, 72.0), (72.1, 168.0)]
            selected_range = random.choice(ranges)
            return round(random.uniform(selected_range[0], selected_range[1]), 1)
        else:
            return round(random.uniform(1, 24), 1)
    
    def _generate_minutes_value(self, attr: Attribute, context: Dict[str, Any] = None) -> int:
        """生成分钟数"""
        return random.randint(1, 60)
    
    def _generate_seconds_value(self, attr: Attribute, context: Dict[str, Any] = None) -> int:
        """生成秒数"""
        return random.randint(1, 60)
    
    def _generate_days_value(self, attr: Attribute, context: Dict[str, Any] = None) -> int:
        """生成天数"""
        return random.randint(1, 30)
    
    # 计数相关生成器
    def _generate_count_value(self, attr: Attribute, context: Dict[str, Any] = None) -> int:
        """生成计数值"""
        attr_lower = attr.name.lower()
        if 'order' in attr_lower:
            # 订单数量分布
            counts = [0, 1, 2, 3, 5, 8, 10]
            return random.choice(counts)
        elif 'rejection' in attr_lower or 'reject' in attr_lower:
            # 拒绝次数分布
            counts = [0, 1, 2, 3, 5, 10]
            return random.choice(counts)
        else:
            return random.randint(0, 10)
    
    def _generate_amount_value(self, attr: Attribute, context: Dict[str, Any] = None) -> float:
        """生成数量值"""
        if attr.type in ['int', 'integer']:
            return random.randint(1, 100)
        else:
            return round(random.uniform(1.0, 1000.0), 2)
    
    # 状态相关生成器
    def _generate_status_value(self, attr: Attribute, context: Dict[str, Any] = None) -> int:
        """生成状态值"""
        # 如果有枚举值，从中选择
        if attr.enum:
            return random.choice(attr.enum)
        # 否则生成1-6的状态值
        return random.randint(1, 6)
    
    def _generate_type_value(self, attr: Attribute, context: Dict[str, Any] = None) -> int:
        """生成类型值"""
        if attr.enum:
            return random.choice(attr.enum)
        return random.randint(1, 5)
    
    def _generate_level_value(self, attr: Attribute, context: Dict[str, Any] = None) -> int:
        """生成级别值"""
        return random.randint(1, 10)
    
    # 标识相关生成器
    def _generate_id_value(self, attr: Attribute, context: Dict[str, Any] = None) -> int:
        """生成ID值"""
        attr_lower = attr.name.lower()
        if 'assigned' in attr_lower:
            # 分配的ID，可能为0（未分配）
            if random.random() < 0.2:
                return 0
            return random.randint(1, 1000)
        else:
            # 使用父类的ID生成器
            return self._generate_id(context.get('entity_name', 'Entity'), attr.name)
    
    def _generate_code_value(self, attr: Attribute, context: Dict[str, Any] = None) -> str:
        """生成代码值"""
        if attr.type in ['int', 'integer']:
            return random.randint(1000, 9999)
        else:
            # 生成字母数字代码
            chars = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789'
            return ''.join(random.choice(chars) for _ in range(6))
    
    def _generate_key_value(self, attr: Attribute, context: Dict[str, Any] = None) -> str:
        """生成键值"""
        return f"KEY_{random.randint(1000, 9999)}"
    
    # 百分比相关生成器
    def _generate_rate_value(self, attr: Attribute, context: Dict[str, Any] = None) -> float:
        """生成比率值（0-1）"""
        return round(random.uniform(0, 1), 2)
    
    def _generate_percentage_value(self, attr: Attribute, context: Dict[str, Any] = None) -> float:
        """生成百分比值（0-100）"""
        return round(random.uniform(0, 100), 1)
    
    # 金额相关生成器
    def _generate_price_value(self, attr: Attribute, context: Dict[str, Any] = None) -> float:
        """生成价格值"""
        price_ranges = [(9.99, 49.99), (50.0, 199.99), (200.0, 999.99)]
        price_range = random.choice(price_ranges)
        return round(random.uniform(price_range[0], price_range[1]), 2)
    
    def _generate_balance_value(self, attr: Attribute, context: Dict[str, Any] = None) -> float:
        """生成余额值"""
        return round(random.uniform(0, 10000), 2)
    
    # 布尔相关生成器
    def _generate_boolean_value(self, attr: Attribute, context: Dict[str, Any] = None) -> bool:
        """生成布尔值"""
        # 对某些属性有偏好
        attr_lower = attr.name.lower()
        if 'is_available' in attr_lower or 'is_active' in attr_lower:
            # 80%概率为True
            return random.random() < 0.8
        return random.choice([True, False])
    
    # 位置相关生成器
    def _generate_location_value(self, attr: Attribute, context: Dict[str, Any] = None) -> Any:
        """生成位置值"""
        if attr.type == 'string':
            locations = ['North', 'South', 'East', 'West', 'Center', 'Downtown', 'Suburb']
            return random.choice(locations)
        else:
            return random.randint(1, 100)
    
    def _generate_position_value(self, attr: Attribute, context: Dict[str, Any] = None) -> int:
        """生成位置值"""
        return random.randint(1, 100)
    
    def _generate_coordinate_value(self, attr: Attribute, context: Dict[str, Any] = None) -> float:
        """生成坐标值"""
        # 生成合理的经纬度范围
        if 'lat' in attr.name.lower():
            return round(random.uniform(-90, 90), 6)
        elif 'lon' in attr.name.lower():
            return round(random.uniform(-180, 180), 6)
        else:
            return round(random.uniform(-1000, 1000), 2)
    
    # 大小相关生成器
    def _generate_size_value(self, attr: Attribute, context: Dict[str, Any] = None) -> float:
        """生成大小值"""
        return round(random.uniform(1, 100), 2)
    
    def _generate_length_value(self, attr: Attribute, context: Dict[str, Any] = None) -> float:
        """生成长度值"""
        return round(random.uniform(0.1, 100), 2)
    
    def _generate_width_value(self, attr: Attribute, context: Dict[str, Any] = None) -> float:
        """生成宽度值"""
        return round(random.uniform(0.1, 100), 2)
    
    def _generate_height_value(self, attr: Attribute, context: Dict[str, Any] = None) -> float:
        """生成高度值"""
        return round(random.uniform(0.1, 100), 2)
    
    def _generate_weight_value(self, attr: Attribute, context: Dict[str, Any] = None) -> float:
        """生成重量值"""
        return round(random.uniform(0.1, 1000), 2)
    
    # 年龄相关生成器
    def _generate_age_value(self, attr: Attribute, context: Dict[str, Any] = None) -> int:
        """生成年龄值"""
        age_ranges = [(18, 25), (26, 35), (36, 50), (51, 65), (66, 80)]
        age_range = random.choice(age_ranges)
        return random.randint(age_range[0], age_range[1])
    
    # 评分相关生成器
    def _generate_score_value(self, attr: Attribute, context: Dict[str, Any] = None) -> float:
        """生成分数值"""
        if attr.type in ['int', 'integer']:
            return random.randint(0, 100)
        else:
            return round(random.uniform(0, 100), 1)
    
    def _generate_rating_value(self, attr: Attribute, context: Dict[str, Any] = None) -> float:
        """生成评级值"""
        # 通常1-5星评级
        ratings = [1.0, 1.5, 2.0, 2.5, 3.0, 3.5, 4.0, 4.5, 5.0]
        return random.choice(ratings)
    
    def _generate_points_value(self, attr: Attribute, context: Dict[str, Any] = None) -> int:
        """生成积分值"""
        return random.randint(0, 1000)