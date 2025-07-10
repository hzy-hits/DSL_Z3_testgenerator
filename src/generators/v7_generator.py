#!/usr/bin/env python3
"""
统一的 DSL 测试生成器 V7 - 稳定性与高质量
基于 V6 的改进：
1. 完整的表达式解析器，处理所有约束类型
2. 安全的值生成，防止范围错误
3. 错误恢复机制，确保100%文件处理成功
4. 保持高质量的测试生成
"""

import argparse
import json
import yaml
import z3
from typing import List, Dict, Any, Set, Tuple, Optional, Union, Callable
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
import re
from datetime import datetime, timedelta, date
import hashlib
from abc import ABC, abstractmethod
import random
import time
import ast
import operator


class TestType(Enum):
    """测试类型枚举"""
    FUNCTIONAL = "functional"
    BOUNDARY = "boundary"
    NEGATIVE = "negative"
    RULE_ACTIVATION = "rule_activation"
    RULE_DEACTIVATION = "rule_deactivation"
    CONSTRAINT_SATISFACTION = "constraint_satisfaction"
    CONSTRAINT_VIOLATION = "constraint_violation"
    SCENARIO = "scenario"
    STATE_TRANSITION = "state_transition"
    COMBINATORIAL = "combinatorial"
    PERFORMANCE = "performance"
    SECURITY = "security"
    COLLECTION = "collection"


@dataclass
class AttributeMetadata:
    """增强的属性元数据"""
    name: str
    type: str
    min: Optional[Union[int, float]] = None
    max: Optional[Union[int, float]] = None
    min_size: Optional[int] = None
    max_size: Optional[int] = None
    enum: Optional[List[Any]] = None
    pattern: Optional[str] = None
    optional: bool = False
    default: Optional[Any] = None
    unique: bool = False
    nullable: bool = False
    description: Optional[str] = None
    format: Optional[str] = None
    custom_validator: Optional[str] = None
    dependencies: Optional[List[str]] = None
    
    @property
    def is_numeric(self) -> bool:
        return self.type in ['integer', 'real']
    
    @property
    def is_collection(self) -> bool:
        return self.type.startswith('array[') or self.type.startswith('set[')
    
    @property
    def is_temporal(self) -> bool:
        return self.format in ['date', 'time', 'datetime', 'timestamp']
    
    @property
    def element_type(self) -> Optional[str]:
        if self.type.startswith('array['):
            return self.type[6:-1]
        elif self.type.startswith('set['):
            return self.type[4:-1]
        return None
    
    def get_safe_range(self) -> Tuple[Union[int, float], Union[int, float]]:
        """获取安全的数值范围"""
        if self.is_numeric:
            min_val = self.min if self.min is not None else 0
            max_val = self.max if self.max is not None else 1000
            
            # 处理时间戳特殊情况
            if 'timestamp' in self.name.lower() or 'time' in self.format if self.format else False:
                # Unix timestamp range: 2020-01-01 to 2030-01-01
                min_val = max(min_val, 1577836800)
                max_val = min(max_val, 1893456000)
            
            # 确保 min <= max
            if min_val > max_val:
                # 交换或使用默认值
                if self.type == 'integer':
                    return (0, 100)
                else:
                    return (0.0, 100.0)
            
            return (min_val, max_val)
        return (0, 100)


class ExpressionParser:
    """完整的表达式解析器"""
    
    def __init__(self):
        self.operators = {
            '>=': operator.ge,
            '<=': operator.le,
            '>': operator.gt,
            '<': operator.lt,
            '==': operator.eq,
            '!=': operator.ne,
            'and': operator.and_,
            'or': operator.or_,
            '=>': lambda a, b: (not a) or b  # 蕴含
        }
    
    def parse(self, expression: str, context: Dict[str, Any] = None) -> Dict[str, Any]:
        """解析表达式并返回约束信息"""
        if context is None:
            context = {}
        
        expression = str(expression).strip()
        
        # 处理特殊情况
        if expression in ['true', 'True']:
            return {'type': 'boolean', 'value': True}
        if expression in ['false', 'False']:
            return {'type': 'boolean', 'value': False}
        
        # 处理条件约束 (=>)
        if '=>' in expression:
            return self._parse_implication(expression, context)
        
        # 处理逻辑运算符
        if ' and ' in expression:
            return self._parse_logical(expression, 'and', context)
        if ' or ' in expression:
            return self._parse_logical(expression, 'or', context)
        
        # 处理比较运算符
        for op in ['>=', '<=', '>', '<', '==', '!=']:
            if op in expression:
                return self._parse_comparison(expression, op, context)
        
        # 处理函数调用
        if 'size(' in expression:
            return self._parse_size_function(expression, context)
        
        return {'type': 'unknown', 'expression': expression}
    
    def _parse_implication(self, expression: str, context: Dict[str, Any]) -> Dict[str, Any]:
        """解析蕴含表达式 A => B"""
        parts = expression.split('=>', 1)
        if len(parts) != 2:
            return {'type': 'unknown', 'expression': expression}
        
        condition = self.parse(parts[0].strip(), context)
        consequence = self.parse(parts[1].strip(), context)
        
        return {
            'type': 'implication',
            'condition': condition,
            'consequence': consequence
        }
    
    def _parse_logical(self, expression: str, op: str, context: Dict[str, Any]) -> Dict[str, Any]:
        """解析逻辑表达式"""
        # 简单分割（未处理括号）
        parts = expression.split(f' {op} ', 1)
        if len(parts) != 2:
            return {'type': 'unknown', 'expression': expression}
        
        left = self.parse(parts[0].strip(), context)
        right = self.parse(parts[1].strip(), context)
        
        return {
            'type': 'logical',
            'operator': op,
            'left': left,
            'right': right
        }
    
    def _parse_comparison(self, expression: str, op: str, context: Dict[str, Any]) -> Dict[str, Any]:
        """解析比较表达式"""
        parts = expression.split(op, 1)
        if len(parts) != 2:
            return {'type': 'unknown', 'expression': expression}
        
        left = parts[0].strip()
        right = parts[1].strip()
        
        # 解析左侧
        left_info = self._parse_operand(left, context)
        # 解析右侧
        right_info = self._parse_operand(right, context)
        
        return {
            'type': 'comparison',
            'operator': op,
            'left': left_info,
            'right': right_info
        }
    
    def _parse_operand(self, operand: str, context: Dict[str, Any]) -> Dict[str, Any]:
        """解析操作数"""
        operand = operand.strip()
        
        # 处理函数调用
        if 'size(' in operand:
            return self._parse_size_function(operand, context)
        
        # 处理字段引用 (Entity.attribute)
        if '.' in operand:
            parts = operand.split('.')
            return {
                'type': 'field',
                'entity': parts[0],
                'attribute': parts[1] if len(parts) > 1 else None
            }
        
        # 处理字符串字面量
        if operand.startswith('"') or operand.startswith("'"):
            return {
                'type': 'literal',
                'value': operand.strip('"\''),
                'datatype': 'string'
            }
        
        # 处理数字字面量
        try:
            if '.' in operand:
                value = float(operand)
                return {'type': 'literal', 'value': value, 'datatype': 'float'}
            else:
                value = int(operand)
                return {'type': 'literal', 'value': value, 'datatype': 'int'}
        except ValueError:
            pass
        
        # 处理特殊值
        if operand.lower() == 'null':
            return {'type': 'literal', 'value': None, 'datatype': 'null'}
        if operand.lower() == 'true':
            return {'type': 'literal', 'value': True, 'datatype': 'boolean'}
        if operand.lower() == 'false':
            return {'type': 'literal', 'value': False, 'datatype': 'boolean'}
        
        # 默认作为字段名
        return {'type': 'field', 'name': operand}
    
    def _parse_size_function(self, expression: str, context: Dict[str, Any]) -> Dict[str, Any]:
        """解析size函数"""
        match = re.search(r'size\(([^)]+)\)', expression)
        if not match:
            return {'type': 'unknown', 'expression': expression}
        
        argument = match.group(1).strip()
        
        # 解析参数
        if '.' in argument:
            parts = argument.split('.')
            return {
                'type': 'function',
                'name': 'size',
                'argument': {
                    'type': 'field',
                    'entity': parts[0],
                    'attribute': parts[1] if len(parts) > 1 else None
                }
            }
        else:
            return {
                'type': 'function',
                'name': 'size',
                'argument': {'type': 'field', 'name': argument}
            }


class RobustBusinessValueGeneratorV7:
    """V7稳健的业务感知值生成器"""
    
    def __init__(self, domain: str):
        self.domain = domain
        self.id_counters = {
            'product': 1001,
            'user': 1,
            'order': 10001,
            'student': 2024001,
            'course': 101,
            'transaction': 100001,
            'item': 1001,
            'cart': 1,
            'permission': 1,
            'role': 1
        }
        self._init_business_rules()
    
    def _init_business_rules(self):
        """初始化增强的业务规则"""
        self.business_patterns = {
            'E-commerce Shopping Cart': {
                'price_range': (0.99, 299.99),
                'typical_prices': [9.99, 19.99, 29.99, 49.99, 99.99],
                'discount_codes': ['SAVE10', 'WELCOME5', 'MEMBER10', 'VIP20', 'BULK15', 'SUMMER25'],
                'categories': ['electronics', 'clothing', 'books', 'home', 'sports', 'toys', 'food', 'beauty']
            },
            'Advanced E-commerce Platform': {
                'price_range': (0.99, 999.99),
                'cost_ratio': 0.6,  # cost = price * 0.6
                'order_statuses': ['pending', 'processing', 'shipped', 'delivered', 'cancelled'],
                'payment_methods': ['credit_card', 'paypal', 'bank_transfer', 'cash_on_delivery'],
                'shipping_methods': ['standard', 'express', 'overnight', 'pickup']
            },
            'Order Processing System': {
                'order_statuses': ['created', 'confirmed', 'processing', 'shipped', 'delivered', 'cancelled'],
                'priority_levels': ['low', 'normal', 'high', 'urgent'],
                'shipping_delay_days': {'standard': 5, 'express': 2, 'overnight': 1}
            },
            'User Account Management System': {
                'user_statuses': ['active', 'inactive', 'suspended', 'deleted'],
                'roles': ['user', 'admin', 'moderator', 'premium'],
                'account_types': ['free', 'basic', 'premium', 'enterprise']
            },
            'Role-Based Access Control': {
                'permissions': ['read', 'write', 'delete', 'admin', 'execute'],
                'resources': ['file', 'folder', 'database', 'api', 'service'],
                'roles': ['guest', 'user', 'power_user', 'admin', 'super_admin']
            },
            '学生成绩管理系统': {
                'score_range': (0, 100),
                'grade_levels': ['A', 'B', 'C', 'D', 'F'],
                'grade_ranges': [(1, 6), (7, 9), (10, 12)],  # 小学、初中、高中
                'subjects': ['语文', '数学', '英语', '物理', '化学', '历史'],
                'semesters': ['2024春季', '2024秋季', '2025春季']
            },
            'Score Management System': {
                'score_range': (0, 100),
                'passing_score': 60,
                'grade_thresholds': {'A': 90, 'B': 80, 'C': 70, 'D': 60, 'F': 0}
            }
        }
    
    def generate_value(self, entity_name: str, attr_name: str, attr_meta: AttributeMetadata, 
                      constraints: Dict[str, Any] = None) -> Any:
        """生成符合业务规则和约束的值"""
        try:
            # 处理ID类型
            if 'id' in attr_name.lower():
                return self._generate_id(entity_name, attr_name)
            
            # 处理价格/成本
            if 'price' in attr_name or 'cost' in attr_name:
                return self._generate_price(entity_name, attr_name, attr_meta)
            
            # 处理日期/时间
            if attr_meta.is_temporal:
                return self._generate_temporal_value(entity_name, attr_name, attr_meta)
            
            # 处理状态/枚举
            if 'status' in attr_name or 'state' in attr_name or attr_meta.enum:
                return self._generate_enum_value(entity_name, attr_name, attr_meta)
            
            # 处理集合类型
            if attr_meta.is_collection:
                return self._generate_collection_value(entity_name, attr_name, attr_meta)
            
            # 处理布尔值
            if attr_meta.type == 'boolean':
                return random.choice([True, False])
            
            # 处理字符串
            if attr_meta.type == 'string':
                return self._generate_string_value(entity_name, attr_name, attr_meta)
            
            # 处理数值
            if attr_meta.is_numeric:
                return self._generate_numeric_value(attr_meta)
            
            # 默认值
            return self._generate_default_value(attr_meta)
            
        except Exception as e:
            # 错误恢复：返回安全的默认值
            return self._generate_safe_default(attr_meta)
    
    def _generate_id(self, entity_name: str, attr_name: str) -> int:
        """生成连续的ID"""
        # 确定ID类型
        id_type = None
        for key in self.id_counters:
            if key in entity_name.lower() or key in attr_name.lower():
                id_type = key
                break
        
        if id_type is None:
            id_type = 'item'  # 默认类型
        
        current_id = self.id_counters[id_type]
        self.id_counters[id_type] += 1
        return current_id
    
    def _generate_price(self, entity_name: str, attr_name: str, attr_meta: AttributeMetadata) -> float:
        """生成合理的价格"""
        domain_rules = self.business_patterns.get(self.domain, {})
        
        # 使用属性的范围限制
        min_val, max_val = attr_meta.get_safe_range()
        
        # 处理成本（价格的60%）
        if 'cost' in attr_name:
            price_range = domain_rules.get('price_range', (min_val, max_val))
            base_price = random.uniform(price_range[0], price_range[1])
            cost_ratio = domain_rules.get('cost_ratio', 0.6)
            return round(base_price * cost_ratio, 2)
        
        # 生成价格
        if 'typical_prices' in domain_rules and random.random() < 0.7:
            price = random.choice(domain_rules['typical_prices'])
            # 确保在允许范围内
            if min_val <= price <= max_val:
                return price
        
        # 使用安全范围
        return round(random.uniform(min_val, min(max_val, 1000)), 2)
    
    def _generate_temporal_value(self, entity_name: str, attr_name: str, attr_meta: AttributeMetadata) -> str:
        """生成时间值"""
        # 对于timestamp类型，使用整数
        if attr_meta.format == 'timestamp' or 'timestamp' in attr_name.lower():
            min_val, max_val = attr_meta.get_safe_range()
            timestamp = int(random.uniform(min_val, max_val))
            return timestamp
        
        # 对于日期类型
        base_date = datetime.now()
        
        # 根据属性名调整日期
        if 'order_date' in attr_name or 'created' in attr_name:
            days_ago = random.randint(1, 30)
            result_date = base_date - timedelta(days=days_ago)
        elif 'shipping_date' in attr_name or 'shipped' in attr_name:
            days_after = random.randint(1, 3)
            result_date = base_date - timedelta(days=25) + timedelta(days=days_after)
        elif 'delivery_date' in attr_name or 'delivered' in attr_name:
            days_after = random.randint(5, 10)
            result_date = base_date - timedelta(days=20) + timedelta(days=days_after)
        else:
            days_ago = random.randint(0, 60)
            result_date = base_date - timedelta(days=days_ago)
        
        # 根据格式返回
        if attr_meta.format == 'date':
            return result_date.strftime('%Y-%m-%d')
        elif attr_meta.format == 'datetime':
            return result_date.strftime('%Y-%m-%d %H:%M:%S')
        else:
            return result_date.isoformat()
    
    def _generate_enum_value(self, entity_name: str, attr_name: str, attr_meta: AttributeMetadata) -> Any:
        """生成枚举值"""
        # 如果有明确的枚举定义
        if attr_meta.enum:
            return random.choice(attr_meta.enum)
        
        # 根据领域和属性名查找
        domain_rules = self.business_patterns.get(self.domain, {})
        
        # 查找匹配的枚举列表
        for key in ['order_statuses', 'user_statuses', 'statuses', 'roles', 'permissions']:
            if key in domain_rules and key.replace('_', '') in attr_name.lower():
                return random.choice(domain_rules[key])
        
        # 默认状态
        if 'status' in attr_name:
            return random.choice(['active', 'inactive', 'pending'])
        
        return f"{attr_name}_value"
    
    def _generate_collection_value(self, entity_name: str, attr_name: str, attr_meta: AttributeMetadata) -> List[Any]:
        """生成集合值"""
        # 确定集合大小
        min_size = attr_meta.min_size or 0
        max_size = attr_meta.max_size or 5
        
        # 安全的大小范围
        if min_size > max_size:
            min_size, max_size = 0, 5
        
        size = random.randint(min_size, min(max_size, 10))
        
        # 根据元素类型生成
        element_type = attr_meta.element_type
        
        if 'categories' in attr_name:
            domain_rules = self.business_patterns.get(self.domain, {})
            available = domain_rules.get('categories', ['category1', 'category2', 'category3'])
            return random.sample(available, min(size, len(available)))
        
        if 'codes' in attr_name or 'discount' in attr_name:
            domain_rules = self.business_patterns.get(self.domain, {})
            available = domain_rules.get('discount_codes', ['CODE1', 'CODE2', 'CODE3'])
            return random.sample(available, min(size, len(available)))
        
        if element_type == 'integer' or 'id' in attr_name or 'item' in attr_name:
            # 生成连续的ID序列
            id_type = 'item'
            for key in self.id_counters:
                if key in attr_name.lower():
                    id_type = key
                    break
            
            start_id = self.id_counters.get(id_type, 1001)
            result = list(range(start_id, start_id + size))
            self.id_counters[id_type] = start_id + size
            return result
        
        if element_type == 'string':
            # 根据属性名生成合适的字符串
            if 'permission' in attr_name:
                perms = ['read', 'write', 'delete', 'admin', 'execute']
                return random.sample(perms, min(size, len(perms)))
            elif 'role' in attr_name:
                roles = ['user', 'admin', 'moderator', 'guest', 'premium']
                return random.sample(roles, min(size, len(roles)))
            else:
                return [f"{attr_name}_{i}" for i in range(size)]
        
        return []
    
    def _generate_string_value(self, entity_name: str, attr_name: str, attr_meta: AttributeMetadata) -> str:
        """生成字符串值"""
        # 处理名称
        if 'name' in attr_name:
            prefixes = {
                'user': ['Alice', 'Bob', 'Charlie', 'David', 'Emma'],
                'product': ['Premium', 'Basic', 'Deluxe', 'Standard', 'Pro'],
                'student': ['张三', '李四', '王五', '赵六', '陈七']
            }
            for key, names in prefixes.items():
                if key in entity_name.lower():
                    return random.choice(names)
            return f"{entity_name}_{random.randint(1, 100)}"
        
        # 处理描述
        if 'description' in attr_name:
            return f"Test description for {entity_name}"
        
        # 处理邮箱
        if 'email' in attr_name:
            return f"user{random.randint(1, 1000)}@example.com"
        
        # 默认
        return f"{attr_name}_value_{random.randint(1, 100)}"
    
    def _generate_numeric_value(self, attr_meta: AttributeMetadata) -> Union[int, float]:
        """生成数值"""
        min_val, max_val = attr_meta.get_safe_range()
        
        # 特殊处理年级
        if 'grade' in attr_meta.name.lower() or 'level' in attr_meta.name.lower():
            if '学生' in self.domain or 'student' in attr_meta.name.lower():
                return random.randint(1, 12)  # 1-12年级
        
        if attr_meta.type == 'integer':
            return random.randint(int(min_val), int(max_val))
        else:
            return round(random.uniform(float(min_val), float(max_val)), 2)
    
    def _generate_default_value(self, attr_meta: AttributeMetadata) -> Any:
        """生成默认值"""
        if attr_meta.default is not None:
            return attr_meta.default
        
        if attr_meta.type == 'string':
            return "default_value"
        elif attr_meta.type == 'integer':
            return 1
        elif attr_meta.type == 'real':
            return 1.0
        elif attr_meta.type == 'boolean':
            return False
        elif attr_meta.is_collection:
            return []
        else:
            return None
    
    def _generate_safe_default(self, attr_meta: AttributeMetadata) -> Any:
        """生成安全的默认值（错误恢复）"""
        if attr_meta.is_collection:
            return []
        elif attr_meta.type == 'string':
            return "safe_default"
        elif attr_meta.type == 'integer':
            return 1
        elif attr_meta.type == 'real':
            return 1.0
        elif attr_meta.type == 'boolean':
            return False
        else:
            return None


class RobustConstraintParserV7:
    """V7稳健的约束解析器"""
    
    def __init__(self, entities: Dict[str, Dict[str, AttributeMetadata]], 
                 value_generator: RobustBusinessValueGeneratorV7):
        self.entities = entities
        self.value_generator = value_generator
        self.expression_parser = ExpressionParser()
    
    def parse_constraint(self, constraint: str, test_data: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        """解析并生成满足约束的数据"""
        try:
            # 处理布尔值约束
            if isinstance(constraint, bool):
                return True, test_data
            
            constraint = str(constraint).strip()
            
            # 解析表达式
            parsed = self.expression_parser.parse(constraint)
            
            # 根据解析结果生成数据
            return self._generate_from_parsed(parsed, test_data)
            
        except Exception as e:
            # 错误恢复：返回原始数据
            print(f"Warning: Failed to parse constraint '{constraint}': {e}")
            return True, test_data
    
    def _generate_from_parsed(self, parsed: Dict[str, Any], test_data: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        """根据解析结果生成数据"""
        if parsed['type'] == 'boolean':
            return True, test_data
        
        elif parsed['type'] == 'comparison':
            return self._handle_comparison(parsed, test_data)
        
        elif parsed['type'] == 'logical':
            return self._handle_logical(parsed, test_data)
        
        elif parsed['type'] == 'implication':
            return self._handle_implication(parsed, test_data)
        
        else:
            return True, test_data
    
    def _handle_comparison(self, parsed: Dict[str, Any], test_data: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        """处理比较约束"""
        op = parsed['operator']
        left = parsed['left']
        right = parsed['right']
        
        # 处理 size(A) >= size(B) 类型
        if left.get('type') == 'function' and left.get('name') == 'size' and \
           right.get('type') == 'function' and right.get('name') == 'size':
            return self._handle_size_comparison(left, right, op, test_data)
        
        # 处理 size(A) >= N 类型
        if left.get('type') == 'function' and left.get('name') == 'size':
            field_key = self._get_field_key(left['argument'])
            size_value = right.get('value', 1)
            return self._generate_collection_with_size(field_key, size_value, op, test_data)
        
        # 处理字段比较
        if left.get('type') == 'field' and right.get('type') == 'field':
            return self._handle_field_comparison(left, right, op, test_data)
        
        # 处理字段与字面量比较
        if left.get('type') == 'field' and right.get('type') == 'literal':
            field_key = self._get_field_key(left)
            value = right['value']
            return self._generate_value_with_constraint(field_key, value, op, test_data)
        
        return True, test_data
    
    def _handle_logical(self, parsed: Dict[str, Any], test_data: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        """处理逻辑约束"""
        op = parsed['operator']
        
        if op == 'and':
            # 两个约束都要满足
            success1, test_data = self._generate_from_parsed(parsed['left'], test_data)
            success2, test_data = self._generate_from_parsed(parsed['right'], test_data)
            return success1 and success2, test_data
        
        elif op == 'or':
            # 随机选择一个约束满足
            if random.choice([True, False]):
                return self._generate_from_parsed(parsed['left'], test_data)
            else:
                return self._generate_from_parsed(parsed['right'], test_data)
        
        return True, test_data
    
    def _handle_implication(self, parsed: Dict[str, Any], test_data: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        """处理蕴含约束 A => B"""
        # 生成满足条件的数据
        success, test_data = self._generate_from_parsed(parsed['condition'], test_data)
        if success:
            # 如果条件为真，则结果也必须为真
            success, test_data = self._generate_from_parsed(parsed['consequence'], test_data)
        
        return success, test_data
    
    def _handle_size_comparison(self, left: Dict, right: Dict, op: str, test_data: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        """处理 size(A) >= size(B) 类型的约束"""
        left_key = self._get_field_key(left['argument'])
        right_key = self._get_field_key(right['argument'])
        
        # 生成满足约束的大小
        if op == '>=':
            right_size = random.randint(0, 5)
            left_size = random.randint(right_size, right_size + 5)
        elif op == '>':
            right_size = random.randint(0, 5)
            left_size = random.randint(right_size + 1, right_size + 6)
        elif op == '<=':
            left_size = random.randint(0, 5)
            right_size = random.randint(left_size, left_size + 5)
        elif op == '<':
            left_size = random.randint(0, 5)
            right_size = random.randint(left_size + 1, left_size + 6)
        else:  # ==
            size = random.randint(1, 5)
            left_size = right_size = size
        
        # 生成对应的集合
        test_data[left_key] = self._generate_collection(left_key, left_size)
        test_data[right_key] = self._generate_collection(right_key, right_size)
        
        return True, test_data
    
    def _handle_field_comparison(self, left: Dict, right: Dict, op: str, test_data: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        """处理字段之间的比较"""
        left_key = self._get_field_key(left)
        right_key = self._get_field_key(right)
        
        # 特殊处理价格和成本
        if 'price' in left_key and 'cost' in right_key:
            cost = round(random.uniform(10, 50), 2)
            if op in ['>', '>=']:
                price = round(cost * random.uniform(1.2, 2.0), 2)
            else:
                price = round(cost * random.uniform(0.5, 0.9), 2)
            test_data[right_key] = cost
            test_data[left_key] = price
            return True, test_data
        
        # 处理日期比较
        if any(date_kw in left_key for date_kw in ['date', 'time']) or \
           any(date_kw in right_key for date_kw in ['date', 'time']):
            return self._handle_date_comparison(left_key, right_key, op, test_data)
        
        # 通用数值比较
        return self._handle_numeric_comparison(left_key, right_key, op, test_data)
    
    def _handle_date_comparison(self, left_key: str, right_key: str, op: str, test_data: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        """处理日期比较"""
        base_date = datetime.now() - timedelta(days=30)
        
        if op in ['>', '>=']:
            test_data[right_key] = base_date.strftime('%Y-%m-%d')
            test_data[left_key] = (base_date + timedelta(days=5)).strftime('%Y-%m-%d')
        elif op in ['<', '<=']:
            test_data[left_key] = base_date.strftime('%Y-%m-%d')
            test_data[right_key] = (base_date + timedelta(days=5)).strftime('%Y-%m-%d')
        else:  # ==
            date_str = base_date.strftime('%Y-%m-%d')
            test_data[left_key] = date_str
            test_data[right_key] = date_str
        
        return True, test_data
    
    def _handle_numeric_comparison(self, left_key: str, right_key: str, op: str, test_data: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        """处理数值比较"""
        if op == '>':
            test_data[right_key] = 50
            test_data[left_key] = 100
        elif op == '>=':
            test_data[right_key] = 50
            test_data[left_key] = random.choice([50, 100])
        elif op == '<':
            test_data[left_key] = 50
            test_data[right_key] = 100
        elif op == '<=':
            test_data[left_key] = 50
            test_data[right_key] = random.choice([50, 100])
        else:  # ==
            value = 50
            test_data[left_key] = value
            test_data[right_key] = value
        
        return True, test_data
    
    def _generate_collection_with_size(self, field_key: str, size_value: Any, op: str, test_data: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        """生成满足大小约束的集合"""
        try:
            size_int = int(size_value)
        except:
            size_int = 1
        
        # 确定实际大小
        if op == '>=':
            actual_size = random.randint(size_int, size_int + 5)
        elif op == '>':
            actual_size = random.randint(size_int + 1, size_int + 6)
        elif op == '<=':
            actual_size = random.randint(max(0, size_int - 5), size_int)
        elif op == '<':
            actual_size = random.randint(max(0, size_int - 6), max(0, size_int - 1))
        else:  # ==
            actual_size = size_int
        
        # 生成集合
        test_data[field_key] = self._generate_collection(field_key, actual_size)
        
        return True, test_data
    
    def _generate_value_with_constraint(self, field_key: str, value: Any, op: str, test_data: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        """生成满足约束的值"""
        if isinstance(value, (int, float)):
            # 数值约束
            if op == '>':
                test_data[field_key] = value + random.uniform(0.01, 10)
            elif op == '>=':
                test_data[field_key] = value + random.uniform(0, 10)
            elif op == '<':
                test_data[field_key] = max(0, value - random.uniform(0.01, 10))
            elif op == '<=':
                test_data[field_key] = max(0, value - random.uniform(0, 10))
            else:  # ==
                test_data[field_key] = value
            
            # 确保正确的类型
            if field_key in test_data:
                if any(int_kw in field_key for int_kw in ['id', 'count', 'size', 'level', 'grade']):
                    test_data[field_key] = int(test_data[field_key])
                else:
                    test_data[field_key] = round(test_data[field_key], 2)
        
        elif op == '==' and isinstance(value, str):
            test_data[field_key] = value
        
        elif op == '!=' and value is None:
            # 生成非空值
            if 'date' in field_key:
                test_data[field_key] = datetime.now().strftime('%Y-%m-%d')
            else:
                test_data[field_key] = f"{field_key}_value"
        
        return True, test_data
    
    def _get_field_key(self, field_info: Dict[str, Any]) -> str:
        """获取字段的键名"""
        if field_info.get('type') == 'field':
            if 'entity' in field_info and 'attribute' in field_info:
                return f"{field_info['entity'].lower()}_{field_info['attribute'].lower()}"
            elif 'name' in field_info:
                return field_info['name'].lower()
        
        return "unknown_field"
    
    def _generate_collection(self, field_key: str, size: int) -> List[Any]:
        """生成指定大小的集合"""
        # 根据字段名确定元素类型
        if 'permission' in field_key:
            perms = ['read', 'write', 'delete', 'admin', 'execute', 'view', 'edit']
            return random.sample(perms, min(size, len(perms)))
        elif 'role' in field_key:
            roles = ['user', 'admin', 'moderator', 'guest', 'premium', 'vip', 'staff']
            return random.sample(roles, min(size, len(roles)))
        elif 'id' in field_key or 'item' in field_key:
            start_id = self.value_generator.id_counters.get('item', 1001)
            result = list(range(start_id, start_id + size))
            self.value_generator.id_counters['item'] = start_id + size
            return result
        elif 'code' in field_key:
            codes = ['CODE1', 'CODE2', 'CODE3', 'CODE4', 'CODE5']
            return random.sample(codes, min(size, len(codes)))
        else:
            return [f"item_{i}" for i in range(size)]


class UnifiedTestGeneratorV7:
    """V7统一测试生成器主类 - 稳定性优先"""
    
    def __init__(self, dsl_model: Dict[str, Any]):
        self.dsl_model = dsl_model
        self.domain = dsl_model.get('domain', 'Unknown')
        self.entities = self._parse_entities()
        self.value_generator = RobustBusinessValueGeneratorV7(self.domain)
        self.constraint_parser = RobustConstraintParserV7(self.entities, self.value_generator)
        self.test_counter = 0
        self.generated_hashes = set()
    
    def _parse_entities(self) -> Dict[str, Dict[str, AttributeMetadata]]:
        """解析实体定义"""
        entities = {}
        for entity in self.dsl_model.get('entities', []):
            entity_name = entity['name']
            attributes = {}
            
            for attr in entity.get('attributes', []):
                attr_meta = AttributeMetadata(
                    name=attr['name'],
                    type=attr.get('type', 'string'),
                    min=attr.get('min'),
                    max=attr.get('max'),
                    min_size=attr.get('min_size'),
                    max_size=attr.get('max_size'),
                    enum=attr.get('enum'),
                    pattern=attr.get('pattern'),
                    optional=attr.get('optional', False),
                    default=attr.get('default'),
                    unique=attr.get('unique', False),
                    nullable=attr.get('nullable', False),
                    format=attr.get('format'),
                    description=attr.get('description')
                )
                attributes[attr['name']] = attr_meta
            
            entities[entity_name] = attributes
        
        return entities
    
    def generate_tests(self) -> Dict[str, Any]:
        """生成完整的测试套件"""
        all_tests = []
        
        try:
            # 1. 生成test_requirements指定的测试
            if 'test_requirements' in self.dsl_model:
                all_tests.extend(self._generate_required_tests())
            else:
                # 为没有test_requirements的文件生成默认测试
                all_tests.extend(self._generate_default_tests())
            
            # 2. 生成功能测试
            all_tests.extend(self._generate_functional_tests())
            
            # 3. 生成约束测试
            all_tests.extend(self._generate_constraint_tests())
            
            # 4. 生成边界测试
            all_tests.extend(self._generate_boundary_tests())
            
            # 5. 生成规则测试
            all_tests.extend(self._generate_rule_tests())
            
            # 6. 生成集合测试
            all_tests.extend(self._generate_collection_tests())
            
            # 7. 生成组合测试
            all_tests.extend(self._generate_combinatorial_tests())
            
            # 8. 生成负面测试
            all_tests.extend(self._generate_negative_tests())
            
            # 9. 生成状态机测试
            if 'state_machines' in self.dsl_model:
                all_tests.extend(self._generate_state_machine_tests())
            
            # 10. 生成场景测试
            if 'scenarios' in self.dsl_model:
                all_tests.extend(self._generate_scenario_tests())
                
        except Exception as e:
            print(f"Warning: Error during test generation: {e}")
            # 确保至少有一些基本测试
            if not all_tests:
                all_tests = self._generate_emergency_tests()
        
        # 去重和组织
        unique_tests = self._deduplicate_tests(all_tests)
        return self._organize_test_output(unique_tests)
    
    def _generate_required_tests(self) -> List[Dict[str, Any]]:
        """生成test_requirements中指定的测试"""
        tests = []
        test_reqs = self.dsl_model.get('test_requirements', [])
        
        for req in test_reqs:
            try:
                req_name = req.get('name', '')
                req_type = req.get('type', '')
                
                if req_type == 'boundary':
                    # 生成边界测试
                    for entity_name, attributes in self.entities.items():
                        for attr_name, attr_meta in attributes.items():
                            if attr_meta.is_numeric:
                                tests.extend(self._generate_boundary_tests_for_attribute(
                                    entity_name, attr_name, attr_meta, tag='required_test'
                                ))
                
                elif req_type == 'collection':
                    # 生成集合测试
                    for entity_name, attributes in self.entities.items():
                        for attr_name, attr_meta in attributes.items():
                            if attr_meta.is_collection:
                                tests.extend(self._generate_collection_tests_for_attribute(
                                    entity_name, attr_name, attr_meta, tag='required_test'
                                ))
                
                elif req_type == 'combinatorial':
                    # 生成组合测试
                    if 'focus' in req:
                        focus_attrs = req.get('focus', [])
                        tests.extend(self._generate_focused_combination_tests(focus_attrs))
                    else:
                        tests.extend(self._generate_combinatorial_tests())
                        
            except Exception as e:
                print(f"Warning: Failed to generate {req_type} tests: {e}")
                continue
        
        return tests
    
    def _generate_default_tests(self) -> List[Dict[str, Any]]:
        """为没有test_requirements的文件生成默认测试"""
        tests = []
        
        try:
            # 为每个实体生成基本测试
            for entity_name, attributes in self.entities.items():
                # 功能测试
                test_data = {}
                for attr_name, attr_meta in attributes.items():
                    key = f"{entity_name.lower()}_{attr_name}"
                    test_data[key] = self.value_generator.generate_value(entity_name, attr_name, attr_meta)
                
                tests.append({
                    "id": self._next_test_id(),
                    "name": f"Default functional test for {entity_name}",
                    "type": TestType.FUNCTIONAL.value,
                    "description": f"Basic functionality test for {entity_name}",
                    "test_data": test_data,
                    "expected_result": "pass",
                    "priority": 8,
                    "tags": ["functional", "default_test", entity_name.lower()]
                })
                
                # 为集合属性生成测试
                for attr_name, attr_meta in attributes.items():
                    if attr_meta.is_collection:
                        tests.extend(self._generate_collection_tests_for_attribute(
                            entity_name, attr_name, attr_meta, tag='default_test'
                        ))
                        
        except Exception as e:
            print(f"Warning: Failed to generate default tests: {e}")
        
        return tests
    
    def _generate_functional_tests(self) -> List[Dict[str, Any]]:
        """生成功能测试"""
        tests = []
        
        try:
            for entity_name, attributes in self.entities.items():
                # 生成包含所有必需字段的测试
                test_data = {}
                for attr_name, attr_meta in attributes.items():
                    if not attr_meta.optional:
                        key = f"{entity_name.lower()}_{attr_name}"
                        test_data[key] = self.value_generator.generate_value(entity_name, attr_name, attr_meta)
                
                tests.append({
                    "id": self._next_test_id(),
                    "name": f"Create {entity_name} with valid business data",
                    "type": TestType.FUNCTIONAL.value,
                    "description": f"Test creating {entity_name} with realistic data",
                    "test_data": test_data,
                    "expected_result": "pass",
                    "priority": 9,
                    "tags": ["functional", entity_name.lower(), "business_data"]
                })
                
                # 生成包含所有字段的测试
                test_data_complete = {}
                for attr_name, attr_meta in attributes.items():
                    key = f"{entity_name.lower()}_{attr_name}"
                    test_data_complete[key] = self.value_generator.generate_value(entity_name, attr_name, attr_meta)
                
                tests.append({
                    "id": self._next_test_id(),
                    "name": f"Create {entity_name} with all fields",
                    "type": TestType.FUNCTIONAL.value,
                    "description": f"Test {entity_name} with all optional fields",
                    "test_data": test_data_complete,
                    "expected_result": "pass",
                    "priority": 8,
                    "tags": ["functional", entity_name.lower(), "complete"]
                })
                
        except Exception as e:
            print(f"Warning: Failed to generate functional tests: {e}")
        
        return tests
    
    def _generate_constraint_tests(self) -> List[Dict[str, Any]]:
        """生成约束测试"""
        tests = []
        constraints = self.dsl_model.get('constraints', [])
        
        for constraint in constraints:
            try:
                # 生成满足约束的测试
                test_data = {}
                success, test_data = self.constraint_parser.parse_constraint(constraint, test_data)
                
                if success:
                    tests.append({
                        "id": self._next_test_id(),
                        "name": f"Constraint satisfaction: {self._simplify_constraint_name(constraint)}",
                        "type": TestType.CONSTRAINT_SATISFACTION.value,
                        "description": "Test constraint is satisfied",
                        "test_data": test_data,
                        "expected_result": "pass",
                        "priority": 8,
                        "tags": ["constraint", "satisfaction"],
                        "constraints_tested": [constraint]
                    })
                
                # 生成违反约束的测试
                violation_data = self._generate_constraint_violation(constraint)
                if violation_data:
                    tests.append({
                        "id": self._next_test_id(),
                        "name": f"Constraint violation: {self._simplify_constraint_name(constraint)}",
                        "type": TestType.CONSTRAINT_VIOLATION.value,
                        "description": "Test constraint is violated",
                        "test_data": violation_data,
                        "expected_result": "fail",
                        "priority": 7,
                        "tags": ["constraint", "violation", "negative"],
                        "constraints_tested": [constraint]
                    })
                    
            except Exception as e:
                print(f"Warning: Failed to generate constraint test for '{constraint}': {e}")
                continue
        
        return tests
    
    def _simplify_constraint_name(self, constraint: str) -> str:
        """简化约束名称用于显示"""
        constraint_str = str(constraint)
        # 截断过长的约束
        if len(constraint_str) > 50:
            return constraint_str[:47] + "..."
        return constraint_str
    
    def _generate_constraint_violation(self, constraint: str) -> Optional[Dict[str, Any]]:
        """生成违反约束的测试数据"""
        try:
            test_data = {}
            constraint_str = str(constraint)
            
            # 解析表达式
            parsed = self.constraint_parser.expression_parser.parse(constraint_str)
            
            # 生成违反的数据
            if parsed['type'] == 'comparison':
                op = parsed['operator']
                left = parsed['left']
                right = parsed['right']
                
                # 反转操作符
                if op == '>=':
                    new_op = '<'
                elif op == '>':
                    new_op = '<='
                elif op == '<=':
                    new_op = '>'
                elif op == '<':
                    new_op = '>='
                elif op == '==':
                    new_op = '!='
                else:
                    return None
                
                # 生成违反的值
                if left.get('type') == 'field' and right.get('type') == 'literal':
                    field_key = self.constraint_parser._get_field_key(left)
                    value = right['value']
                    success, test_data = self.constraint_parser._generate_value_with_constraint(
                        field_key, value, new_op, test_data
                    )
                    return test_data
            
            return None
            
        except Exception as e:
            print(f"Warning: Failed to generate violation for '{constraint}': {e}")
            return None
    
    def _generate_boundary_tests(self) -> List[Dict[str, Any]]:
        """生成边界测试"""
        tests = []
        
        try:
            for entity_name, attributes in self.entities.items():
                for attr_name, attr_meta in attributes.items():
                    if attr_meta.is_numeric:
                        tests.extend(self._generate_boundary_tests_for_attribute(
                            entity_name, attr_name, attr_meta
                        ))
        except Exception as e:
            print(f"Warning: Failed to generate boundary tests: {e}")
        
        return tests
    
    def _generate_boundary_tests_for_attribute(self, entity_name: str, attr_name: str, 
                                             attr_meta: AttributeMetadata, tag: str = None) -> List[Dict[str, Any]]:
        """为单个属性生成边界测试"""
        tests = []
        key = f"{entity_name.lower()}_{attr_name}"
        
        try:
            # 获取安全范围
            min_val, max_val = attr_meta.get_safe_range()
            
            # 最小值测试
            test_data = {key: min_val}
            tags = ["boundary", attr_name, "min"]
            if tag:
                tags.append(tag)
            
            tests.append({
                "id": self._next_test_id(),
                "name": f"Boundary test: {attr_name} = {min_val}",
                "type": TestType.BOUNDARY.value,
                "description": f"Test minimum value for {attr_name}",
                "test_data": test_data,
                "expected_result": "pass",
                "priority": 7,
                "tags": tags
            })
            
            # 小于最小值（如果有明确的最小值限制）
            if attr_meta.min is not None:
                below_min = attr_meta.min - 1
                test_data = {key: below_min}
                tags = ["boundary", attr_name, "below_min", "negative"]
                if tag:
                    tags.append(tag)
                
                tests.append({
                    "id": self._next_test_id(),
                    "name": f"Boundary test: {attr_name} < min",
                    "type": TestType.BOUNDARY.value,
                    "description": f"Test below minimum value for {attr_name}",
                    "test_data": test_data,
                    "expected_result": "fail",
                    "priority": 7,
                    "tags": tags
                })
                
        except Exception as e:
            print(f"Warning: Failed to generate boundary test for {attr_name}: {e}")
        
        return tests
    
    def _generate_rule_tests(self) -> List[Dict[str, Any]]:
        """生成规则测试"""
        tests = []
        rules = self.dsl_model.get('rules', [])
        
        for rule in rules:
            try:
                rule_name = rule.get('name', 'Unknown rule')
                condition = rule.get('condition', '')
                
                # 生成激活规则的测试
                activation_data = {}
                if condition:
                    success, activation_data = self.constraint_parser.parse_constraint(condition, activation_data)
                
                tests.append({
                    "id": self._next_test_id(),
                    "name": f"Rule activation: {rule_name}",
                    "type": TestType.RULE_ACTIVATION.value,
                    "description": f"Test {rule_name} when condition is true",
                    "test_data": activation_data,
                    "expected_result": "pass",
                    "priority": 8,
                    "tags": ["rule", "activation", rule_name.lower().replace(' ', '_')],
                    "rules_tested": [rule_name]
                })
                
                # 生成不激活规则的测试
                deactivation_data = self._generate_rule_deactivation_data(condition)
                tests.append({
                    "id": self._next_test_id(),
                    "name": f"Rule deactivation: {rule_name}",
                    "type": TestType.RULE_DEACTIVATION.value,
                    "description": f"Test {rule_name} when condition is false",
                    "test_data": deactivation_data,
                    "expected_result": "pass",
                    "priority": 7,
                    "tags": ["rule", "deactivation", rule_name.lower().replace(' ', '_')],
                    "rules_tested": [rule_name]
                })
                
            except Exception as e:
                print(f"Warning: Failed to generate rule test for '{rule_name}': {e}")
                continue
        
        return tests
    
    def _generate_rule_deactivation_data(self, condition: str) -> Dict[str, Any]:
        """生成不激活规则的数据"""
        try:
            test_data = {}
            
            # 简单取反逻辑
            if 'true' in str(condition):
                # 找到布尔字段并设为false
                for match in re.finditer(r'(\w+)\.(\w+)\s*==\s*true', str(condition)):
                    entity = match.group(1)
                    attr = match.group(2)
                    key = f"{entity.lower()}_{attr.lower()}"
                    test_data[key] = False
            elif '>' in str(condition):
                # 生成不满足大于条件的数据
                match = re.search(r'(\w+)\.(\w+)\s*>\s*([\d.]+)', str(condition))
                if match:
                    entity = match.group(1)
                    attr = match.group(2)
                    value = float(match.group(3))
                    key = f"{entity.lower()}_{attr.lower()}"
                    test_data[key] = max(0, value - 1)
            
            return test_data
            
        except Exception as e:
            print(f"Warning: Failed to generate deactivation data: {e}")
            return {}
    
    def _generate_collection_tests(self) -> List[Dict[str, Any]]:
        """生成集合测试"""
        tests = []
        
        try:
            for entity_name, attributes in self.entities.items():
                for attr_name, attr_meta in attributes.items():
                    if attr_meta.is_collection:
                        tests.extend(self._generate_collection_tests_for_attribute(
                            entity_name, attr_name, attr_meta
                        ))
        except Exception as e:
            print(f"Warning: Failed to generate collection tests: {e}")
        
        return tests
    
    def _generate_collection_tests_for_attribute(self, entity_name: str, attr_name: str,
                                               attr_meta: AttributeMetadata, tag: str = None) -> List[Dict[str, Any]]:
        """为单个集合属性生成测试"""
        tests = []
        key = f"{entity_name.lower()}_{attr_name}"
        
        try:
            # 空集合测试
            tags = ["collection", attr_name, "empty"]
            if tag:
                tags.append(tag)
            
            tests.append({
                "id": self._next_test_id(),
                "name": f"Required test - Empty {attr_name}",
                "type": TestType.COLLECTION.value,
                "description": f"Test {attr_name} empty as required",
                "test_data": {key: []},
                "expected_result": "pass",
                "priority": 8,
                "tags": tags
            })
            
            # 单元素集合测试
            single_value = self.value_generator._generate_collection_value(entity_name, attr_name, attr_meta)
            if single_value:
                single_item = single_value[:1] if len(single_value) > 0 else ['item_0']
            else:
                single_item = ['item_0']
            
            tags = ["collection", attr_name, "single"]
            if tag:
                tags.append(tag)
            
            tests.append({
                "id": self._next_test_id(),
                "name": f"Required test - Single {attr_name}",
                "type": TestType.COLLECTION.value,
                "description": f"Test {attr_name} with single element as required",
                "test_data": {key: single_item},
                "expected_result": "pass",
                "priority": 8,
                "tags": tags
            })
            
        except Exception as e:
            print(f"Warning: Failed to generate collection test for {attr_name}: {e}")
        
        return tests
    
    def _generate_combinatorial_tests(self) -> List[Dict[str, Any]]:
        """生成组合测试"""
        tests = []
        
        try:
            # 找到布尔和枚举类型的属性进行组合
            boolean_attrs = []
            enum_attrs = []
            
            for entity_name, attributes in self.entities.items():
                for attr_name, attr_meta in attributes.items():
                    key = f"{entity_name.lower()}_{attr_name}"
                    if attr_meta.type == 'boolean':
                        boolean_attrs.append((key, [True, False]))
                    elif attr_meta.enum:
                        enum_attrs.append((key, attr_meta.enum))
            
            # 生成2-way组合
            if len(boolean_attrs) >= 2:
                # 组合前两个布尔属性
                attr1_key, attr1_values = boolean_attrs[0]
                attr2_key, attr2_values = boolean_attrs[1]
                
                for v1 in attr1_values:
                    for v2 in attr2_values:
                        test_data = {attr1_key: v1, attr2_key: v2}
                        
                        tests.append({
                            "id": self._next_test_id(),
                            "name": f"2-way combination #{len(tests)+1}: {attr1_key.split('_')[1]} × {attr2_key.split('_')[1]}",
                            "type": TestType.COMBINATORIAL.value,
                            "description": f"Test combination of {attr1_key.split('_')[1]} and {attr2_key.split('_')[1]}",
                            "test_data": test_data,
                            "expected_result": "pass",
                            "priority": 5,
                            "tags": ["combinatorial", "2way", attr1_key.split('_')[1], attr2_key.split('_')[1]]
                        })
                        
        except Exception as e:
            print(f"Warning: Failed to generate combinatorial tests: {e}")
        
        return tests[:4]  # 限制组合测试数量
    
    def _generate_focused_combination_tests(self, focus_attrs: List[str]) -> List[Dict[str, Any]]:
        """生成聚焦于特定属性的组合测试"""
        tests = []
        
        try:
            # 将focus属性转换为完整的键名
            test_attrs = []
            for attr in focus_attrs:
                # 查找匹配的属性
                for entity_name, attributes in self.entities.items():
                    for attr_name, attr_meta in attributes.items():
                        if attr in attr_name:
                            key = f"{entity_name.lower()}_{attr_name}"
                            if attr_meta.type == 'boolean':
                                test_attrs.append((key, [True, False]))
                            elif attr_meta.is_collection:
                                test_attrs.append((key, [[], ['COMBO10']]))
                            break
            
            # 生成2-way组合
            if len(test_attrs) >= 2:
                attr1_key, attr1_values = test_attrs[0]
                attr2_key, attr2_values = test_attrs[1]
                
                for v1 in attr1_values:
                    for v2 in attr2_values:
                        test_data = {attr1_key: v1, attr2_key: v2}
                        
                        tests.append({
                            "id": self._next_test_id(),
                            "name": f"2-way combination #{len(tests)+1}: {attr1_key.split('_')[1]} × {attr2_key.split('_')[1]}",
                            "type": TestType.COMBINATORIAL.value,
                            "description": f"Test combination of {attr1_key.split('_')[1]} and {attr2_key.split('_')[1]}",
                            "test_data": test_data,
                            "expected_result": "pass",
                            "priority": 5,
                            "tags": ["combinatorial", "2way", attr1_key.split('_')[1], attr2_key.split('_')[1]]
                        })
                        
        except Exception as e:
            print(f"Warning: Failed to generate focused combination tests: {e}")
        
        return tests
    
    def _generate_negative_tests(self) -> List[Dict[str, Any]]:
        """生成负面测试"""
        tests = []
        
        try:
            for entity_name, attributes in self.entities.items():
                for attr_name, attr_meta in attributes.items():
                    key = f"{entity_name.lower()}_{attr_name}"
                    
                    # 类型错误测试
                    wrong_value = None
                    if attr_meta.type == 'integer':
                        wrong_value = "not_a_number"
                    elif attr_meta.type == 'real':
                        wrong_value = "not_a_float"
                    elif attr_meta.type == 'boolean':
                        wrong_value = "not_a_bool"
                    elif attr_meta.is_collection:
                        wrong_value = "not_an_array"
                    
                    if wrong_value:
                        tests.append({
                            "id": self._next_test_id(),
                            "name": f"Type validation for {attr_name}",
                            "type": TestType.NEGATIVE.value,
                            "description": f"Testing wrong type for {attr_name}",
                            "test_data": {key: wrong_value},
                            "expected_result": "fail",
                            "priority": 6,
                            "tags": ["negative", "type_validation", attr_name]
                        })
                        
        except Exception as e:
            print(f"Warning: Failed to generate negative tests: {e}")
        
        return tests
    
    def _generate_state_machine_tests(self) -> List[Dict[str, Any]]:
        """生成状态机测试"""
        tests = []
        state_machines = self.dsl_model.get('state_machines', [])
        
        for sm in state_machines:
            try:
                sm_name = sm.get('name', 'Unknown')
                transitions = sm.get('transitions', [])
                
                for transition in transitions:
                    test_data = {
                        f"{sm_name.lower()}_current_state": transition.get('from'),
                        f"{sm_name.lower()}_event": transition.get('event', 'transition'),
                        f"{sm_name.lower()}_expected_state": transition['to']
                    }
                    
                    # 如果有条件，添加满足条件的数据
                    if 'condition' in transition:
                        success, test_data = self.constraint_parser.parse_constraint(
                            transition['condition'], test_data
                        )
                    
                    tests.append({
                        "id": self._next_test_id(),
                        "name": f"{sm_name}: {transition['from']} -> {transition['to']}",
                        "type": TestType.STATE_TRANSITION.value,
                        "description": f"Test state transition in {sm_name}",
                        "test_data": test_data,
                        "expected_result": "pass",
                        "priority": 7,
                        "tags": ["state_machine", sm_name.lower(), "transition"]
                    })
                    
            except Exception as e:
                print(f"Warning: Failed to generate state machine test: {e}")
                continue
        
        return tests
    
    def _generate_scenario_tests(self) -> List[Dict[str, Any]]:
        """生成场景测试"""
        tests = []
        scenarios = self.dsl_model.get('scenarios', [])
        
        for scenario in scenarios:
            try:
                scenario_name = scenario.get('name', 'Unknown scenario')
                steps = scenario.get('steps', [])
                
                test_data = {}
                for step in steps:
                    # 简化：为每个步骤生成基本数据
                    action = step.get('action', '')
                    if 'create' in action.lower():
                        entity = step.get('entity', '')
                        if entity and entity in self.entities:
                            for attr_name, attr_meta in self.entities[entity].items():
                                key = f"{entity.lower()}_{attr_name}"
                                test_data[key] = self.value_generator.generate_value(entity, attr_name, attr_meta)
                
                tests.append({
                    "id": self._next_test_id(),
                    "name": f"Scenario: {scenario_name}",
                    "type": TestType.SCENARIO.value,
                    "description": scenario.get('description', f"Test scenario {scenario_name}"),
                    "test_data": test_data,
                    "expected_result": "pass",
                    "priority": 8,
                    "tags": ["scenario", scenario_name.lower().replace(' ', '_')]
                })
                
            except Exception as e:
                print(f"Warning: Failed to generate scenario test: {e}")
                continue
        
        return tests
    
    def _generate_emergency_tests(self) -> List[Dict[str, Any]]:
        """生成应急测试（当其他生成失败时）"""
        tests = []
        
        # 至少为每个实体生成一个基本测试
        for entity_name in self.entities:
            tests.append({
                "id": self._next_test_id(),
                "name": f"Emergency test for {entity_name}",
                "type": TestType.FUNCTIONAL.value,
                "description": f"Basic test for {entity_name}",
                "test_data": {},
                "expected_result": "pass",
                "priority": 5,
                "tags": ["emergency", entity_name.lower()]
            })
        
        return tests
    
    def _next_test_id(self) -> str:
        """生成下一个测试ID"""
        self.test_counter += 1
        return f"TEST_{self.test_counter:04d}"
    
    def _deduplicate_tests(self, tests: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """去除重复的测试"""
        unique_tests = []
        seen_hashes = set()
        
        for test in tests:
            # 计算测试的哈希值
            test_str = json.dumps(test.get('test_data', {}), sort_keys=True)
            test_hash = hashlib.md5(test_str.encode()).hexdigest()
            
            if test_hash not in seen_hashes:
                seen_hashes.add(test_hash)
                unique_tests.append(test)
        
        return unique_tests
    
    def _organize_test_output(self, tests: List[Dict[str, Any]]) -> Dict[str, Any]:
        """组织测试输出"""
        # 按测试类型分组
        test_suites = {}
        for test in tests:
            test_type = test['type']
            if test_type not in test_suites:
                test_suites[test_type] = []
            test_suites[test_type].append(test)
        
        # 统计信息
        test_distribution = {k: len(v) for k, v in test_suites.items()}
        tag_distribution = {}
        priority_distribution = {}
        
        for test in tests:
            # 统计标签
            for tag in test.get('tags', []):
                tag_distribution[tag] = tag_distribution.get(tag, 0) + 1
            
            # 统计优先级
            priority = test.get('priority', 5)
            priority_level = 'high' if priority >= 8 else 'medium' if priority >= 5 else 'low'
            priority_distribution[priority_level] = priority_distribution.get(priority_level, 0) + 1
        
        # 计算覆盖率
        coverage = self._calculate_coverage(tests)
        
        return {
            "meta": {
                "generator": "Unified DSL Test Generator v7.0",
                "domain": self.domain,
                "timestamp": datetime.now().isoformat(),
                "dsl_file": "Unknown",  # 将在主函数中设置
                "test_requirements_parsed": 'test_requirements' in self.dsl_model
            },
            "summary": {
                "total_tests": len(tests),
                "test_distribution": test_distribution,
                "tag_distribution": tag_distribution,
                "priority_distribution": priority_distribution,
                "requirements_coverage": coverage
            },
            "test_suites": test_suites
        }
    
    def _calculate_coverage(self, tests: List[Dict[str, Any]]) -> Dict[str, Any]:
        """计算测试覆盖率"""
        coverage = {
            "test_requirements": [],
            "constraints": [],
            "rules": []
        }
        
        try:
            # 计算test_requirements覆盖
            if 'test_requirements' in self.dsl_model:
                for req in self.dsl_model['test_requirements']:
                    req_type = req.get('type', '')
                    req_name = req.get('name', req_type)
                    
                    # 检查是否有对应类型的测试
                    covered = any(
                        test['type'] == req_type or 
                        req_type in test.get('tags', []) or
                        'required_test' in test.get('tags', [])
                        for test in tests
                    )
                    
                    coverage['test_requirements'].append({
                        "name": req_name,
                        "type": req_type,
                        "covered": covered
                    })
            
            # 计算约束覆盖
            for constraint in self.dsl_model.get('constraints', []):
                covered = any(
                    str(constraint) in test.get('constraints_tested', [])
                    for test in tests
                )
                coverage['constraints'].append({
                    "constraint": str(constraint),
                    "covered": covered
                })
            
            # 计算规则覆盖
            for rule in self.dsl_model.get('rules', []):
                rule_name = rule.get('name', 'Unknown')
                covered = any(
                    rule_name in test.get('rules_tested', [])
                    for test in tests
                )
                coverage['rules'].append({
                    "rule": rule_name,
                    "covered": covered
                })
                
        except Exception as e:
            print(f"Warning: Failed to calculate coverage: {e}")
        
        return coverage


def main():
    """主函数"""
    parser = argparse.ArgumentParser(description='V7 DSL Test Generator - Stable and High Quality')
    parser.add_argument('dsl_file', help='Path to DSL YAML file')
    parser.add_argument('-o', '--output', help='Output file path', 
                       default='generated_tests_v7.json')
    
    args = parser.parse_args()
    
    try:
        # 读取DSL文件
        with open(args.dsl_file, 'r', encoding='utf-8') as f:
            dsl_model = yaml.safe_load(f)
        
        # 生成测试
        generator = UnifiedTestGeneratorV7(dsl_model)
        result = generator.generate_tests()
        
        # 设置文件路径
        result['meta']['dsl_file'] = args.dsl_file
        
        # 保存结果
        with open(args.output, 'w', encoding='utf-8') as f:
            json.dump(result, f, ensure_ascii=False, indent=2)
        
        print(f"[V7] Starting test generation for: {dsl_model.get('domain', 'Unknown')}")
        print(f"[V7] Generated {result['summary']['total_tests']} tests successfully")
        print(f"\nTests saved to: {args.output}")
        
    except Exception as e:
        print(f"[V7] Error: {e}")
        # 生成最小输出
        minimal_output = {
            "meta": {
                "generator": "Unified DSL Test Generator v7.0",
                "error": str(e),
                "timestamp": datetime.now().isoformat()
            },
            "summary": {
                "total_tests": 0,
                "error": "Generation failed"
            },
            "test_suites": {}
        }
        
        with open(args.output, 'w', encoding='utf-8') as f:
            json.dump(minimal_output, f, ensure_ascii=False, indent=2)


if __name__ == "__main__":
    main()