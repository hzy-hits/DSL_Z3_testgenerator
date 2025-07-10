#!/usr/bin/env python3
"""
统一的 DSL 测试生成器 V6 - 高级约束和完整覆盖
基于 V5 的改进：
1. 完整的约束解析器（跨字段、时间、条件）
2. 改进的测试需求检测
3. 增强的业务规则理解
4. 更智能的测试生成策略
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


class AdvancedBusinessValueGeneratorV6:
    """V6增强的业务感知值生成器"""
    
    def __init__(self, domain: str):
        self.domain = domain
        self.id_counters = {
            'product': 1001,
            'user': 1,
            'order': 10001,
            'student': 2024001,
            'course': 101,
            'transaction': 100001
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
                'subjects': ['语文', '数学', '英语', '物理', '化学', '历史'],
                'semesters': ['2024春季', '2024秋季', '2025春季']
            }
        }
    
    def generate_value(self, entity_name: str, attr_name: str, attr_meta: AttributeMetadata) -> Any:
        """生成符合业务规则的值"""
        # 处理ID类型
        if 'id' in attr_name.lower():
            return self._generate_id(entity_name, attr_name)
        
        # 处理价格/成本
        if 'price' in attr_name or 'cost' in attr_name:
            return self._generate_price(entity_name, attr_name)
        
        # 处理日期/时间
        if attr_meta.is_temporal:
            return self._generate_temporal_value(entity_name, attr_name, attr_meta)
        
        # 处理状态/枚举
        if 'status' in attr_name or 'state' in attr_name:
            return self._generate_status(entity_name, attr_name)
        
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
        
        return None
    
    def _generate_id(self, entity_name: str, attr_name: str) -> int:
        """生成连续的ID"""
        # 确定ID类型
        id_type = 'product'
        for key in self.id_counters:
            if key in entity_name.lower() or key in attr_name.lower():
                id_type = key
                break
        
        current_id = self.id_counters[id_type]
        self.id_counters[id_type] += 1
        return current_id
    
    def _generate_price(self, entity_name: str, attr_name: str) -> float:
        """生成合理的价格"""
        domain_rules = self.business_patterns.get(self.domain, {})
        
        # 处理成本（价格的60%）
        if 'cost' in attr_name:
            price_range = domain_rules.get('price_range', (1.0, 100.0))
            base_price = random.uniform(price_range[0], price_range[1])
            cost_ratio = domain_rules.get('cost_ratio', 0.6)
            return round(base_price * cost_ratio, 2)
        
        # 生成价格
        if 'typical_prices' in domain_rules:
            if random.random() < 0.7:  # 70%使用典型价格
                return random.choice(domain_rules['typical_prices'])
        
        price_range = domain_rules.get('price_range', (1.0, 100.0))
        return round(random.uniform(price_range[0], price_range[1]), 2)
    
    def _generate_temporal_value(self, entity_name: str, attr_name: str, attr_meta: AttributeMetadata) -> str:
        """生成时间值"""
        base_date = datetime.now()
        
        # 根据属性名调整日期
        if 'order_date' in attr_name or 'created' in attr_name:
            # 订单日期在过去30天内
            days_ago = random.randint(1, 30)
            result_date = base_date - timedelta(days=days_ago)
        elif 'shipping_date' in attr_name or 'shipped' in attr_name:
            # 发货日期在订单后1-3天
            days_after = random.randint(1, 3)
            result_date = base_date - timedelta(days=25) + timedelta(days=days_after)
        elif 'delivery_date' in attr_name or 'delivered' in attr_name:
            # 配送日期在发货后3-7天
            days_after = random.randint(5, 10)
            result_date = base_date - timedelta(days=20) + timedelta(days=days_after)
        else:
            # 默认：随机过去60天
            days_ago = random.randint(0, 60)
            result_date = base_date - timedelta(days=days_ago)
        
        # 根据格式返回
        if attr_meta.format == 'date':
            return result_date.strftime('%Y-%m-%d')
        elif attr_meta.format == 'datetime':
            return result_date.strftime('%Y-%m-%d %H:%M:%S')
        else:
            return result_date.isoformat()
    
    def _generate_status(self, entity_name: str, attr_name: str) -> str:
        """生成状态值"""
        domain_rules = self.business_patterns.get(self.domain, {})
        
        # 查找匹配的状态列表
        for key in ['order_statuses', 'user_statuses', 'statuses']:
            if key in domain_rules:
                return random.choice(domain_rules[key])
        
        # 默认状态
        return random.choice(['active', 'inactive', 'pending'])
    
    def _generate_collection_value(self, entity_name: str, attr_name: str, attr_meta: AttributeMetadata) -> List[Any]:
        """生成集合值"""
        # 确定集合大小
        min_size = attr_meta.min_size or 0
        max_size = attr_meta.max_size or 5
        size = random.randint(min_size, min(max_size, 8))
        
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
        
        if element_type == 'integer':
            # 生成连续的ID序列
            start_id = self.id_counters.get('product', 1001)
            result = list(range(start_id, start_id + size))
            self.id_counters['product'] = start_id + size
            return result
        
        if element_type == 'string':
            return [f"item_{i}" for i in range(size)]
        
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
        
        # 默认
        return f"{attr_name}_value_{random.randint(1, 100)}"
    
    def _generate_numeric_value(self, attr_meta: AttributeMetadata) -> Union[int, float]:
        """生成数值"""
        min_val = attr_meta.min if attr_meta.min is not None else 0
        max_val = attr_meta.max if attr_meta.max is not None else 100
        
        if attr_meta.type == 'integer':
            return random.randint(int(min_val), int(max_val))
        else:
            return round(random.uniform(float(min_val), float(max_val)), 2)


class AdvancedConstraintParserV6:
    """V6完整的约束解析器"""
    
    def __init__(self, entities: Dict[str, Dict[str, AttributeMetadata]], 
                 value_generator: AdvancedBusinessValueGeneratorV6):
        self.entities = entities
        self.value_generator = value_generator
        self.z3_vars = {}
        self._init_z3_vars()
    
    def _init_z3_vars(self):
        """初始化Z3变量"""
        for entity_name, attributes in self.entities.items():
            self.z3_vars[entity_name] = {}
            for attr_name, attr_meta in attributes.items():
                var_name = f"{entity_name}_{attr_name}"
                if attr_meta.type == 'integer':
                    self.z3_vars[entity_name][attr_name] = z3.Int(var_name)
                elif attr_meta.type == 'real':
                    self.z3_vars[entity_name][attr_name] = z3.Real(var_name)
                elif attr_meta.type == 'boolean':
                    self.z3_vars[entity_name][attr_name] = z3.Bool(var_name)
                elif attr_meta.type == 'string':
                    # 用整数代表字符串的枚举值
                    self.z3_vars[entity_name][attr_name] = z3.Int(var_name)
    
    def parse_constraint(self, constraint: str, test_data: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        """解析并生成满足约束的数据"""
        # 处理布尔值约束
        if isinstance(constraint, bool):
            return True, test_data
        
        constraint = str(constraint).strip()
        
        # 处理条件约束 (A => B)
        if '=>' in constraint:
            return self._handle_conditional_constraint(constraint, test_data)
        
        # 处理跨字段约束
        if '.' in constraint and any(op in constraint for op in ['>', '<', '>=', '<=', '==']):
            return self._handle_cross_field_constraint(constraint, test_data)
        
        # 处理时间约束
        if any(date_kw in constraint for date_kw in ['date', 'time', 'Date', 'Time']):
            return self._handle_temporal_constraint(constraint, test_data)
        
        # 处理size函数
        if 'size(' in constraint:
            return self._handle_size_constraint(constraint, test_data)
        
        # 处理比较约束
        if any(op in constraint for op in ['>', '<', '>=', '<=', '==']):
            return self._handle_comparison_constraint(constraint, test_data)
        
        return True, test_data
    
    def _handle_conditional_constraint(self, constraint: str, test_data: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        """处理条件约束 A => B"""
        parts = constraint.split('=>')
        if len(parts) != 2:
            return True, test_data
        
        condition = parts[0].strip()
        consequence = parts[1].strip()
        
        # 解析条件部分
        if '==' in condition:
            field, value = condition.split('==')
            field = field.strip()
            value = value.strip().strip("'\"")
            
            # 设置条件为真的数据
            if '.' in field:
                entity, attr = field.split('.')
                key = f"{entity.lower()}_{attr.lower()}"
                test_data[key] = value
            
            # 解析结果部分
            if '!=' in consequence and 'null' in consequence:
                # 需要设置非空值
                field = consequence.split('!=')[0].strip()
                if '.' in field:
                    entity, attr = field.split('.')
                    key = f"{entity.lower()}_{attr.lower()}"
                    # 生成合适的非空值
                    if 'date' in attr.lower():
                        test_data[key] = datetime.now().strftime('%Y-%m-%d')
                    else:
                        test_data[key] = f"{attr}_value"
        
        return True, test_data
    
    def _handle_cross_field_constraint(self, constraint: str, test_data: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        """处理跨字段约束 如 Product.price > Product.cost"""
        # 提取操作符
        op = None
        for operator in ['>=', '<=', '>', '<', '==']:
            if operator in constraint:
                op = operator
                break
        
        if not op:
            return True, test_data
        
        parts = constraint.split(op)
        left = parts[0].strip()
        right = parts[1].strip()
        
        # 解析字段
        left_entity, left_attr = left.split('.')
        right_entity, right_attr = right.split('.')
        
        left_key = f"{left_entity.lower()}_{left_attr.lower()}"
        right_key = f"{right_entity.lower()}_{right_attr.lower()}"
        
        # 生成满足约束的值
        if 'price' in left_attr and 'cost' in right_attr:
            # 价格应该大于成本
            cost = round(random.uniform(10, 50), 2)
            price = round(cost * random.uniform(1.2, 2.0), 2)  # 20%-100%利润
            test_data[right_key] = cost
            test_data[left_key] = price
        elif 'date' in left_attr.lower() or 'date' in right_attr.lower():
            # 处理日期比较
            base_date = datetime.now() - timedelta(days=30)
            if op in ['>', '>=']:
                test_data[right_key] = base_date.strftime('%Y-%m-%d')
                test_data[left_key] = (base_date + timedelta(days=5)).strftime('%Y-%m-%d')
            else:
                test_data[left_key] = base_date.strftime('%Y-%m-%d')
                test_data[right_key] = (base_date + timedelta(days=5)).strftime('%Y-%m-%d')
        else:
            # 通用数值比较
            if op in ['>', '>=']:
                test_data[right_key] = 50
                test_data[left_key] = 100
            else:
                test_data[left_key] = 50
                test_data[right_key] = 100
        
        return True, test_data
    
    def _handle_temporal_constraint(self, constraint: str, test_data: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        """处理时间约束"""
        # 提取操作符和字段
        op = None
        for operator in ['>=', '<=', '>', '<', '==']:
            if operator in constraint:
                op = operator
                break
        
        if not op:
            return True, test_data
        
        parts = constraint.split(op)
        left = parts[0].strip()
        right = parts[1].strip()
        
        # 处理字段名
        if '.' in left:
            entity, attr = left.split('.')
            left_key = f"{entity.lower()}_{attr.lower()}"
        else:
            left_key = left.lower()
        
        if '.' in right:
            entity, attr = right.split('.')
            right_key = f"{entity.lower()}_{attr.lower()}"
        else:
            right_key = right.lower()
        
        # 生成满足约束的日期
        base_date = datetime.now() - timedelta(days=30)
        
        if 'order' in left_key and 'shipping' in right_key:
            # 订单日期 < 发货日期
            test_data[left_key] = base_date.strftime('%Y-%m-%d')
            test_data[right_key] = (base_date + timedelta(days=3)).strftime('%Y-%m-%d')
        elif 'shipping' in left_key and 'delivery' in right_key:
            # 发货日期 < 配送日期
            test_data[left_key] = base_date.strftime('%Y-%m-%d')
            test_data[right_key] = (base_date + timedelta(days=7)).strftime('%Y-%m-%d')
        else:
            # 通用处理
            if op in ['>', '>=']:
                test_data[right_key] = base_date.strftime('%Y-%m-%d')
                test_data[left_key] = (base_date + timedelta(days=5)).strftime('%Y-%m-%d')
            else:
                test_data[left_key] = base_date.strftime('%Y-%m-%d')
                test_data[right_key] = (base_date + timedelta(days=5)).strftime('%Y-%m-%d')
        
        return True, test_data
    
    def _handle_size_constraint(self, constraint: str, test_data: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        """处理size约束"""
        # 提取size函数的参数
        match = re.search(r'size\(([^)]+)\)', constraint)
        if not match:
            return True, test_data
        
        field = match.group(1).strip()
        
        # 提取操作符和值
        remaining = constraint[match.end():].strip()
        op = None
        for operator in ['>=', '<=', '>', '<', '==']:
            if remaining.startswith(operator):
                op = operator
                value = int(remaining[len(operator):].strip())
                break
        
        if not op:
            return True, test_data
        
        # 生成满足约束的集合
        if '.' in field:
            entity, attr = field.split('.')
            key = f"{entity.lower()}_{attr.lower()}"
        else:
            key = field.lower()
        
        # 确定集合大小
        if op == '>=':
            size = value
        elif op == '>':
            size = value + 1
        elif op == '<=':
            size = value
        elif op == '<':
            size = max(0, value - 1)
        else:  # ==
            size = value
        
        # 生成集合数据
        if 'categories' in key:
            domain_rules = self.value_generator.business_patterns.get(self.value_generator.domain, {})
            available = domain_rules.get('categories', ['cat1', 'cat2', 'cat3'])
            test_data[key] = random.sample(available, min(size, len(available)))
        elif 'items' in key or 'ids' in key:
            start_id = self.value_generator.id_counters.get('product', 1001)
            test_data[key] = list(range(start_id, start_id + size))
            self.value_generator.id_counters['product'] = start_id + size
        else:
            test_data[key] = [f"item_{i}" for i in range(size)]
        
        return True, test_data
    
    def _handle_comparison_constraint(self, constraint: str, test_data: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        """处理基本比较约束"""
        # 提取操作符
        op = None
        for operator in ['>=', '<=', '>', '<', '==']:
            if operator in constraint:
                op = operator
                break
        
        if not op:
            return True, test_data
        
        parts = constraint.split(op)
        field = parts[0].strip()
        value = parts[1].strip()
        
        # 处理字段名
        if '.' in field:
            entity, attr = field.split('.')
            key = f"{entity.lower()}_{attr.lower()}"
        else:
            key = field.lower()
        
        # 解析值
        try:
            if '.' in value:
                num_value = float(value)
            else:
                num_value = int(value)
        except:
            return True, test_data
        
        # 生成满足约束的值
        if op == '>':
            test_data[key] = num_value + random.uniform(0.01, 10)
        elif op == '>=':
            test_data[key] = num_value + random.uniform(0, 10)
        elif op == '<':
            test_data[key] = num_value - random.uniform(0.01, 10)
        elif op == '<=':
            test_data[key] = num_value - random.uniform(0, 10)
        else:  # ==
            test_data[key] = num_value
        
        # 确保值在合理范围内
        if key in test_data:
            if isinstance(test_data[key], float):
                test_data[key] = round(max(0, test_data[key]), 2)
            else:
                test_data[key] = max(0, int(test_data[key]))
        
        return True, test_data


class UnifiedTestGeneratorV6:
    """V6统一测试生成器主类"""
    
    def __init__(self, dsl_model: Dict[str, Any]):
        self.dsl_model = dsl_model
        self.domain = dsl_model.get('domain', 'Unknown')
        self.entities = self._parse_entities()
        self.value_generator = AdvancedBusinessValueGeneratorV6(self.domain)
        self.constraint_parser = AdvancedConstraintParserV6(self.entities, self.value_generator)
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
        
        # 去重和组织
        unique_tests = self._deduplicate_tests(all_tests)
        return self._organize_test_output(unique_tests)
    
    def _generate_required_tests(self) -> List[Dict[str, Any]]:
        """生成test_requirements中指定的测试"""
        tests = []
        test_reqs = self.dsl_model.get('test_requirements', [])
        
        for req in test_reqs:
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
                    # 使用focus字段生成特定属性的组合
                    focus_attrs = req.get('focus', [])
                    tests.extend(self._generate_focused_combination_tests(focus_attrs))
                elif 'combinations' in req and isinstance(req['combinations'], list):
                    for combo in req['combinations']:
                        tests.extend(self._generate_specific_combination_tests(combo))
                else:
                    tests.extend(self._generate_combinatorial_tests())
        
        return tests
    
    def _generate_default_tests(self) -> List[Dict[str, Any]]:
        """为没有test_requirements的文件生成默认测试"""
        tests = []
        
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
        
        return tests
    
    def _generate_functional_tests(self) -> List[Dict[str, Any]]:
        """生成功能测试"""
        tests = []
        
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
        
        return tests
    
    def _generate_constraint_tests(self) -> List[Dict[str, Any]]:
        """生成约束测试"""
        tests = []
        constraints = self.dsl_model.get('constraints', [])
        
        for constraint in constraints:
            # 生成满足约束的测试
            test_data = {}
            success, test_data = self.constraint_parser.parse_constraint(constraint, test_data)
            
            if success:
                tests.append({
                    "id": self._next_test_id(),
                    "name": f"Constraint satisfaction: {constraint}",
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
                    "name": f"Constraint violation: {constraint}",
                    "type": TestType.CONSTRAINT_VIOLATION.value,
                    "description": "Test constraint is violated",
                    "test_data": violation_data,
                    "expected_result": "fail",
                    "priority": 7,
                    "tags": ["constraint", "violation", "negative"],
                    "constraints_tested": [constraint]
                })
        
        return tests
    
    def _generate_constraint_violation(self, constraint: str) -> Optional[Dict[str, Any]]:
        """生成违反约束的测试数据"""
        test_data = {}
        
        # 处理比较约束的违反
        if '>=' in constraint:
            parts = constraint.split('>=')
            field = parts[0].strip()
            value = float(parts[1].strip())
            key = self._field_to_key(field)
            test_data[key] = value - 1  # 小于最小值
        elif '>' in constraint:
            parts = constraint.split('>')
            field = parts[0].strip()
            value = float(parts[1].strip())
            key = self._field_to_key(field)
            test_data[key] = value  # 等于而不是大于
        elif '<=' in constraint:
            parts = constraint.split('<=')
            field = parts[0].strip()
            value = float(parts[1].strip())
            key = self._field_to_key(field)
            test_data[key] = value + 1  # 大于最大值
        elif 'size(' in constraint and '<=' in constraint:
            # 违反size约束
            match = re.search(r'size\(([^)]+)\)\s*<=\s*(\d+)', constraint)
            if match:
                field = match.group(1)
                max_size = int(match.group(2))
                key = self._field_to_key(field)
                # 生成超过最大大小的集合
                test_data[key] = [f"item_{i}" for i in range(max_size + 1)]
        
        return test_data if test_data else None
    
    def _field_to_key(self, field: str) -> str:
        """将字段名转换为测试数据的键"""
        if '.' in field:
            entity, attr = field.split('.')
            return f"{entity.lower()}_{attr.lower()}"
        return field.lower()
    
    def _generate_boundary_tests(self) -> List[Dict[str, Any]]:
        """生成边界测试"""
        tests = []
        
        for entity_name, attributes in self.entities.items():
            for attr_name, attr_meta in attributes.items():
                if attr_meta.is_numeric:
                    tests.extend(self._generate_boundary_tests_for_attribute(
                        entity_name, attr_name, attr_meta
                    ))
        
        return tests
    
    def _generate_boundary_tests_for_attribute(self, entity_name: str, attr_name: str, 
                                             attr_meta: AttributeMetadata, tag: str = None) -> List[Dict[str, Any]]:
        """为单个属性生成边界测试"""
        tests = []
        key = f"{entity_name.lower()}_{attr_name}"
        
        # 最小值测试
        if attr_meta.min is not None:
            test_data = {key: attr_meta.min}
            tags = ["boundary", attr_name, "min"]
            if tag:
                tags.append(tag)
            
            tests.append({
                "id": self._next_test_id(),
                "name": f"Boundary test: {attr_name} = {attr_meta.min}",
                "type": TestType.BOUNDARY.value,
                "description": f"Test minimum value for {attr_name}",
                "test_data": test_data,
                "expected_result": "pass",
                "priority": 7,
                "tags": tags
            })
            
            # 小于最小值
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
        
        return tests
    
    def _generate_rule_tests(self) -> List[Dict[str, Any]]:
        """生成规则测试"""
        tests = []
        rules = self.dsl_model.get('rules', [])
        
        for rule in rules:
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
        
        return tests
    
    def _generate_rule_deactivation_data(self, condition: str) -> Dict[str, Any]:
        """生成不激活规则的数据"""
        test_data = {}
        
        # 简单取反逻辑
        if 'true' in condition:
            # 找到布尔字段并设为false
            for match in re.finditer(r'(\w+)\.(\w+)\s*==\s*true', condition):
                entity = match.group(1)
                attr = match.group(2)
                key = f"{entity.lower()}_{attr.lower()}"
                test_data[key] = False
        elif '>' in condition:
            # 生成不满足大于条件的数据
            match = re.search(r'(\w+)\.(\w+)\s*>\s*([\d.]+)', condition)
            if match:
                entity = match.group(1)
                attr = match.group(2)
                value = float(match.group(3))
                key = f"{entity.lower()}_{attr.lower()}"
                test_data[key] = value - 1
        
        return test_data
    
    def _generate_collection_tests(self) -> List[Dict[str, Any]]:
        """生成集合测试"""
        tests = []
        
        for entity_name, attributes in self.entities.items():
            for attr_name, attr_meta in attributes.items():
                if attr_meta.is_collection:
                    tests.extend(self._generate_collection_tests_for_attribute(
                        entity_name, attr_name, attr_meta
                    ))
        
        return tests
    
    def _generate_collection_tests_for_attribute(self, entity_name: str, attr_name: str,
                                               attr_meta: AttributeMetadata, tag: str = None) -> List[Dict[str, Any]]:
        """为单个集合属性生成测试"""
        tests = []
        key = f"{entity_name.lower()}_{attr_name}"
        
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
        
        return tests
    
    def _generate_combinatorial_tests(self) -> List[Dict[str, Any]]:
        """生成组合测试"""
        tests = []
        
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
        
        return tests[:4]  # 限制组合测试数量
    
    def _generate_focused_combination_tests(self, focus_attrs: List[str]) -> List[Dict[str, Any]]:
        """生成聚焦于特定属性的组合测试"""
        tests = []
        
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
        
        return tests
    
    def _generate_specific_combination_tests(self, combo_spec: Dict[str, Any]) -> List[Dict[str, Any]]:
        """生成特定的组合测试"""
        tests = []
        attributes = combo_spec.get('attributes', [])
        
        if len(attributes) >= 2:
            # 简化：只测试指定属性的true/false或有/无组合
            test_data = {}
            for attr in attributes:
                if 'premium' in attr or 'member' in attr:
                    test_data[attr.lower()] = True
                elif 'discount' in attr or 'code' in attr:
                    test_data[attr.lower()] = ['COMBO10']
            
            tests.append({
                "id": self._next_test_id(),
                "name": f"Required combination test: {' + '.join(attributes)}",
                "type": TestType.COMBINATORIAL.value,
                "description": f"Test specific combination as required",
                "test_data": test_data,
                "expected_result": "pass",
                "priority": 8,
                "tags": ["combinatorial", "required_test"] + [a.lower() for a in attributes]
            })
        
        return tests
    
    def _generate_negative_tests(self) -> List[Dict[str, Any]]:
        """生成负面测试"""
        tests = []
        
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
        
        return tests
    
    def _generate_state_machine_tests(self) -> List[Dict[str, Any]]:
        """生成状态机测试"""
        tests = []
        state_machines = self.dsl_model.get('state_machines', [])
        
        for sm in state_machines:
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
        
        return tests
    
    def _generate_scenario_tests(self) -> List[Dict[str, Any]]:
        """生成场景测试"""
        tests = []
        scenarios = self.dsl_model.get('scenarios', [])
        
        for scenario in scenarios:
            scenario_name = scenario.get('name', 'Unknown scenario')
            steps = scenario.get('steps', [])
            
            test_data = {}
            for step in steps:
                # 简化：为每个步骤生成基本数据
                action = step.get('action', '')
                if 'create' in action.lower():
                    entity = step.get('entity', '')
                    if entity:
                        for attr_name, attr_meta in self.entities.get(entity, {}).items():
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
            test_str = json.dumps(test['test_data'], sort_keys=True)
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
                "generator": "Unified DSL Test Generator v6.0",
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
                constraint in test.get('constraints_tested', [])
                for test in tests
            )
            coverage['constraints'].append({
                "constraint": constraint,
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
        
        return coverage


def main():
    """主函数"""
    parser = argparse.ArgumentParser(description='V6 DSL Test Generator')
    parser.add_argument('dsl_file', help='Path to DSL YAML file')
    parser.add_argument('-o', '--output', help='Output file path', 
                       default='generated_tests_v6.json')
    
    args = parser.parse_args()
    
    # 读取DSL文件
    with open(args.dsl_file, 'r', encoding='utf-8') as f:
        dsl_model = yaml.safe_load(f)
    
    # 生成测试
    generator = UnifiedTestGeneratorV6(dsl_model)
    result = generator.generate_tests()
    
    # 设置文件路径
    result['meta']['dsl_file'] = args.dsl_file
    
    # 保存结果
    with open(args.output, 'w', encoding='utf-8') as f:
        json.dump(result, f, ensure_ascii=False, indent=2)
    
    print(f"[V6] Starting test generation for: {dsl_model.get('domain', 'Unknown')}")
    print(f"[V6] Generated {result['summary']['total_tests']} tests")
    print(f"\nTests saved to: {args.output}")


if __name__ == "__main__":
    main()