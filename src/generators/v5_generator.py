#!/usr/bin/env python3
"""
统一的 DSL 测试生成器 V5 - 修复版
基于 V4 的改进：
1. 修复集合类型生成（确保生成数组而非字符串）
2. 增强约束解析（支持复杂约束和条件约束）
3. 改进数据质量（合理的价格、连续的ID）
4. 修复覆盖率计算
5. 为无test_requirements的文件生成默认测试
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
from datetime import datetime, timedelta
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


class BusinessAwareValueGeneratorV5:
    """增强的业务感知值生成器"""
    
    def __init__(self, domain: str):
        self.domain = domain
        self.product_id_counter = 1001  # 产品ID从1001开始
        self.user_id_counter = 1
        self.order_id_counter = 10001
        self._init_business_rules()
    
    def _init_business_rules(self):
        """初始化业务规则"""
        self.business_patterns = {
            'E-commerce Shopping Cart': {
                'price_range': (0.99, 299.99),
                'discount_codes': ['SAVE10', 'BULK15', 'VIP20', 'WELCOME5', 'MEMBER10', 'SUMMER25'],
                'categories': ['electronics', 'books', 'clothing', 'home', 'sports', 'toys', 'beauty', 'food'],
            },
            'Advanced E-commerce Platform': {
                'price_range': (9.99, 999.99),
                'cost_range': (5.00, 500.00),
                'warehouse_locations': ['US-EAST', 'US-WEST', 'EU-CENTRAL', 'ASIA-PACIFIC'],
            },
            'User Account Management System': {
                'email_pattern': lambda i: f"user{i}@example.com",
                'balance_range': (0, 10000),
            },
            'Order Processing System': {
                'order_amount_range': (10, 5000),
                'status_values': ['pending', 'processing', 'shipped', 'delivered'],
            }
        }
    
    def generate_business_value(self, entity_name: str, attr_name: str, attr_meta: AttributeMetadata) -> Any:
        """生成符合业务逻辑的值"""
        # 处理集合类型
        if attr_meta.is_collection:
            return self._generate_collection_value(entity_name, attr_name, attr_meta)
        
        # 处理ID
        if attr_name == 'id' or attr_name.endswith('_id'):
            return self._generate_id(entity_name, attr_name)
        
        # 处理价格
        if any(keyword in attr_name for keyword in ['price', 'amount', 'cost']):
            return self._generate_price(entity_name, attr_name)
        
        # 处理邮箱
        if 'email' in attr_name:
            return f"test{self.user_id_counter}@example.com"
        
        # 处理折扣码
        if 'discount' in attr_name and 'code' in attr_name:
            domain_rules = self.business_patterns.get(self.domain, {})
            codes = domain_rules.get('discount_codes', ['DISCOUNT10'])
            return random.choice(codes)
        
        # 处理时间戳
        if attr_meta.is_temporal or 'timestamp' in attr_name:
            base_time = int(datetime.now().timestamp())
            if 'created' in attr_name:
                return base_time - random.randint(86400, 864000)  # 1-10天前
            elif 'shipping' in attr_name:
                return base_time + random.randint(86400, 259200)  # 1-3天后
            else:
                return base_time
        
        # 处理布尔值
        if attr_meta.type == 'boolean':
            # 根据属性名智能选择
            if 'is_active' in attr_name or 'is_verified' in attr_name:
                return random.choice([True, True, False])  # 66%概率为True
            return random.choice([True, False])
        
        # 处理枚举
        if attr_meta.enum:
            return random.choice(attr_meta.enum)
        
        # 使用默认值生成
        return self._generate_default_value(attr_meta)
    
    def _generate_collection_value(self, entity_name: str, attr_name: str, attr_meta: AttributeMetadata) -> List[Any]:
        """生成集合值"""
        # 确定集合大小
        if 'categories' in attr_name:
            size = random.randint(1, 3)
        elif 'items' in attr_name:
            size = random.randint(1, 10)
        elif 'permissions' in attr_name or 'roles' in attr_name:
            size = random.randint(1, 5)
        else:
            min_size = attr_meta.min_size or 0
            max_size = min(attr_meta.max_size or 10, 10)
            size = random.randint(min_size, max_size)
        
        # 生成元素
        element_type = attr_meta.element_type
        
        if element_type == 'integer':
            if 'id' in attr_name or 'items' in attr_name:
                # 生成连续的ID
                start = self.product_id_counter
                self.product_id_counter += size
                return list(range(start, start + size))
            else:
                return [random.randint(1, 100) for _ in range(size)]
                
        elif element_type == 'string':
            if 'categories' in attr_name:
                domain_rules = self.business_patterns.get(self.domain, {})
                available = domain_rules.get('categories', ['category1', 'category2', 'category3'])
                return random.sample(available, min(size, len(available)))
            elif 'discount_codes' in attr_name:
                domain_rules = self.business_patterns.get(self.domain, {})
                available = domain_rules.get('discount_codes', ['CODE1', 'CODE2'])
                return random.sample(available, min(size, len(available)))
            else:
                return [f"{attr_name}_{i}" for i in range(size)]
        
        return []
    
    def _generate_id(self, entity_name: str, attr_name: str) -> int:
        """生成ID值"""
        if 'product' in entity_name.lower():
            id_val = self.product_id_counter
            self.product_id_counter += 1
            return id_val
        elif 'user' in entity_name.lower() or 'customer' in attr_name:
            id_val = self.user_id_counter
            self.user_id_counter += 1
            return id_val
        elif 'order' in entity_name.lower():
            id_val = self.order_id_counter
            self.order_id_counter += 1
            return id_val
        else:
            return random.randint(1, 1000)
    
    def _generate_price(self, entity_name: str, attr_name: str) -> float:
        """生成价格值"""
        domain_rules = self.business_patterns.get(self.domain, {})
        
        if 'cost' in attr_name:
            price_range = domain_rules.get('cost_range', (1.0, 100.0))
        else:
            price_range = domain_rules.get('price_range', (0.99, 199.99))
        
        # 生成合理的价格
        price = random.uniform(price_range[0], price_range[1])
        
        # 常见价格模式
        if random.random() < 0.3:  # 30%概率使用.99结尾
            return float(int(price)) + 0.99
        else:
            return round(price, 2)
    
    def _generate_default_value(self, attr_meta: AttributeMetadata) -> Any:
        """生成默认值"""
        if attr_meta.type == 'integer':
            if attr_meta.min is not None:
                return attr_meta.min
            return 1
        elif attr_meta.type == 'real':
            if attr_meta.min is not None:
                return float(attr_meta.min)
            return 0.0
        elif attr_meta.type == 'string':
            return "test_value"
        elif attr_meta.type == 'boolean':
            return False
        return None


class ComplexConstraintParser:
    """复杂约束解析器"""
    
    def __init__(self):
        self.operators = {
            '=>': 'implies',
            '->': 'implies',
            '||': 'or',
            '&&': 'and',
            '==': 'eq',
            '!=': 'ne',
            '>=': 'ge',
            '<=': 'le',
            '>': 'gt',
            '<': 'lt'
        }
    
    def parse_constraint(self, constraint: str, test_data: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        """
        解析并生成满足约束的数据
        返回：(是否成功解析, 生成的数据)
        """
        # 处理布尔值约束
        if isinstance(constraint, bool):
            return True, test_data
        
        # 确保constraint是字符串
        constraint = str(constraint)
        
        # 处理条件约束 (A => B)
        if '=>' in constraint or '->' in constraint:
            return self._handle_conditional_constraint(constraint, test_data)
        
        # 处理比较约束 (A > B)
        if any(op in constraint for op in ['>', '<', '>=', '<=', '==']):
            return self._handle_comparison_constraint(constraint, test_data)
        
        # 处理size函数
        if 'size(' in constraint:
            return self._handle_size_constraint(constraint, test_data)
        
        # 处理逻辑约束 (A and B)
        if ' and ' in constraint or ' or ' in constraint:
            return self._handle_logical_constraint(constraint, test_data)
        
        return False, test_data
    
    def _handle_conditional_constraint(self, constraint: str, test_data: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        """处理条件约束 A => B"""
        # 分割条件和结果
        parts = re.split('=>|->',

 constraint)
        if len(parts) != 2:
            return False, test_data
        
        condition = parts[0].strip()
        implication = parts[1].strip()
        
        # 示例：Order.status == 'delivered' => Order.delivery_date != null
        if "status == 'delivered'" in condition:
            test_data['order_status'] = 'delivered'
            test_data['order_delivery_date'] = int(datetime.now().timestamp())
        elif "status == 'shipped'" in condition:
            test_data['order_status'] = 'shipped'
            test_data['order_shipping_date'] = int(datetime.now().timestamp())
        
        return True, test_data
    
    def _handle_comparison_constraint(self, constraint: str, test_data: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        """处理比较约束"""
        # 示例：Product.price > Product.cost
        if 'price' in constraint and 'cost' in constraint and '>' in constraint:
            cost = random.uniform(10, 100)
            price = cost * random.uniform(1.2, 2.0)  # 价格是成本的1.2-2倍
            test_data['product_cost'] = round(cost, 2)
            test_data['product_price'] = round(price, 2)
            return True, test_data
        
        # 示例：order_amount > 0
        match = re.match(r'(\w+)\s*([><=]+)\s*([\d.]+)', constraint)
        if match:
            field, op, value = match.groups()
            value = float(value)
            
            if op == '>':
                test_data[field] = value + random.uniform(10, 100)
            elif op == '>=':
                test_data[field] = value + random.uniform(0, 100)
            elif op == '<':
                test_data[field] = value - random.uniform(1, 10)
            elif op == '<=':
                test_data[field] = value - random.uniform(0, 10)
            
            return True, test_data
        
        return False, test_data
    
    def _handle_size_constraint(self, constraint: str, test_data: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        """处理size函数约束"""
        # 示例：size(Order.items) > 0
        match = re.search(r'size\(([^)]+)\)\s*([><=]+)\s*(\d+)', constraint)
        if match:
            field, op, size = match.groups()
            size = int(size)
            
            # 清理字段名
            field = field.replace('.', '_').lower()
            
            if op == '>':
                actual_size = size + random.randint(1, 5)
            elif op == '>=':
                actual_size = size + random.randint(0, 5)
            elif op == '<':
                actual_size = max(0, size - random.randint(1, 5))
            elif op == '<=':
                actual_size = max(0, size - random.randint(0, 5))
            else:
                actual_size = size
            
            # 生成对应大小的数组
            if 'items' in field:
                test_data[field] = list(range(1001, 1001 + actual_size))
            elif 'categories' in field:
                test_data[field] = [f"category_{i}" for i in range(actual_size)]
            else:
                test_data[field] = list(range(actual_size))
            
            return True, test_data
        
        return False, test_data
    
    def _handle_logical_constraint(self, constraint: str, test_data: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        """处理逻辑约束"""
        # 示例：student_grade_level >= 1 and student_grade_level <= 6
        if ' and ' in constraint:
            parts = constraint.split(' and ')
            for part in parts:
                _, test_data = self._handle_comparison_constraint(part.strip(), test_data)
        
        return True, test_data


class UnifiedDSLTestGeneratorV5:
    """统一的 DSL 测试生成器 V5"""
    
    def __init__(self, dsl_file: str, config: Dict[str, Any] = None):
        self.dsl_file = dsl_file
        self.config = config or {}
        
        # 加载 DSL
        with open(dsl_file, 'r', encoding='utf-8') as f:
            self.dsl_model = yaml.safe_load(f)
        
        # 初始化组件
        self.domain = self.dsl_model.get('domain', 'Unknown')
        self.business_generator = BusinessAwareValueGeneratorV5(self.domain)
        self.constraint_parser = ComplexConstraintParser()
        
        # 解析测试需求
        self.test_requirements = self._parse_test_requirements()
        
        # 内部映射
        self.entity_map = {}
        self.attribute_map = {}
        self.test_counter = 0
        self.constraint_coverage = set()  # 跟踪已覆盖的约束
        
        # 测试分布控制
        self.test_distribution = {
            TestType.FUNCTIONAL: 0.20,
            TestType.BOUNDARY: 0.20,
            TestType.RULE_ACTIVATION: 0.10,
            TestType.RULE_DEACTIVATION: 0.10,
            TestType.CONSTRAINT_SATISFACTION: 0.10,
            TestType.CONSTRAINT_VIOLATION: 0.10,
            TestType.NEGATIVE: 0.15,
            TestType.COLLECTION: 0.05
        }
        
        # 构建映射
        self._build_internal_mappings()
    
    def _parse_test_requirements(self) -> List[Dict[str, Any]]:
        """解析测试需求"""
        requirements = []
        for req in self.dsl_model.get('test_requirements', []):
            requirements.append({
                'name': req.get('name', ''),
                'type': req.get('type', ''),
                'focus': req.get('focus', []),
                'collection_tests': req.get('collection_tests', []),
                'combinations': req.get('combinations')
            })
        return requirements
    
    def _build_internal_mappings(self):
        """构建内部映射"""
        for entity in self.dsl_model.get('entities', []):
            entity_name = entity['name']
            self.entity_map[entity_name.lower()] = entity
            
            for attr in entity.get('attributes', []):
                # 创建增强的属性元数据
                attr_meta = AttributeMetadata(
                    name=attr['name'],
                    type=attr['type'],
                    min=attr.get('min'),
                    max=attr.get('max'),
                    min_size=attr.get('min_size', 0),
                    max_size=attr.get('max_size', 50),
                    enum=attr.get('enum'),
                    pattern=attr.get('pattern'),
                    optional=attr.get('optional', False),
                    default=attr.get('default'),
                    unique=attr.get('unique', False),
                    nullable=attr.get('nullable', False),
                    description=attr.get('description'),
                    format=attr.get('format'),
                    custom_validator=attr.get('validator'),
                    dependencies=attr.get('dependencies', [])
                )
                
                attr_key = f"{entity_name.lower()}_{attr['name']}"
                self.attribute_map[attr_key] = {
                    'entity': entity,
                    'attribute': attr_meta
                }
    
    def generate_tests(self) -> Dict[str, Any]:
        """生成测试"""
        print(f"[V5] Starting test generation for: {self.domain}")
        
        all_tests = []
        
        # 1. 生成功能测试
        all_tests.extend(self._generate_functional_tests())
        
        # 2. 生成约束测试（优先级高）
        all_tests.extend(self._generate_constraint_tests())
        
        # 3. 如果有test_requirements，根据需求生成
        if self.test_requirements:
            all_tests.extend(self._generate_required_tests())
        else:
            # 没有test_requirements时，生成默认测试集
            all_tests.extend(self._generate_default_test_suite())
        
        # 4. 生成规则测试
        all_tests.extend(self._generate_rule_tests())
        
        # 5. 生成边界测试
        all_tests.extend(self._generate_boundary_tests())
        
        # 6. 生成负面测试
        all_tests.extend(self._generate_negative_tests())
        
        # 7. 生成状态机测试
        if 'state_machines' in self.dsl_model:
            all_tests.extend(self._generate_state_machine_tests())
        
        # 8. 去重和优化
        optimized_tests = self._optimize_test_suite(all_tests)
        
        print(f"[V5] Generated {len(optimized_tests)} tests")
        
        # 格式化输出
        return self._format_output(optimized_tests)
    
    def _generate_functional_tests(self) -> List[Dict[str, Any]]:
        """生成功能测试"""
        tests = []
        
        for entity_name, entity in self.entity_map.items():
            # 测试1：基本功能测试
            test_data = self._generate_business_aware_data(entity)
            
            tests.append({
                "id": self._next_test_id(),
                "name": f"Create {entity['name']} with valid business data",
                "type": TestType.FUNCTIONAL.value,
                "description": f"Test creating {entity['name']} with realistic data",
                "test_data": test_data,
                "expected_result": "pass",
                "priority": 9,
                "tags": ["functional", entity_name, "business_data"]
            })
            
            # 测试2：完整数据测试
            complete_data = self._generate_complete_data(entity)
            tests.append({
                "id": self._next_test_id(),
                "name": f"Create {entity['name']} with all fields",
                "type": TestType.FUNCTIONAL.value,
                "description": f"Test {entity['name']} with all optional fields",
                "test_data": complete_data,
                "expected_result": "pass",
                "priority": 8,
                "tags": ["functional", entity_name, "complete"]
            })
        
        return tests
    
    def _generate_constraint_tests(self) -> List[Dict[str, Any]]:
        """生成约束测试"""
        tests = []
        
        for constraint in self.dsl_model.get('constraints', []):
            # 约束满足测试
            test_data = {}
            success, test_data = self.constraint_parser.parse_constraint(constraint, test_data)
            
            if success:
                # 补充其他必要字段
                test_data = self._complete_test_data(test_data)
                
                tests.append({
                    "id": self._next_test_id(),
                    "name": f"Constraint satisfaction: {constraint[:50]}",
                    "type": TestType.CONSTRAINT_SATISFACTION.value,
                    "description": "Test constraint is satisfied",
                    "test_data": test_data,
                    "expected_result": "pass",
                    "priority": 8,
                    "tags": ["constraint", "satisfaction"],
                    "constraints_tested": [constraint]
                })
                self.constraint_coverage.add(constraint)
            
            # 约束违反测试（针对某些约束）
            if any(op in constraint for op in ['>', '<', '>=', '<=']):
                violation_data = self._generate_constraint_violation_data(constraint)
                if violation_data:
                    tests.append({
                        "id": self._next_test_id(),
                        "name": f"Constraint violation: {constraint[:50]}",
                        "type": TestType.CONSTRAINT_VIOLATION.value,
                        "description": "Test constraint is violated",
                        "test_data": violation_data,
                        "expected_result": "fail",
                        "priority": 7,
                        "tags": ["constraint", "violation", "negative"],
                        "constraints_tested": [constraint]
                    })
        
        return tests
    
    def _generate_required_tests(self) -> List[Dict[str, Any]]:
        """根据test_requirements生成测试"""
        tests = []
        
        for req in self.test_requirements:
            if req['type'] == 'boundary':
                for attr_name in req['focus']:
                    for entity_name, entity in self.entity_map.items():
                        full_attr_key = f"{entity_name}_{attr_name}"
                        if full_attr_key in self.attribute_map:
                            attr_info = self.attribute_map[full_attr_key]
                            attr = attr_info['attribute']
                            if attr.is_numeric:
                                # 生成边界测试
                                tests.extend(self._generate_boundary_tests_for_attribute(full_attr_key, attr))
            
            elif req['type'] == 'collection':
                tests.extend(self._generate_collection_tests_for_requirement(req))
            
            elif req['type'] == 'combinatorial':
                tests.extend(self._generate_combinatorial_tests(req['focus'], req['combinations']))
        
        return tests
    
    def _generate_default_test_suite(self) -> List[Dict[str, Any]]:
        """为没有test_requirements的文件生成默认测试"""
        tests = []
        
        # 1. 为每个集合属性生成集合测试
        for attr_key, attr_info in self.attribute_map.items():
            attr = attr_info['attribute']
            if attr.is_collection:
                tests.extend(self._generate_collection_tests_for_attribute(attr_key, attr))
        
        # 2. 生成一些组合测试
        # 找出布尔和枚举属性进行组合
        boolean_attrs = []
        enum_attrs = []
        
        for attr_key, attr_info in self.attribute_map.items():
            attr = attr_info['attribute']
            if attr.type == 'boolean':
                boolean_attrs.append(attr_key)
            elif attr.enum:
                enum_attrs.append(attr_key)
        
        # 生成2-way组合
        if len(boolean_attrs) >= 2:
            tests.extend(self._generate_combinatorial_tests(boolean_attrs[:2], 2))
        
        return tests
    
    def _generate_rule_tests(self) -> List[Dict[str, Any]]:
        """生成规则测试"""
        tests = []
        
        for rule in self.dsl_model.get('rules', []):
            rule_name = rule.get('name', 'Unknown')
            condition = rule.get('condition', '')
            implies = rule.get('implies', rule.get('action', ''))
            
            # 规则激活测试
            activation_data = self._generate_rule_activation_data(condition, implies)
            if activation_data:
                tests.append({
                    "id": self._next_test_id(),
                    "name": f"Rule activation: {rule_name}",
                    "type": TestType.RULE_ACTIVATION.value,
                    "description": f"Test {rule_name} when condition is true",
                    "test_data": activation_data,
                    "expected_result": "pass",
                    "priority": 8,
                    "tags": ["rule", "activation", self._sanitize_tag(rule_name)],
                    "rules_tested": [rule_name]
                })
            
            # 规则未激活测试
            deactivation_data = self._generate_rule_deactivation_data(condition)
            if deactivation_data:
                tests.append({
                    "id": self._next_test_id(),
                    "name": f"Rule deactivation: {rule_name}",
                    "type": TestType.RULE_DEACTIVATION.value,
                    "description": f"Test {rule_name} when condition is false",
                    "test_data": deactivation_data,
                    "expected_result": "pass",
                    "priority": 7,
                    "tags": ["rule", "deactivation", self._sanitize_tag(rule_name)],
                    "rules_tested": [rule_name]
                })
        
        return tests
    
    def _generate_boundary_tests(self) -> List[Dict[str, Any]]:
        """生成边界测试"""
        tests = []
        max_tests = int(self.config.get('max_tests_per_type', 30) * 0.20)
        
        for attr_key, attr_info in self.attribute_map.items():
            attr = attr_info['attribute']
            
            if attr.is_numeric and (attr.min is not None or attr.max is not None):
                tests.extend(self._generate_boundary_tests_for_attribute(attr_key, attr))
            
            if len(tests) >= max_tests:
                break
        
        return tests[:max_tests]
    
    def _generate_negative_tests(self) -> List[Dict[str, Any]]:
        """生成负面测试"""
        tests = []
        
        # 1. 类型错误测试
        for attr_key, attr_info in self.attribute_map.items():
            attr = attr_info['attribute']
            
            # 为集合类型生成错误数据
            if attr.is_collection:
                # 测试非数组值
                tests.append({
                    "id": self._next_test_id(),
                    "name": f"Type validation for {attr_key} (not array)",
                    "type": TestType.NEGATIVE.value,
                    "description": f"Testing non-array value for collection {attr_key}",
                    "test_data": {attr_key: "not_an_array"},
                    "expected_result": "fail",
                    "priority": 6,
                    "tags": ["negative", "type_validation", attr_key]
                })
            else:
                wrong_value = self._get_wrong_type_value(attr.type)
                if wrong_value is not None:
                    tests.append({
                        "id": self._next_test_id(),
                        "name": f"Type validation for {attr_key}",
                        "type": TestType.NEGATIVE.value,
                        "description": f"Testing wrong type for {attr_key}",
                        "test_data": {attr_key: wrong_value},
                        "expected_result": "fail",
                        "priority": 6,
                        "tags": ["negative", "type_validation", attr_key]
                    })
        
        return tests
    
    def _generate_state_machine_tests(self) -> List[Dict[str, Any]]:
        """生成状态机测试"""
        tests = []
        
        for sm in self.dsl_model.get('state_machines', []):
            sm_name = sm.get('name', 'StateMachine')
            
            for transition in sm.get('transitions', []):
                test_data = {
                    f"{sm_name.lower()}_current_state": transition['from'],
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
                    "tags": ["state_machine", "transition", sm_name.lower()]
                })
        
        return tests
    
    # 辅助方法
    def _generate_business_aware_data(self, entity: Dict[str, Any]) -> Dict[str, Any]:
        """生成业务感知的测试数据"""
        test_data = {}
        entity_name = entity['name']
        
        for attr in entity.get('attributes', []):
            attr_name = attr['name']
            attr_key = f"{entity_name.lower()}_{attr_name}"
            
            if attr_key in self.attribute_map:
                attr_meta = self.attribute_map[attr_key]['attribute']
                value = self.business_generator.generate_business_value(
                    entity_name, attr_name, attr_meta
                )
                
                if value is not None:
                    test_data[attr_key] = value
        
        return test_data
    
    def _generate_complete_data(self, entity: Dict[str, Any]) -> Dict[str, Any]:
        """生成包含所有字段的完整数据"""
        test_data = self._generate_business_aware_data(entity)
        
        # 确保所有可选字段也有值
        entity_name = entity['name']
        for attr in entity.get('attributes', []):
            attr_key = f"{entity_name.lower()}_{attr['name']}"
            if attr_key not in test_data:
                if attr_key in self.attribute_map:
                    attr_meta = self.attribute_map[attr_key]['attribute']
                    test_data[attr_key] = self.business_generator.generate_business_value(
                        entity_name, attr['name'], attr_meta
                    )
        
        return test_data
    
    def _complete_test_data(self, partial_data: Dict[str, Any]) -> Dict[str, Any]:
        """补充测试数据中缺失的必要字段"""
        complete_data = partial_data.copy()
        
        # 根据已有字段推断实体类型，补充其他字段
        for key in partial_data.keys():
            parts = key.split('_')
            if len(parts) >= 2:
                entity_prefix = parts[0]
                entity = self.entity_map.get(entity_prefix)
                
                if entity:
                    # 补充该实体的其他必要字段
                    for attr in entity.get('attributes', []):
                        attr_key = f"{entity_prefix}_{attr['name']}"
                        if attr_key not in complete_data and not attr.get('optional', False):
                            if attr_key in self.attribute_map:
                                attr_meta = self.attribute_map[attr_key]['attribute']
                                complete_data[attr_key] = self.business_generator.generate_business_value(
                                    entity['name'], attr['name'], attr_meta
                                )
        
        return complete_data
    
    def _generate_boundary_tests_for_attribute(self, attr_key: str, attr: AttributeMetadata) -> List[Dict[str, Any]]:
        """为特定属性生成边界测试"""
        tests = []
        
        if attr.min is not None:
            # 最小值测试
            tests.append({
                "id": self._next_test_id(),
                "name": f"Boundary test: {attr_key} = {attr.min}",
                "type": TestType.BOUNDARY.value,
                "description": f"Test minimum value for {attr_key}",
                "test_data": {attr_key: attr.min},
                "expected_result": "pass",
                "priority": 7,
                "tags": ["boundary", attr_key, "min"]
            })
            
            # 小于最小值
            tests.append({
                "id": self._next_test_id(),
                "name": f"Boundary test: {attr_key} < min",
                "type": TestType.BOUNDARY.value,
                "description": f"Test below minimum value for {attr_key}",
                "test_data": {attr_key: attr.min - 1},
                "expected_result": "fail",
                "priority": 7,
                "tags": ["boundary", attr_key, "below_min", "negative"]
            })
        
        if attr.max is not None:
            # 最大值测试
            tests.append({
                "id": self._next_test_id(),
                "name": f"Boundary test: {attr_key} = {attr.max}",
                "type": TestType.BOUNDARY.value,
                "description": f"Test maximum value for {attr_key}",
                "test_data": {attr_key: attr.max},
                "expected_result": "pass",
                "priority": 7,
                "tags": ["boundary", attr_key, "max"]
            })
        
        return tests
    
    def _generate_collection_tests_for_attribute(self, attr_key: str, attr: AttributeMetadata) -> List[Dict[str, Any]]:
        """为集合属性生成测试"""
        tests = []
        
        # 空集合
        tests.append({
            "id": self._next_test_id(),
            "name": f"Empty collection: {attr_key}",
            "type": TestType.COLLECTION.value,
            "description": f"Test {attr_key} with empty collection",
            "test_data": {attr_key: []},
            "expected_result": "pass" if attr.min_size == 0 else "fail",
            "priority": 6,
            "tags": ["collection", attr_key, "empty"]
        })
        
        # 单元素
        single_value = self._generate_collection_of_size(attr, 1)
        tests.append({
            "id": self._next_test_id(),
            "name": f"Single element: {attr_key}",
            "type": TestType.COLLECTION.value,
            "description": f"Test {attr_key} with one element",
            "test_data": {attr_key: single_value},
            "expected_result": "pass",
            "priority": 6,
            "tags": ["collection", attr_key, "single"]
        })
        
        # 正常大小
        normal_size = min(5, attr.max_size or 5)
        normal_value = self._generate_collection_of_size(attr, normal_size)
        tests.append({
            "id": self._next_test_id(),
            "name": f"Normal size: {attr_key}",
            "type": TestType.COLLECTION.value,
            "description": f"Test {attr_key} with {normal_size} elements",
            "test_data": {attr_key: normal_value},
            "expected_result": "pass",
            "priority": 6,
            "tags": ["collection", attr_key, "normal"]
        })
        
        # 最大容量
        if attr.max_size:
            max_value = self._generate_collection_of_size(attr, attr.max_size)
            tests.append({
                "id": self._next_test_id(),
                "name": f"Max size: {attr_key}",
                "type": TestType.COLLECTION.value,
                "description": f"Test {attr_key} at maximum capacity ({attr.max_size})",
                "test_data": {attr_key: max_value},
                "expected_result": "pass",
                "priority": 7,
                "tags": ["collection", attr_key, "max_size", "boundary"]
            })
        
        return tests
    
    def _generate_collection_tests_for_requirement(self, req: Dict[str, Any]) -> List[Dict[str, Any]]:
        """根据test_requirement生成集合测试"""
        tests = []
        
        for test_type in req.get('collection_tests', []):
            for attr_key, attr_info in self.attribute_map.items():
                attr = attr_info['attribute']
                
                if attr.is_collection:
                    if test_type == 'empty' and attr.min_size == 0:
                        tests.append({
                            "id": self._next_test_id(),
                            "name": f"Required test - Empty {attr_key}",
                            "type": TestType.COLLECTION.value,
                            "description": f"Test {attr_key} empty as required",
                            "test_data": {attr_key: []},
                            "expected_result": "pass",
                            "priority": 8,
                            "tags": ["collection", attr_key, "empty", "required_test"]
                        })
                    elif test_type == 'single':
                        value = self._generate_collection_of_size(attr, 1)
                        tests.append({
                            "id": self._next_test_id(),
                            "name": f"Required test - Single {attr_key}",
                            "type": TestType.COLLECTION.value,
                            "description": f"Test {attr_key} with single element as required",
                            "test_data": {attr_key: value},
                            "expected_result": "pass",
                            "priority": 8,
                            "tags": ["collection", attr_key, "single", "required_test"]
                        })
        
        return tests
    
    def _generate_combinatorial_tests(self, focus_attrs: List[str], strength: int = 2) -> List[Dict[str, Any]]:
        """生成组合测试"""
        tests = []
        
        # 简单的2-way实现
        if len(focus_attrs) >= 2 and strength >= 2:
            attr1, attr2 = focus_attrs[0], focus_attrs[1]
            
            # 查找对应的属性元数据
            attr1_key = None
            attr2_key = None
            
            for key in self.attribute_map:
                if attr1 in key:
                    attr1_key = key
                if attr2 in key:
                    attr2_key = key
            
            if attr1_key and attr2_key:
                # 生成组合
                combinations = [
                    (True, True),
                    (True, False),
                    (False, True),
                    (False, False)
                ]
                
                for i, (val1, val2) in enumerate(combinations):
                    test_data = {}
                    
                    # 设置值
                    if 'premium' in attr1_key or 'active' in attr1_key:
                        test_data[attr1_key] = val1
                    if 'discount' in attr2_key and 'code' in attr2_key:
                        test_data[attr2_key] = ['COMBO10'] if val2 else []
                    
                    tests.append({
                        "id": self._next_test_id(),
                        "name": f"2-way combination #{i+1}: {attr1} × {attr2}",
                        "type": TestType.COMBINATORIAL.value,
                        "description": f"Test combination of {attr1} and {attr2}",
                        "test_data": test_data,
                        "expected_result": "pass",
                        "priority": 5,
                        "tags": ["combinatorial", "2way", attr1, attr2]
                    })
        
        return tests
    
    def _generate_collection_of_size(self, attr: AttributeMetadata, size: int) -> List[Any]:
        """生成指定大小的集合"""
        # 使用业务生成器
        entity_name = None
        attr_name = attr.name
        
        # 尝试从属性映射中找到实体名
        for key, info in self.attribute_map.items():
            if info['attribute'] == attr:
                entity_name = info['entity']['name']
                break
        
        if entity_name:
            mock_attr = attr
            mock_attr.min_size = size
            mock_attr.max_size = size
            return self.business_generator._generate_collection_value(entity_name, attr_name, mock_attr)
        
        # 默认生成
        if attr.element_type == 'integer':
            return list(range(1001, 1001 + size))
        elif attr.element_type == 'string':
            return [f"item_{i}" for i in range(size)]
        else:
            return list(range(size))
    
    def _generate_rule_activation_data(self, condition: str, implies: str) -> Dict[str, Any]:
        """生成规则激活数据"""
        data = {}
        
        # 使用约束解析器
        success, data = self.constraint_parser.parse_constraint(condition, data)
        
        # 补充特定规则的数据
        if "size(cart_items) >= 10" in condition:
            data['cart_items'] = list(range(1001, 1011))
            data['cart_discount_codes'] = ['BULK10']
        elif "cart_is_premium_member == true" in condition:
            data['cart_is_premium_member'] = True
            data['cart_total_price'] = 50.0
        elif "size(cart_items) == 0" in condition:
            data['cart_items'] = []
            data['cart_total_price'] = 0.0
        elif "Order.subtotal > 100" in condition:
            data['order_subtotal'] = 150.0
            data['order_shipping_cost'] = 0.0
        
        return self._complete_test_data(data)
    
    def _generate_rule_deactivation_data(self, condition: str) -> Dict[str, Any]:
        """生成规则未激活数据"""
        data = {}
        
        # 生成不满足条件的数据
        if "size(cart_items) >= 10" in condition:
            data['cart_items'] = list(range(1001, 1010))  # 只有9个
            data['cart_discount_codes'] = []
        elif "cart_is_premium_member == true" in condition:
            data['cart_is_premium_member'] = False
            data['cart_total_price'] = 50.0
        elif "size(cart_items) == 0" in condition:
            data['cart_items'] = [1001]
            data['cart_total_price'] = 29.99
        elif "Order.subtotal > 100" in condition:
            data['order_subtotal'] = 99.99
            data['order_shipping_cost'] = 10.0
        
        return self._complete_test_data(data)
    
    def _generate_constraint_violation_data(self, constraint: str) -> Dict[str, Any]:
        """生成违反约束的数据"""
        data = {}
        
        if "cart_total_price >= 0" in constraint:
            data['cart_total_price'] = -10.0
        elif "size(cart_items) <= 50" in constraint:
            data['cart_items'] = list(range(1001, 1052))  # 51个
        elif "size(cart_discount_codes) <= 5" in constraint:
            data['cart_discount_codes'] = [f"CODE{i}" for i in range(6)]
        elif "product_price > 0" in constraint:
            data['product_price'] = 0.0
        elif "size(product_categories) >= 1" in constraint:
            data['product_categories'] = []
        elif "order_amount > 0" in constraint:
            data['order_amount'] = 0.0
        elif "user_balance >= 0" in constraint:
            data['user_balance'] = -100.0
        
        return self._complete_test_data(data)
    
    def _get_wrong_type_value(self, correct_type: str) -> Any:
        """获取错误类型的值"""
        if correct_type == 'integer':
            return "not_a_number"
        elif correct_type == 'real':
            return "not_a_float"
        elif correct_type == 'boolean':
            return "not_a_bool"
        elif correct_type == 'string':
            return 12345
        else:
            return None
    
    def _sanitize_tag(self, tag: str) -> str:
        """清理标签名称"""
        return tag.lower().replace(' ', '_').replace('-', '_')
    
    def _next_test_id(self) -> str:
        """生成下一个测试ID"""
        self.test_counter += 1
        return f"TEST_{self.test_counter:04d}"
    
    def _optimize_test_suite(self, tests: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """优化测试套件"""
        # 简单去重
        seen = set()
        optimized = []
        
        for test in tests:
            test_key = json.dumps(test['test_data'], sort_keys=True)
            if test_key not in seen:
                seen.add(test_key)
                optimized.append(test)
        
        return optimized
    
    def _format_output(self, tests: List[Dict[str, Any]]) -> Dict[str, Any]:
        """格式化输出"""
        # 按类型分组
        test_suites = {}
        for test in tests:
            test_type = test['type']
            if test_type not in test_suites:
                test_suites[test_type] = []
            test_suites[test_type].append(test)
        
        # 统计信息
        tag_counts = {}
        priority_counts = {}
        
        for test in tests:
            for tag in test.get('tags', []):
                tag_counts[tag] = tag_counts.get(tag, 0) + 1
            
            priority = test.get('priority', 5)
            priority_level = 'high' if priority >= 8 else 'medium' if priority >= 5 else 'low'
            priority_counts[priority_level] = priority_counts.get(priority_level, 0) + 1
        
        # 计算覆盖率
        coverage = self._calculate_coverage(tests)
        
        return {
            "meta": {
                "generator": "Unified DSL Test Generator v5.0",
                "domain": self.domain,
                "timestamp": datetime.now().isoformat(),
                "dsl_file": self.dsl_file,
                "test_requirements_parsed": len(self.test_requirements) > 0
            },
            "summary": {
                "total_tests": len(tests),
                "test_distribution": {test_type: len(tests) for test_type, tests in test_suites.items()},
                "tag_distribution": tag_counts,
                "priority_distribution": priority_counts,
                "requirements_coverage": coverage
            },
            "test_suites": test_suites
        }
    
    def _calculate_coverage(self, tests: List[Dict[str, Any]]) -> Dict[str, Any]:
        """计算覆盖率"""
        coverage = {
            "test_requirements": [],
            "constraints": [],
            "rules": []
        }
        
        # 测试需求覆盖
        for req in self.test_requirements:
            # 检查是否有相关测试
            req_name = req['name']
            req_type = req['type']
            
            covered = False
            if req_type == 'boundary':
                covered = any('boundary' in test.get('tags', []) and 
                            any(focus in str(test) for focus in req.get('focus', [])) 
                            for test in tests)
            elif req_type == 'collection':
                covered = any('collection' in test.get('tags', []) for test in tests)
            elif req_type == 'combinatorial':
                covered = any('combinatorial' in test.get('tags', []) for test in tests)
            
            coverage["test_requirements"].append({
                "name": req_name,
                "type": req_type,
                "covered": covered
            })
        
        # 约束覆盖
        for constraint in self.dsl_model.get('constraints', []):
            covered = any(constraint in test.get('constraints_tested', []) for test in tests)
            coverage["constraints"].append({
                "constraint": constraint,
                "covered": covered
            })
        
        # 规则覆盖
        for rule in self.dsl_model.get('rules', []):
            rule_name = rule.get('name', '')
            covered = any(rule_name in test.get('rules_tested', []) for test in tests)
            coverage["rules"].append({
                "rule": rule_name,
                "covered": covered
            })
        
        return coverage


def main():
    parser = argparse.ArgumentParser(description="Unified DSL Test Generator V5")
    parser.add_argument("dsl_file", help="Path to DSL YAML file")
    parser.add_argument("-o", "--output", default="tests_v5.json", help="Output file")
    parser.add_argument("--max-tests", type=int, default=50, help="Max tests per type")
    
    args = parser.parse_args()
    
    config = {
        'max_tests_per_type': args.max_tests
    }
    
    # 生成测试
    generator = UnifiedDSLTestGeneratorV5(args.dsl_file, config)
    result = generator.generate_tests()
    
    # 保存结果
    with open(args.output, 'w', encoding='utf-8') as f:
        json.dump(result, f, ensure_ascii=False, indent=2)
    
    print(f"\nTests saved to: {args.output}")


if __name__ == "__main__":
    main()