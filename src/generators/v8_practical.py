#!/usr/bin/env python3
"""
V8 Practical Test Generator
实用的测试生成器，基于V7架构优化，确保生成的测试用例正确可用
"""

import json
import yaml
import random
import argparse
import logging
from typing import Any, Dict, List, Optional, Tuple
from datetime import datetime, timedelta
from pathlib import Path
from dataclasses import dataclass, field

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


@dataclass
class Attribute:
    """属性定义"""
    name: str
    type: str
    required: bool = True
    enum: List[Any] = None
    is_collection: bool = False
    is_temporal: bool = False
    default: Any = None


@dataclass
class Entity:
    """实体定义"""
    name: str
    attributes: List[Attribute] = field(default_factory=list)
    constraints: List[str] = field(default_factory=list)
    rules: List[Dict[str, Any]] = field(default_factory=list)


class YAMLParser:
    """YAML解析器"""
    
    def parse_file(self, file_path: str) -> List[Entity]:
        """解析YAML文件"""
        with open(file_path, 'r', encoding='utf-8') as f:
            data = yaml.safe_load(f)
        
        entities = []
        
        # 解析entities部分
        entities_data = data.get('entities', [])
        if isinstance(entities_data, list):
            # 处理列表格式
            for entity_data in entities_data:
                if isinstance(entity_data, dict) and 'name' in entity_data:
                    entity_name = entity_data['name']
                    entity = self._parse_entity(entity_name, entity_data)
                    entities.append(entity)
        elif isinstance(entities_data, dict):
            # 处理字典格式
            for entity_name, entity_data in entities_data.items():
                entity = self._parse_entity(entity_name, entity_data)
                entities.append(entity)
        
        return entities
    
    def _parse_entity(self, entity_name: str, entity_data: Dict[str, Any]) -> Entity:
        entity = Entity(name=entity_name)
        
        # 解析属性
        attributes_data = entity_data.get('attributes', [])
        if isinstance(attributes_data, list):
            # 处理列表格式的属性
            for attr_data in attributes_data:
                if isinstance(attr_data, dict) and 'name' in attr_data:
                    attr = self._parse_attribute(attr_data)
                    entity.attributes.append(attr)
        elif isinstance(attributes_data, dict):
            # 处理字典格式的属性
            for attr_name, attr_data in attributes_data.items():
                if isinstance(attr_data, dict):
                    attr_data['name'] = attr_name
                    attr = self._parse_attribute(attr_data)
                else:
                    # 简单类型定义
                    attr = Attribute(name=attr_name, type=attr_data)
                
                entity.attributes.append(attr)
        
        # 解析约束
        for constraint in entity_data.get('constraints', []):
            if isinstance(constraint, dict):
                entity.constraints.append(constraint.get('expression', ''))
            else:
                entity.constraints.append(str(constraint))
        
        # 解析规则
        entity.rules = entity_data.get('rules', [])
        
        return entity
    
    def _parse_attribute(self, attr_data: Dict[str, Any]) -> Attribute:
        """解析单个属性"""
        attr_type = attr_data.get('type', 'string')
        
        # 处理集合类型
        is_collection = False
        if attr_type.startswith('array[') or attr_type.startswith('set['):
            is_collection = True
            # 提取基本类型
            base_type = attr_type[attr_type.index('[')+1:attr_type.index(']')]
            attr_type = base_type
        elif attr_type in ['array', 'list', 'set']:
            is_collection = True
        
        # 处理real类型
        if attr_type == 'real':
            attr_type = 'float'
        
        return Attribute(
            name=attr_data.get('name', 'unnamed'),
            type=attr_type,
            required=attr_data.get('required', True),
            enum=attr_data.get('enum'),
            is_collection=is_collection,
            is_temporal=attr_type in ['date', 'datetime', 'timestamp']
        )


class ValueGenerator:
    """智能值生成器"""
    
    def __init__(self):
        self.id_counters = {}
        self.domain_patterns = self._init_domain_patterns()
        self.generation_count = {}  # 跟踪生成次数以增加多样性
    
    def _init_domain_patterns(self) -> Dict[str, Dict[str, Any]]:
        """初始化领域模式"""
        return {
            'ecommerce': {
                'product_id': lambda: random.randint(1001, 9999),
                'price': lambda: random.choice([9.99, 19.99, 29.99, 49.99, 99.99]),
                'discount': lambda: random.choice([0, 0.1, 0.2, 0.25, 0.5]),
                'status': ['active', 'inactive', 'out_of_stock'],
                'category': ['electronics', 'clothing', 'books', 'home']
            },
            'education': {
                'student_id': lambda: random.randint(2024001, 2024999),
                'score': lambda: random.randint(0, 100),
                'grade': ['A', 'B', 'C', 'D', 'F'],
                'semester': ['Spring 2024', 'Fall 2024', 'Spring 2025']
            },
            'general': {
                'name': ['Alice', 'Bob', 'Charlie', 'David', 'Emma'],
                'email': lambda: f"user{random.randint(1,100)}@example.com",
                'phone': lambda: f"{random.randint(100,999)}-{random.randint(100,999)}-{random.randint(1000,9999)}",
                'date': lambda: (datetime.now() + timedelta(days=random.randint(-30, 30))).strftime('%Y-%m-%d')
            }
        }
    
    def generate(self, entity_name: str, attr: Attribute, context: Dict[str, Any] = None) -> Any:
        """生成属性值"""
        # 处理枚举
        if attr.enum:
            return random.choice(attr.enum)
        
        # 处理ID
        if 'id' in attr.name.lower():
            return self._generate_id(entity_name, attr.name)
        
        # 先检查是否是集合类型
        if attr.is_collection:
            return self._generate_collection(attr.name)
        
        # 根据类型生成
        if attr.type == 'int' or attr.type == 'integer':
            return self._generate_int(attr.name, context)
        elif attr.type == 'float' or attr.type == 'double':
            return self._generate_float(attr.name, context)
        elif attr.type == 'string':
            return self._generate_string(attr.name, context)
        elif attr.type == 'boolean' or attr.type == 'bool':
            return random.choice([True, False])
        elif attr.is_temporal:
            return self._generate_date(attr.name)
        else:
            return f"{attr.name}_value"
    
    def _generate_id(self, entity_name: str, attr_name: str) -> int:
        """生成ID"""
        key = f"{entity_name}_{attr_name}"
        if key not in self.id_counters:
            # 设置起始值
            if 'product' in entity_name.lower():
                self.id_counters[key] = 1001
            elif 'order' in entity_name.lower():
                self.id_counters[key] = 10001
            elif 'student' in entity_name.lower():
                self.id_counters[key] = 2024001
            elif 'user' in entity_name.lower() or 'customer' in entity_name.lower():
                self.id_counters[key] = 1
            else:
                self.id_counters[key] = 1
        
        current = self.id_counters[key]
        self.id_counters[key] += 1
        return current
    
    def _generate_int(self, attr_name: str, context: Dict[str, Any] = None) -> int:
        """生成整数"""
        attr_lower = attr_name.lower()
        
        # 跟踪生成次数以增加多样性
        gen_key = f"int_{attr_name}"
        self.generation_count[gen_key] = self.generation_count.get(gen_key, 0) + 1
        count = self.generation_count[gen_key]
        
        # 基于属性名的智能生成
        if 'age' in attr_lower:
            # 不同年龄段
            age_ranges = [(18, 25), (26, 35), (36, 50), (51, 65), (66, 80)]
            age_range = age_ranges[(count - 1) % len(age_ranges)]
            return random.randint(age_range[0], age_range[1])
        elif 'score' in attr_lower:
            # 不同分数段
            score_ranges = [(0, 20), (21, 40), (41, 60), (61, 80), (81, 100)]
            score_range = score_ranges[(count - 1) % len(score_ranges)]
            return random.randint(score_range[0], score_range[1])
        elif 'grade' in attr_lower or 'level' in attr_lower:
            # 循环使用不同级别
            return ((count - 1) % 12) + 1
        elif 'quantity' in attr_lower or 'count' in attr_lower:
            # 不同数量级别
            quantities = [1, 5, 10, 20, 50]
            base = quantities[(count - 1) % len(quantities)]
            return base + random.randint(-2, 2)
        elif 'stock' in attr_lower:
            # 不同库存水平
            stock_levels = [0, 10, 50, 100, 500, 1000]
            return stock_levels[(count - 1) % len(stock_levels)] + random.randint(0, 10)
        elif 'price' in attr_lower or 'cost' in attr_lower or 'amount' in attr_lower:
            # 不同价格区间
            price_ranges = [(10, 50), (51, 100), (101, 500), (501, 1000)]
            price_range = price_ranges[(count - 1) % len(price_ranges)]
            return random.randint(price_range[0], price_range[1])
        elif 'year' in attr_lower:
            return 2020 + ((count - 1) % 6)
        elif 'month' in attr_lower:
            return ((count - 1) % 12) + 1
        elif 'day' in attr_lower:
            return ((count - 1) % 28) + 1
        
        # 默认范围 - 也要多样化
        ranges = [(1, 20), (21, 50), (51, 80), (81, 100)]
        range_idx = (count - 1) % len(ranges)
        return random.randint(ranges[range_idx][0], ranges[range_idx][1])
    
    def _generate_float(self, attr_name: str, context: Dict[str, Any] = None) -> float:
        """生成浮点数"""
        attr_lower = attr_name.lower()
        
        if 'price' in attr_lower or 'cost' in attr_lower:
            # 生成真实的价格
            prices = [9.99, 19.99, 29.99, 49.99, 99.99, 149.99, 199.99]
            base_price = random.choice(prices)
            # 可能的折扣
            if random.random() < 0.3:
                base_price *= random.choice([0.9, 0.8, 0.7])
            return round(base_price, 2)
        elif 'rate' in attr_lower or 'percentage' in attr_lower:
            return round(random.uniform(0, 1), 2)
        elif 'weight' in attr_lower:
            return round(random.uniform(0.1, 50), 2)
        elif 'amount' in attr_lower:
            return round(random.uniform(10, 500), 2)
        elif 'score' in attr_lower:
            return round(random.uniform(0, 100), 1)
        
        return round(random.uniform(0, 100), 2)
    
    def _generate_string(self, attr_name: str, context: Dict[str, Any] = None) -> str:
        """生成字符串"""
        attr_lower = attr_name.lower()
        
        # 跟踪生成次数
        gen_key = f"string_{attr_name}"
        self.generation_count[gen_key] = self.generation_count.get(gen_key, 0) + 1
        count = self.generation_count[gen_key]
        
        # 常见模式
        if 'name' in attr_lower:
            if 'first' in attr_lower:
                names = ['Alice', 'Bob', 'Charlie', 'David', 'Emma', 'Frank', 'Grace', 'Henry', 'Iris', 'Jack']
                return names[(count - 1) % len(names)]
            elif 'last' in attr_lower:
                names = ['Smith', 'Johnson', 'Brown', 'Davis', 'Wilson', 'Miller', 'Taylor', 'Anderson']
                return names[(count - 1) % len(names)]
            else:
                first_names = ['Alice', 'Bob', 'Charlie', 'David', 'Emma']
                last_names = ['Smith', 'Johnson', 'Brown', 'Davis', 'Wilson']
                return f"{first_names[(count - 1) % len(first_names)]} {last_names[(count - 1) % len(last_names)]}"
        elif 'email' in attr_lower:
            domains = ['example.com', 'test.com', 'demo.org', 'sample.net']
            return f"user{count}@{domains[(count - 1) % len(domains)]}"
        elif 'phone' in attr_lower:
            return f"{100 + count % 900}-{555}-{1000 + count % 9000}"
        elif 'address' in attr_lower:
            streets = ['Main St', 'Oak Ave', 'Elm Dr', 'Park Blvd', 'First St']
            return f"{count} {streets[(count - 1) % len(streets)]}, City, State {10000 + count}"
        elif 'status' in attr_lower:
            statuses = ['active', 'inactive', 'pending', 'completed', 'processing', 'cancelled']
            return statuses[(count - 1) % len(statuses)]
        elif 'code' in attr_lower:
            if 'discount' in attr_lower:
                codes = ['SAVE10', 'WELCOME20', 'VIP15', 'SUMMER25', 'WINTER30', 'SPRING15']
                return codes[(count - 1) % len(codes)]
            else:
                return f"CODE{1000 + count}"
        elif 'description' in attr_lower:
            variations = ['Basic', 'Standard', 'Premium', 'Special', 'Limited']
            return f"{variations[(count - 1) % len(variations)]} description for {attr_name}"
        elif 'category' in attr_lower:
            categories = ['electronics', 'clothing', 'books', 'home', 'sports', 'toys', 'food', 'beauty']
            return categories[(count - 1) % len(categories)]
        elif 'type' in attr_lower:
            types = ['standard', 'premium', 'basic', 'advanced', 'professional']
            return types[(count - 1) % len(types)]
        elif 'color' in attr_lower:
            colors = ['red', 'blue', 'green', 'black', 'white', 'yellow', 'purple', 'orange']
            return colors[(count - 1) % len(colors)]
        
        # 默认值
        return f"{attr_name}_value_{count}"
    
    def _generate_date(self, attr_name: str) -> str:
        """生成日期"""
        base = datetime.now()
        
        if 'birth' in attr_name.lower():
            # 生日：18-80年前
            days_ago = random.randint(18*365, 80*365)
            date = base - timedelta(days=days_ago)
        elif 'start' in attr_name.lower():
            # 开始日期：过去30天到未来30天
            offset = random.randint(-30, 30)
            date = base + timedelta(days=offset)
        elif 'end' in attr_name.lower():
            # 结束日期：未来1-90天
            offset = random.randint(1, 90)
            date = base + timedelta(days=offset)
        elif 'created' in attr_name.lower() or 'registration' in attr_name.lower():
            # 创建日期：过去365天内
            offset = random.randint(0, 365)
            date = base - timedelta(days=offset)
        else:
            # 默认：前后30天
            offset = random.randint(-30, 30)
            date = base + timedelta(days=offset)
        
        return date.strftime('%Y-%m-%d')
    
    def _generate_collection(self, attr_name: str) -> List[Any]:
        """生成集合"""
        attr_lower = attr_name.lower()
        
        if 'permissions' in attr_lower or 'roles' in attr_lower:
            all_items = ['read', 'write', 'delete', 'admin', 'execute']
            size = random.randint(1, min(3, len(all_items)))
            return random.sample(all_items, size)
        elif 'tags' in attr_lower:
            all_tags = ['important', 'urgent', 'review', 'approved', 'pending', 'new']
            size = random.randint(1, 3)
            return random.sample(all_tags, size)
        elif 'items' in attr_lower:
            # 购物车items - 产品ID数组
            size = random.randint(1, 5)
            return [random.randint(1001, 1020) for _ in range(size)]
        elif 'products' in attr_lower:
            size = random.randint(1, 5)
            return [f"product_{i+1}" for i in range(size)]
        elif 'discount_codes' in attr_lower:
            # 折扣码集合
            all_codes = ['SAVE10', 'WELCOME20', 'VIP15', 'SUMMER25', 'BULK15']
            size = random.randint(0, min(3, len(all_codes)))
            return random.sample(all_codes, size)
        elif 'categories' in attr_lower:
            all_cats = ['electronics', 'clothing', 'books', 'home', 'sports', 'toys']
            size = random.randint(1, 3)
            return random.sample(all_cats, size)
        
        # 默认集合
        size = random.randint(1, 3)
        return [f"{attr_name}_{i+1}" for i in range(size)]


class ConstraintHandler:
    """约束处理器"""
    
    def evaluate(self, expression: str, data: Dict[str, Any]) -> bool:
        """求值约束表达式"""
        try:
            # 替换变量
            expr = expression
            for key, value in data.items():
                if key in expr:
                    if isinstance(value, str):
                        expr = expr.replace(key, f"'{value}'")
                    elif isinstance(value, list):
                        expr = expr.replace(key, str(value))
                    else:
                        expr = expr.replace(key, str(value))
            
            # 处理特殊函数
            if 'size(' in expr:
                # 处理size函数
                import re
                size_pattern = r'size\((\w+)\)'
                def size_replacer(match):
                    var_name = match.group(1)
                    if var_name in data and hasattr(data[var_name], '__len__'):
                        return str(len(data[var_name]))
                    return '0'
                expr = re.sub(size_pattern, size_replacer, expr)
            
            # 安全求值
            allowed_names = {
                'len': len,
                'abs': abs,
                'min': min,
                'max': max,
                'sum': sum
            }
            
            result = eval(expr, {"__builtins__": {}}, allowed_names)
            return bool(result)
        except Exception as e:
            logger.warning(f"Failed to evaluate constraint '{expression}': {e}")
            return True  # 默认满足
    
    def fix_constraint_violation(self, data: Dict[str, Any], constraint: str, 
                               entity: Entity) -> Dict[str, Any]:
        """修复约束违反"""
        # 简单的修复策略
        if '>' in constraint:
            parts = constraint.split('>')
            if len(parts) == 2:
                left = parts[0].strip()
                right = parts[1].strip()
                
                # 处理简单的比较
                if left in data and right.strip().isdigit():
                    target = int(right)
                    if isinstance(data[left], (int, float)):
                        data[left] = target + random.randint(1, 10)
                
                # 处理字段间比较
                elif left in data and right in data:
                    if isinstance(data[left], (int, float)) and isinstance(data[right], (int, float)):
                        data[left] = data[right] + random.randint(1, 10)
        
        elif '<' in constraint:
            parts = constraint.split('<')
            if len(parts) == 2:
                left = parts[0].strip()
                right = parts[1].strip()
                
                if left in data and right.strip().isdigit():
                    target = int(right)
                    if isinstance(data[left], (int, float)):
                        data[left] = max(0, target - random.randint(1, 10))
                
                elif left in data and right in data:
                    if isinstance(data[left], (int, float)) and isinstance(data[right], (int, float)):
                        data[left] = max(0, data[right] - random.randint(1, 10))
        
        elif '>=' in constraint:
            parts = constraint.split('>=')
            if len(parts) == 2:
                left = parts[0].strip()
                right = parts[1].strip()
                
                if left in data and right.strip().isdigit():
                    target = int(right)
                    if isinstance(data[left], (int, float)):
                        data[left] = target + random.randint(0, 5)
        
        return data


class TestGenerator:
    """主测试生成器"""
    
    def __init__(self):
        self.value_generator = ValueGenerator()
        self.constraint_handler = ConstraintHandler()
    
    def generate_tests(self, entities: List[Entity]) -> List[Dict[str, Any]]:
        """生成测试用例"""
        all_tests = []
        
        for entity in entities:
            logger.info(f"Generating tests for entity: {entity.name}")
            
            # 生成各种类型的测试
            tests = []
            
            # 功能测试
            tests.extend(self._generate_functional_tests(entity, 3))
            
            # 边界测试
            tests.extend(self._generate_boundary_tests(entity, 2))
            
            # 负面测试
            tests.extend(self._generate_negative_tests(entity, 2))
            
            # 约束测试
            tests.extend(self._generate_constraint_tests(entity))
            
            # 添加元信息
            for i, test in enumerate(tests):
                test['test_id'] = f"{entity.name}_test_{i+1}"
                test['entity'] = entity.name
                test['timestamp'] = datetime.now().isoformat()
            
            all_tests.extend(tests)
        
        return all_tests
    
    def _generate_functional_tests(self, entity: Entity, count: int) -> List[Dict[str, Any]]:
        """生成功能测试"""
        tests = []
        
        for i in range(count):
            # 为每个测试生成不同的数据变体
            data = self._generate_valid_data(entity)
            
            # 增加数据多样性
            if i > 0:
                # 随机修改一些属性值
                for attr in entity.attributes:
                    if random.random() < 0.3:  # 30%概率修改
                        if attr.name in data:
                            # 重新生成该属性
                            data[attr.name] = self.value_generator.generate(entity.name, attr, data)
            
            test = {
                'test_name': f"{entity.name}_functional_{i+1}",
                'test_type': 'functional',
                'description': f"Test basic functionality of {entity.name}",
                'test_data': data,
                'expected_result': 'pass',
                'priority': 8
            }
            tests.append(test)
        
        return tests
    
    def _generate_boundary_tests(self, entity: Entity, count: int) -> List[Dict[str, Any]]:
        """生成边界测试"""
        tests = []
        
        # 数值类型边界测试
        numeric_attrs = [attr for attr in entity.attributes 
                        if attr.type in ['int', 'integer', 'float', 'double'] and not attr.is_collection]
        
        for attr in numeric_attrs[:count]:
            # 最小值测试
            min_data = self._generate_valid_data(entity)
            min_data[attr.name] = 0 if 'int' in attr.type else 0.01
            
            tests.append({
                'test_name': f"{entity.name}_{attr.name}_min_boundary",
                'test_type': 'boundary',
                'description': f"Test minimum boundary for {attr.name}",
                'test_data': min_data,
                'expected_result': 'pass',
                'priority': 7
            })
            
            # 最大值测试
            max_data = self._generate_valid_data(entity)
            max_data[attr.name] = 999999 if 'int' in attr.type else 999999.99
            
            tests.append({
                'test_name': f"{entity.name}_{attr.name}_max_boundary",
                'test_type': 'boundary',
                'description': f"Test maximum boundary for {attr.name}",
                'test_data': max_data,
                'expected_result': 'pass',
                'priority': 7
            })
        
        # 集合类型边界测试
        collection_attrs = [attr for attr in entity.attributes if attr.is_collection]
        
        for attr in collection_attrs[:1]:  # 只测试一个集合
            # 空集合测试
            empty_data = self._generate_valid_data(entity)
            empty_data[attr.name] = []
            
            tests.append({
                'test_name': f"{entity.name}_{attr.name}_empty_collection",
                'test_type': 'boundary',
                'description': f"Test empty collection for {attr.name}",
                'test_data': empty_data,
                'expected_result': 'pass',
                'priority': 7
            })
            
            # 大集合测试
            large_data = self._generate_valid_data(entity)
            if 'items' in attr.name:
                large_data[attr.name] = [random.randint(1001, 1050) for _ in range(10)]
            else:
                large_data[attr.name] = [f"{attr.name}_{i}" for i in range(10)]
            
            tests.append({
                'test_name': f"{entity.name}_{attr.name}_large_collection",
                'test_type': 'boundary',
                'description': f"Test large collection for {attr.name}",
                'test_data': large_data,
                'expected_result': 'pass',
                'priority': 7
            })
        
        return tests
    
    def _generate_negative_tests(self, entity: Entity, count: int) -> List[Dict[str, Any]]:
        """生成负面测试"""
        tests = []
        
        for i, attr in enumerate(entity.attributes[:count]):
            # 类型错误测试
            invalid_data = self._generate_valid_data(entity)
            
            if attr.type in ['int', 'integer']:
                invalid_data[attr.name] = "not_a_number"
            elif attr.type == 'string':
                invalid_data[attr.name] = 12345
            elif attr.type in ['boolean', 'bool']:
                invalid_data[attr.name] = "yes"
            elif attr.is_collection:
                invalid_data[attr.name] = "not_an_array"
            else:
                invalid_data[attr.name] = None
            
            tests.append({
                'test_name': f"{entity.name}_{attr.name}_invalid_type",
                'test_type': 'negative',
                'description': f"Test invalid type for {attr.name}",
                'test_data': invalid_data,
                'expected_result': 'fail',
                'expected_error': 'type_error',
                'priority': 6
            })
        
        return tests
    
    def _generate_constraint_tests(self, entity: Entity) -> List[Dict[str, Any]]:
        """生成约束测试"""
        tests = []
        
        # 如果没有约束，生成基本的约束测试
        if not entity.constraints:
            # 为数值属性生成隐式约束测试
            for attr in entity.attributes:
                if attr.type in ['int', 'integer', 'float', 'double'] and not attr.is_collection:
                    # 正值约束
                    positive_data = self._generate_valid_data(entity)
                    positive_data[attr.name] = abs(positive_data.get(attr.name, 1))
                    
                    tests.append({
                        'test_name': f"{entity.name}_{attr.name}_positive_constraint",
                        'test_type': 'constraint_satisfaction',
                        'description': f"Test implicit positive constraint for {attr.name}",
                        'test_data': positive_data,
                        'constraint': f"{attr.name} >= 0",
                        'expected_result': 'pass',
                        'priority': 6
                    })
                    break  # 只添加一个
        
        # 显式约束测试
        for i, constraint in enumerate(entity.constraints):
            # 满足约束的测试
            valid_data = self._generate_constraint_satisfying_data(entity, constraint)
            tests.append({
                'test_name': f"{entity.name}_constraint_{i+1}_satisfied",
                'test_type': 'constraint_satisfaction',
                'description': f"Test constraint satisfaction: {constraint}",
                'test_data': valid_data,
                'constraint': constraint,
                'expected_result': 'pass',
                'priority': 8
            })
            
            # 违反约束的测试
            invalid_data = self._generate_constraint_violating_data(entity, constraint)
            tests.append({
                'test_name': f"{entity.name}_constraint_{i+1}_violated",
                'test_type': 'constraint_violation',
                'description': f"Test constraint violation: {constraint}",
                'test_data': invalid_data,
                'constraint': constraint,
                'expected_result': 'fail',
                'expected_error': 'constraint_violation',
                'priority': 7
            })
        
        return tests
    
    def _generate_valid_data(self, entity: Entity) -> Dict[str, Any]:
        """生成有效数据"""
        data = {}
        
        # 生成基本数据
        for attr in entity.attributes:
            if attr.required or random.random() > 0.2:
                data[attr.name] = self.value_generator.generate(entity.name, attr, data)
        
        # 确保满足约束
        max_attempts = 10
        for attempt in range(max_attempts):
            all_satisfied = True
            
            for constraint in entity.constraints:
                if not self.constraint_handler.evaluate(constraint, data):
                    all_satisfied = False
                    data = self.constraint_handler.fix_constraint_violation(data, constraint, entity)
                    break
            
            if all_satisfied:
                break
        
        return data
    
    def _generate_constraint_satisfying_data(self, entity: Entity, constraint: str) -> Dict[str, Any]:
        """生成满足特定约束的数据"""
        data = self._generate_valid_data(entity)
        
        # 确保满足特定约束
        max_attempts = 5
        for _ in range(max_attempts):
            if self.constraint_handler.evaluate(constraint, data):
                break
            data = self.constraint_handler.fix_constraint_violation(data, constraint, entity)
        
        return data
    
    def _generate_constraint_violating_data(self, entity: Entity, constraint: str) -> Dict[str, Any]:
        """生成违反特定约束的数据"""
        data = self._generate_valid_data(entity)
        
        # 故意违反约束
        if '>' in constraint and '=' not in constraint:
            parts = constraint.split('>')
            if len(parts) == 2:
                left = parts[0].strip()
                if left in data and isinstance(data[left], (int, float)):
                    data[left] = 0  # 设为0通常会违反大于约束
        
        elif '<' in constraint and '=' not in constraint:
            parts = constraint.split('<')
            if len(parts) == 2:
                left = parts[0].strip()
                if left in data and isinstance(data[left], (int, float)):
                    data[left] = 999999  # 设为大值通常会违反小于约束
        
        elif '==' in constraint:
            parts = constraint.split('==')
            if len(parts) == 2:
                left = parts[0].strip()
                if left in data:
                    # 改变值
                    if isinstance(data[left], bool):
                        data[left] = not data[left]
                    elif isinstance(data[left], (int, float)):
                        data[left] = data[left] + 1
                    elif isinstance(data[left], str):
                        data[left] = f"different_{data[left]}"
        
        return data


def main():
    """主函数"""
    parser = argparse.ArgumentParser(description='V8 Practical Test Generator')
    parser.add_argument('dsl_file', help='Path to DSL YAML file')
    parser.add_argument('-o', '--output', default='generated_tests.json',
                       help='Output file path')
    parser.add_argument('-v', '--verbose', action='store_true',
                       help='Enable verbose logging')
    
    args = parser.parse_args()
    
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)
    
    try:
        # 解析YAML
        yaml_parser = YAMLParser()
        entities = yaml_parser.parse_file(args.dsl_file)
        logger.info(f"Parsed {len(entities)} entities from {args.dsl_file}")
        
        # 生成测试
        generator = TestGenerator()
        tests = generator.generate_tests(entities)
        logger.info(f"Generated {len(tests)} tests")
        
        # 保存结果
        output = {
            'dsl_file': args.dsl_file,
            'generation_time': datetime.now().isoformat(),
            'total_tests': len(tests),
            'tests': tests
        }
        
        # 确保输出目录存在
        output_path = Path(args.output)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(output, f, indent=2, ensure_ascii=False)
        
        logger.info(f"Output saved to: {args.output}")
        
        # 打印统计
        test_types = {}
        for test in tests:
            test_type = test['test_type']
            test_types[test_type] = test_types.get(test_type, 0) + 1
        
        print("\nTest Statistics:")
        for test_type, count in sorted(test_types.items()):
            print(f"  {test_type}: {count}")
        print(f"\nTotal: {len(tests)} tests")
        
    except Exception as e:
        logger.error(f"Error: {e}")
        raise


if __name__ == '__main__':
    main()