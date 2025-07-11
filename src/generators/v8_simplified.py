#!/usr/bin/env python3
"""
V8 Simplified Test Generator
简化但实用的架构优化版本，专注于生成正确可用的测试用例
"""

import json
import random
from typing import Any, Dict, List, Optional, Tuple
from datetime import datetime, timedelta
import logging
from pathlib import Path
import argparse
import sys

# 设置项目根目录
project_root = Path(__file__).parent.parent.parent
sys.path.insert(0, str(project_root))

from src.models.dsl_models import DSLSpecification, Entity, Attribute, Constraint, Rule
from src.parsers.yaml_parser import YAMLParser

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


class ExpressionEvaluator:
    """简化的表达式求值器"""
    
    def evaluate(self, expression: str, context: Dict[str, Any]) -> bool:
        """求值表达式"""
        try:
            # 替换变量
            expr = expression
            for key, value in context.items():
                if key in expr:
                    if isinstance(value, str):
                        expr = expr.replace(key, f"'{value}'")
                    else:
                        expr = expr.replace(key, str(value))
            
            # 安全求值
            result = eval(expr, {"__builtins__": {}}, {})
            return bool(result)
        except:
            return True  # 出错时默认满足


class ValueGenerator:
    """统一的值生成器"""
    
    def __init__(self):
        self.id_counters = {}
    
    def generate(self, entity_name: str, attr: Attribute, constraints: List[str] = None) -> Any:
        """生成属性值"""
        attr_name = attr.name
        
        # ID生成
        if 'id' in attr_name.lower():
            return self._generate_id(entity_name, attr_name)
        
        # 枚举类型
        if attr.enum:
            return random.choice(attr.enum)
        
        # 根据类型生成
        if attr.type == 'int':
            return self._generate_int(attr_name, constraints)
        elif attr.type == 'float':
            return self._generate_float(attr_name)
        elif attr.type == 'string':
            return self._generate_string(attr_name)
        elif attr.type == 'boolean':
            return random.choice([True, False])
        elif attr.type == 'date':
            return self._generate_date()
        elif attr.is_collection:
            return self._generate_collection(attr_name)
        else:
            return f"{attr_name}_value"
    
    def _generate_id(self, entity_name: str, attr_name: str) -> int:
        """生成ID"""
        key = f"{entity_name}_{attr_name}"
        if key not in self.id_counters:
            # 根据实体类型设置起始值
            if 'product' in entity_name.lower():
                self.id_counters[key] = 1001
            elif 'order' in entity_name.lower():
                self.id_counters[key] = 10001
            elif 'student' in entity_name.lower():
                self.id_counters[key] = 2024001
            else:
                self.id_counters[key] = 1
        
        current = self.id_counters[key]
        self.id_counters[key] += 1
        return current
    
    def _generate_int(self, attr_name: str, constraints: List[str] = None) -> int:
        """生成整数"""
        # 根据属性名智能生成
        if 'age' in attr_name:
            return random.randint(18, 65)
        elif 'score' in attr_name:
            return random.randint(0, 100)
        elif 'grade' in attr_name:
            return random.randint(1, 12)
        elif 'quantity' in attr_name or 'stock' in attr_name:
            return random.randint(0, 100)
        elif 'price' in attr_name or 'amount' in attr_name:
            return random.randint(1, 1000)
        
        # 从约束推断范围
        if constraints:
            for constraint in constraints:
                if attr_name in constraint:
                    if '>' in constraint:
                        return random.randint(1, 100)
                    elif '<' in constraint:
                        return random.randint(0, 50)
        
        return random.randint(1, 100)
    
    def _generate_float(self, attr_name: str) -> float:
        """生成浮点数"""
        if 'price' in attr_name or 'cost' in attr_name:
            # 生成合理的价格
            base_prices = [9.99, 19.99, 29.99, 49.99, 99.99]
            return random.choice(base_prices)
        elif 'rate' in attr_name or 'percentage' in attr_name:
            return round(random.uniform(0, 1), 2)
        elif 'amount' in attr_name:
            return round(random.uniform(10, 500), 2)
        
        return round(random.uniform(0, 100), 2)
    
    def _generate_string(self, attr_name: str) -> str:
        """生成字符串"""
        if 'name' in attr_name:
            names = ['Alice', 'Bob', 'Charlie', 'David', 'Emma', 'Frank', 'Grace']
            return random.choice(names)
        elif 'email' in attr_name:
            return f"user{random.randint(1,100)}@example.com"
        elif 'status' in attr_name:
            return random.choice(['active', 'pending', 'completed', 'cancelled'])
        elif 'code' in attr_name:
            return f"CODE{random.randint(1000, 9999)}"
        elif 'description' in attr_name:
            return f"Description for {attr_name}"
        
        return f"{attr_name}_value"
    
    def _generate_date(self) -> str:
        """生成日期"""
        base = datetime.now()
        offset = timedelta(days=random.randint(-30, 30))
        return (base + offset).strftime('%Y-%m-%d')
    
    def _generate_collection(self, attr_name: str) -> List[Any]:
        """生成集合"""
        if 'permissions' in attr_name:
            all_perms = ['read', 'write', 'delete', 'admin']
            size = random.randint(1, len(all_perms))
            return random.sample(all_perms, size)
        elif 'items' in attr_name:
            return [f"item_{i}" for i in range(random.randint(1, 3))]
        elif 'tags' in attr_name:
            all_tags = ['important', 'urgent', 'review', 'approved', 'pending']
            size = random.randint(1, 3)
            return random.sample(all_tags, size)
        
        return [f"{attr_name}_{i}" for i in range(random.randint(1, 3))]


class TestGenerator:
    """主测试生成器"""
    
    def __init__(self):
        self.value_generator = ValueGenerator()
        self.evaluator = ExpressionEvaluator()
    
    def generate_tests(self, spec: DSLSpecification) -> List[Dict[str, Any]]:
        """生成测试用例"""
        all_tests = []
        
        for entity in spec.entities:
            logger.info(f"Generating tests for entity: {entity.name}")
            
            # 生成各种类型的测试
            tests = []
            tests.extend(self._generate_functional_tests(entity))
            tests.extend(self._generate_boundary_tests(entity))
            tests.extend(self._generate_negative_tests(entity))
            tests.extend(self._generate_constraint_tests(entity))
            
            # 为每个测试添加元信息
            for i, test in enumerate(tests):
                test['test_id'] = f"{entity.name}_test_{i+1}"
                test['entity'] = entity.name
                test['timestamp'] = datetime.now().isoformat()
            
            all_tests.extend(tests)
        
        return all_tests
    
    def _generate_functional_tests(self, entity: Entity) -> List[Dict[str, Any]]:
        """生成功能测试"""
        tests = []
        
        # 生成3个基本功能测试
        for i in range(3):
            test_data = self._generate_valid_data(entity)
            
            test = {
                'test_name': f"{entity.name}_functional_test_{i+1}",
                'test_type': 'functional',
                'description': f"Test basic functionality of {entity.name}",
                'test_data': test_data,
                'expected_result': 'pass',
                'priority': 8
            }
            tests.append(test)
        
        return tests
    
    def _generate_boundary_tests(self, entity: Entity) -> List[Dict[str, Any]]:
        """生成边界测试"""
        tests = []
        
        for attr in entity.attributes:
            if attr.type in ['int', 'float']:
                # 最小值测试
                min_data = self._generate_valid_data(entity)
                min_data[attr.name] = 0 if attr.type == 'int' else 0.01
                
                tests.append({
                    'test_name': f"{entity.name}_{attr.name}_min_boundary",
                    'test_type': 'boundary',
                    'description': f"Test minimum value for {attr.name}",
                    'test_data': min_data,
                    'expected_result': 'pass',
                    'priority': 7
                })
                
                # 最大值测试
                max_data = self._generate_valid_data(entity)
                max_data[attr.name] = 999999 if attr.type == 'int' else 999999.99
                
                tests.append({
                    'test_name': f"{entity.name}_{attr.name}_max_boundary",
                    'test_type': 'boundary',
                    'description': f"Test maximum value for {attr.name}",
                    'test_data': max_data,
                    'expected_result': 'pass',
                    'priority': 7
                })
        
        return tests[:4]  # 限制数量
    
    def _generate_negative_tests(self, entity: Entity) -> List[Dict[str, Any]]:
        """生成负面测试"""
        tests = []
        
        for attr in entity.attributes:
            # 类型错误测试
            invalid_data = self._generate_valid_data(entity)
            
            if attr.type == 'int':
                invalid_data[attr.name] = "not_a_number"
            elif attr.type == 'string':
                invalid_data[attr.name] = 12345
            elif attr.type == 'boolean':
                invalid_data[attr.name] = "yes"
            elif attr.is_collection:
                invalid_data[attr.name] = "not_an_array"
            
            tests.append({
                'test_name': f"{entity.name}_{attr.name}_type_error",
                'test_type': 'negative',
                'description': f"Test type error for {attr.name}",
                'test_data': invalid_data,
                'expected_result': 'fail',
                'expected_error': 'type_error',
                'priority': 6
            })
            
            # 空值测试（如果必需）
            if attr.required:
                null_data = self._generate_valid_data(entity)
                null_data[attr.name] = None
                
                tests.append({
                    'test_name': f"{entity.name}_{attr.name}_null_value",
                    'test_type': 'negative',
                    'description': f"Test null value for required field {attr.name}",
                    'test_data': null_data,
                    'expected_result': 'fail',
                    'expected_error': 'required_field_missing',
                    'priority': 6
                })
        
        return tests[:3]  # 限制数量
    
    def _generate_constraint_tests(self, entity: Entity) -> List[Dict[str, Any]]:
        """生成约束测试"""
        tests = []
        
        for constraint in entity.constraints:
            # 满足约束的测试
            valid_data = self._generate_constraint_satisfying_data(entity, constraint)
            tests.append({
                'test_name': f"{entity.name}_constraint_{constraint.id}_satisfied",
                'test_type': 'constraint_satisfaction',
                'description': f"Test constraint satisfaction: {constraint.expression}",
                'test_data': valid_data,
                'constraint': constraint.expression,
                'expected_result': 'pass',
                'priority': 8
            })
            
            # 违反约束的测试
            invalid_data = self._generate_constraint_violating_data(entity, constraint)
            tests.append({
                'test_name': f"{entity.name}_constraint_{constraint.id}_violated",
                'test_type': 'constraint_violation',
                'description': f"Test constraint violation: {constraint.expression}",
                'test_data': invalid_data,
                'constraint': constraint.expression,
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
            if attr.required or random.random() > 0.2:  # 80%概率包含可选字段
                constraints = [c.expression for c in entity.constraints 
                             if attr.name in c.expression]
                data[attr.name] = self.value_generator.generate(entity.name, attr, constraints)
        
        # 确保满足所有约束
        max_attempts = 10
        for _ in range(max_attempts):
            all_satisfied = True
            for constraint in entity.constraints:
                if not self.evaluator.evaluate(constraint.expression, data):
                    all_satisfied = False
                    # 尝试修复
                    self._fix_constraint_violation(data, constraint, entity)
                    break
            
            if all_satisfied:
                break
        
        return data
    
    def _generate_constraint_satisfying_data(self, entity: Entity, 
                                           constraint: Constraint) -> Dict[str, Any]:
        """生成满足特定约束的数据"""
        data = self._generate_valid_data(entity)
        
        # 针对特定约束类型调整数据
        expr = constraint.expression
        
        if '>' in expr:
            # 处理大于约束
            parts = expr.split('>')
            if len(parts) == 2:
                var = parts[0].strip()
                value = parts[1].strip()
                try:
                    if var in data:
                        if value.isdigit():
                            data[var] = int(value) + random.randint(1, 10)
                        else:
                            # 可能是比较两个字段
                            if value in data and isinstance(data[value], (int, float)):
                                data[var] = data[value] + random.randint(1, 10)
                except:
                    pass
        
        elif '<' in expr:
            # 处理小于约束
            parts = expr.split('<')
            if len(parts) == 2:
                var = parts[0].strip()
                value = parts[1].strip()
                try:
                    if var in data:
                        if value.isdigit():
                            data[var] = int(value) - random.randint(1, 10)
                        else:
                            if value in data and isinstance(data[value], (int, float)):
                                data[var] = data[value] - random.randint(1, 10)
                except:
                    pass
        
        return data
    
    def _generate_constraint_violating_data(self, entity: Entity, 
                                          constraint: Constraint) -> Dict[str, Any]:
        """生成违反特定约束的数据"""
        data = self._generate_valid_data(entity)
        
        # 故意违反约束
        expr = constraint.expression
        
        if '>' in expr:
            # 违反大于约束
            parts = expr.split('>')
            if len(parts) == 2:
                var = parts[0].strip()
                value = parts[1].strip()
                try:
                    if var in data:
                        if value.isdigit():
                            data[var] = int(value) - random.randint(1, 10)
                        else:
                            if value in data and isinstance(data[value], (int, float)):
                                data[var] = data[value] - random.randint(1, 10)
                except:
                    pass
        
        elif '<' in expr:
            # 违反小于约束
            parts = expr.split('<')
            if len(parts) == 2:
                var = parts[0].strip()
                value = parts[1].strip()
                try:
                    if var in data:
                        if value.isdigit():
                            data[var] = int(value) + random.randint(1, 10)
                        else:
                            if value in data and isinstance(data[value], (int, float)):
                                data[var] = data[value] + random.randint(1, 10)
                except:
                    pass
        
        elif '==' in expr:
            # 违反相等约束
            parts = expr.split('==')
            if len(parts) == 2:
                var = parts[0].strip()
                if var in data:
                    if isinstance(data[var], bool):
                        data[var] = not data[var]
                    elif isinstance(data[var], str):
                        data[var] = f"different_{data[var]}"
                    elif isinstance(data[var], (int, float)):
                        data[var] = data[var] + 1
        
        return data
    
    def _fix_constraint_violation(self, data: Dict[str, Any], 
                                constraint: Constraint, entity: Entity):
        """修复约束违反"""
        expr = constraint.expression
        
        # 简单的修复策略
        if 'price > cost' in expr:
            if 'price' in data and 'cost' in data:
                data['price'] = data['cost'] * 1.5
        elif 'total >= sum' in expr:
            if 'total' in data:
                data['total'] = random.randint(100, 500)
        elif '> 0' in expr:
            for key in data:
                if key in expr and isinstance(data[key], (int, float)):
                    data[key] = max(1, abs(data[key]))


def main():
    """主函数"""
    parser = argparse.ArgumentParser(description='V8 Simplified Test Generator')
    parser.add_argument('dsl_file', help='Path to DSL YAML file')
    parser.add_argument('-o', '--output', default='generated_tests.json',
                       help='Output file path')
    parser.add_argument('-v', '--verbose', action='store_true',
                       help='Enable verbose logging')
    
    args = parser.parse_args()
    
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)
    
    # 解析DSL
    yaml_parser = YAMLParser()
    spec = yaml_parser.parse_file(args.dsl_file)
    
    # 生成测试
    generator = TestGenerator()
    tests = generator.generate_tests(spec)
    
    # 保存结果
    output = {
        'dsl_file': args.dsl_file,
        'generation_time': datetime.now().isoformat(),
        'total_tests': len(tests),
        'tests': tests
    }
    
    with open(args.output, 'w', encoding='utf-8') as f:
        json.dump(output, f, indent=2, ensure_ascii=False)
    
    logger.info(f"Generated {len(tests)} tests")
    logger.info(f"Output saved to: {args.output}")
    
    # 打印统计
    test_types = {}
    for test in tests:
        test_type = test['test_type']
        test_types[test_type] = test_types.get(test_type, 0) + 1
    
    print("\nTest Statistics:")
    for test_type, count in test_types.items():
        print(f"  {test_type}: {count}")


if __name__ == '__main__':
    main()