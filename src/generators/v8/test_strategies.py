"""
Test Strategy Module
测试生成策略
"""

import random
from abc import ABC, abstractmethod
from typing import Any, Dict, List
from datetime import datetime
from .models import Entity, Test, Attribute
from .value_generator import ValueGenerator
from .constraint_handler import ConstraintHandler


class TestStrategy(ABC):
    """测试策略基类"""
    
    def __init__(self, value_generator: ValueGenerator, constraint_handler: ConstraintHandler):
        self.value_generator = value_generator
        self.constraint_handler = constraint_handler
    
    @abstractmethod
    def generate(self, entity: Entity) -> List[Test]:
        """生成测试用例"""
        pass
    
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


class FunctionalTestStrategy(TestStrategy):
    """功能测试策略"""
    
    def generate(self, entity: Entity, count: int = 3) -> List[Test]:
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
            
            test = Test(
                test_name=f"{entity.name}_functional_{i+1}",
                test_type='functional',
                description=f"Test basic functionality of {entity.name}",
                test_data=data,
                expected_result='pass',
                priority=8
            )
            tests.append(test)
        
        return tests


class BoundaryTestStrategy(TestStrategy):
    """边界测试策略"""
    
    def generate(self, entity: Entity, count: int = 2) -> List[Test]:
        """生成边界测试"""
        tests = []
        
        # 数值类型边界测试
        numeric_attrs = [attr for attr in entity.attributes 
                        if attr.type in ['int', 'integer', 'float', 'double'] and not attr.is_collection]
        
        for attr in numeric_attrs[:count]:
            # 最小值测试
            min_data = self._generate_valid_data(entity)
            min_data[attr.name] = 0 if 'int' in attr.type else 0.01
            
            tests.append(Test(
                test_name=f"{entity.name}_{attr.name}_min_boundary",
                test_type='boundary',
                description=f"Test minimum boundary for {attr.name}",
                test_data=min_data,
                expected_result='pass',
                priority=7
            ))
            
            # 最大值测试
            max_data = self._generate_valid_data(entity)
            max_data[attr.name] = 999999 if 'int' in attr.type else 999999.99
            
            tests.append(Test(
                test_name=f"{entity.name}_{attr.name}_max_boundary",
                test_type='boundary',
                description=f"Test maximum boundary for {attr.name}",
                test_data=max_data,
                expected_result='pass',
                priority=7
            ))
        
        # 集合类型边界测试
        collection_attrs = [attr for attr in entity.attributes if attr.is_collection]
        
        for attr in collection_attrs[:1]:  # 只测试一个集合
            # 空集合测试
            empty_data = self._generate_valid_data(entity)
            empty_data[attr.name] = []
            
            tests.append(Test(
                test_name=f"{entity.name}_{attr.name}_empty_collection",
                test_type='boundary',
                description=f"Test empty collection for {attr.name}",
                test_data=empty_data,
                expected_result='pass',
                priority=7
            ))
            
            # 大集合测试
            large_data = self._generate_valid_data(entity)
            if 'items' in attr.name:
                large_data[attr.name] = [random.randint(1001, 1050) for _ in range(10)]
            else:
                large_data[attr.name] = [f"{attr.name}_{i}" for i in range(10)]
            
            tests.append(Test(
                test_name=f"{entity.name}_{attr.name}_large_collection",
                test_type='boundary',
                description=f"Test large collection for {attr.name}",
                test_data=large_data,
                expected_result='pass',
                priority=7
            ))
        
        return tests


class NegativeTestStrategy(TestStrategy):
    """负面测试策略"""
    
    def generate(self, entity: Entity, count: int = 2) -> List[Test]:
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
            
            tests.append(Test(
                test_name=f"{entity.name}_{attr.name}_invalid_type",
                test_type='negative',
                description=f"Test invalid type for {attr.name}",
                test_data=invalid_data,
                expected_result='fail',
                expected_error='type_error',
                priority=6
            ))
        
        return tests


class ConstraintTestStrategy(TestStrategy):
    """约束测试策略"""
    
    def generate(self, entity: Entity) -> List[Test]:
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
                    
                    tests.append(Test(
                        test_name=f"{entity.name}_{attr.name}_positive_constraint",
                        test_type='constraint_satisfaction',
                        description=f"Test implicit positive constraint for {attr.name}",
                        test_data=positive_data,
                        constraint=f"{attr.name} >= 0",
                        expected_result='pass',
                        priority=6
                    ))
                    break  # 只添加一个
        
        # 显式约束测试
        for i, constraint in enumerate(entity.constraints):
            # 满足约束的测试
            valid_data = self._generate_constraint_satisfying_data(entity, constraint)
            tests.append(Test(
                test_name=f"{entity.name}_constraint_{i+1}_satisfied",
                test_type='constraint_satisfaction',
                description=f"Test constraint satisfaction: {constraint}",
                test_data=valid_data,
                constraint=constraint,
                expected_result='pass',
                priority=8
            ))
            
            # 违反约束的测试
            invalid_data = self._generate_constraint_violating_data(entity, constraint)
            tests.append(Test(
                test_name=f"{entity.name}_constraint_{i+1}_violated",
                test_type='constraint_violation',
                description=f"Test constraint violation: {constraint}",
                test_data=invalid_data,
                constraint=constraint,
                expected_result='fail',
                expected_error='constraint_violation',
                priority=7
            ))
        
        return tests
    
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