"""
Improved Test Generator
改进的测试生成器主类 - 整合所有优化组件
"""

import logging
from typing import List, Dict, Any
from datetime import datetime
from ..v8.models import Entity, Test
from ..v8.value_generator import ValueGenerator
from ..v8.constraint_handler import ConstraintHandler
from ..v8.test_strategies import FunctionalTestStrategy, ConstraintTestStrategy
from .negative_test_strategy import ImprovedNegativeTestStrategy
from .boundary_test_strategy import ImprovedBoundaryTestStrategy
from .constraint_validator import ConstraintValidator
from .enhanced_constraint_solver import EnhancedConstraintSolver
from .type_aware_value_generator import TypeAwareValueGenerator

logger = logging.getLogger(__name__)


class ImprovedTestGenerator:
    """改进的测试生成器"""
    
    def __init__(self):
        self.value_generator = ValueGenerator()
        self.type_aware_generator = TypeAwareValueGenerator()
        self.constraint_handler = ConstraintHandler()
        self.validator = ConstraintValidator()
        self.constraint_solver = EnhancedConstraintSolver()
        
        # 初始化测试策略
        self.strategies = {
            'functional': FunctionalTestStrategy(self.value_generator, self.constraint_handler),
            'boundary': ImprovedBoundaryTestStrategy(self.value_generator, self.constraint_handler),
            'negative': ImprovedNegativeTestStrategy(self.value_generator, self.constraint_handler),
            'constraint': ConstraintTestStrategy(self.value_generator, self.constraint_handler)
        }
    
    def generate_tests(self, entities: List[Entity]) -> List[Dict[str, Any]]:
        """生成测试用例"""
        all_tests = []
        
        for entity in entities:
            logger.info(f"Generating tests for entity: {entity.name}")
            
            # 使用改进的策略生成测试
            tests = []
            
            # 功能测试 - 使用约束求解器生成
            functional_tests = self._generate_functional_tests(entity, count=3)
            tests.extend(functional_tests)
            
            # 边界测试 - 使用改进的边界策略
            boundary_tests = self.strategies['boundary'].generate(entity, count=2)
            tests.extend(boundary_tests)
            
            # 负面测试 - 使用改进的负面策略
            negative_tests = self.strategies['negative'].generate(entity, count=2)
            tests.extend(negative_tests)
            
            # 约束测试
            constraint_tests = self._generate_constraint_tests(entity)
            tests.extend(constraint_tests)
            
            # 验证并修复所有测试
            validated_tests = self._validate_and_fix_tests(tests, entity)
            
            # 为每个测试添加元信息
            for i, test in enumerate(validated_tests):
                test.test_id = f"{entity.name}_test_{i+1}"
                test.entity = entity.name
                test.timestamp = datetime.now().isoformat()
                
                # 转换为字典格式
                test_dict = self._test_to_dict(test)
                all_tests.append(test_dict)
        
        return all_tests
    
    def _generate_functional_tests(self, entity: Entity, count: int = 3) -> List[Test]:
        """使用约束求解器生成功能测试"""
        tests = []
        
        # 准备变量定义
        variables = {}
        for attr in entity.attributes:
            var_info = {
                'type': self._map_attr_type_to_solver_type(attr.type),
                'is_collection': attr.is_collection  # 添加集合标记
            }
            
            # 添加范围信息
            # Note: min_value and max_value are not part of the v8 models
            # Range constraints should be extracted from entity constraints instead
            # 对于ID等特殊字段，设置默认范围
            if 'id' in attr.name.lower():
                var_info['range'] = [1, 999999]
            elif 'price' in attr.name.lower() or 'amount' in attr.name.lower():
                var_info['range'] = [0.01, 999999.99]
            elif 'percentage' in attr.name.lower():
                var_info['range'] = [0, 100]
            
            # 添加选项信息
            if attr.enum:
                var_info['options'] = attr.enum
            
            variables[attr.name] = var_info
        
        # 使用约束求解器生成解
        solutions = self.constraint_solver.solve(
            entity.constraints or [],
            variables,
            num_solutions=count,
            entity_name=entity.name
        )
        
        # 将解转换为测试用例
        for i, solution in enumerate(solutions):
            # 补充缺失的属性
            test_data = self._complete_test_data(solution, entity)
            
            test = Test(
                test_name=f"{entity.name}_functional_{i+1}",
                test_type="functional",
                description=f"Test basic functionality of {entity.name}",
                test_data=test_data,
                expected_result="pass",
                priority=8
            )
            tests.append(test)
        
        return tests
    
    def _generate_constraint_tests(self, entity: Entity) -> List[Test]:
        """生成约束满足测试"""
        tests = []
        
        # 为每个有隐式约束的属性生成测试
        for attr in entity.attributes:
            # Generate tests based on type constraints
            if attr.type in ['integer', 'real', 'float'] and attr.required:
                # Generate positive value test
                test_data = self._generate_base_test_data(entity)
                test_data[attr.name] = 10 if attr.type == 'integer' else 10.0
                
                test = Test(
                    test_name=f"{entity.name}_{attr.name}_positive_value",
                    test_type="constraint_satisfaction",
                    description=f"Test positive value for {attr.name}",
                    test_data=test_data,
                    expected_result="pass",
                    constraint=f"{attr.name} > 0",
                    priority=7
                )
                tests.append(test)
        
        return tests
    
    def _validate_and_fix_tests(self, tests: List[Test], entity: Entity) -> List[Test]:
        """验证并修复测试用例"""
        validated_tests = []
        
        for test in tests:
            # 验证测试数据
            is_valid, violations = self.validator.validate_test_data(
                test.test_data,
                entity,
                test.test_type
            )
            
            if is_valid:
                validated_tests.append(test)
            else:
                # 尝试修复
                if test.test_type != 'negative':
                    # 非负面测试应该满足所有约束
                    fixed_data = self.validator.fix_constraint_violations(
                        test.test_data,
                        violations,
                        entity
                    )
                    
                    # 再次验证
                    is_valid_after_fix, _ = self.validator.validate_test_data(
                        fixed_data,
                        entity,
                        test.test_type
                    )
                    
                    if is_valid_after_fix:
                        test.test_data = fixed_data
                        validated_tests.append(test)
                    else:
                        logger.warning(f"Could not fix test {test.test_name}, skipping")
                else:
                    # 负面测试应该违反约束
                    if violations:
                        validated_tests.append(test)
                    else:
                        logger.warning(f"Negative test {test.test_name} does not violate constraints, skipping")
        
        return validated_tests
    
    def _generate_base_test_data(self, entity: Entity) -> Dict[str, Any]:
        """生成基础测试数据"""
        test_data = {}
        
        for attr in entity.attributes:
            test_data[attr.name] = self.value_generator.generate(entity.name, attr)
        
        return test_data
    
    def _complete_test_data(self, partial_data: Dict[str, Any], entity: Entity) -> Dict[str, Any]:
        """补充缺失的属性值"""
        complete_data = partial_data.copy()
        
        for attr in entity.attributes:
            if attr.name not in complete_data:
                # 使用类型感知生成器生成缺失的值
                complete_data[attr.name] = self.type_aware_generator.generate_value(entity, attr)
        
        return complete_data
    
    def _map_attr_type_to_solver_type(self, attr_type: str) -> str:
        """将属性类型映射到求解器类型"""
        if attr_type == 'integer':
            return 'int'
        elif attr_type in ['real', 'float']:
            return 'float'
        elif attr_type == 'boolean':
            return 'bool'
        elif attr_type == 'string':
            return 'string'
        else:
            return 'int'  # 默认
    
    def _test_to_dict(self, test: Test) -> Dict[str, Any]:
        """将测试对象转换为字典"""
        test_dict = {
            'test_id': test.test_id,
            'test_name': test.test_name,
            'test_type': test.test_type,
            'description': test.description,
            'test_data': test.test_data,
            'expected_result': test.expected_result,
            'priority': test.priority,
            'entity': test.entity,
            'timestamp': test.timestamp
        }
        
        # 添加可选字段
        if test.constraint:
            test_dict['constraint'] = test.constraint
        if test.expected_error:
            test_dict['expected_error'] = test.expected_error
        
        return test_dict
    
    def generate_test_suite(self, entities: List[Entity], config: Dict[str, Any] = None) -> Dict[str, Any]:
        """生成完整的测试套件"""
        tests = self.generate_tests(entities)
        
        # 构建测试套件
        test_suite = {
            'generation_time': datetime.now().isoformat(),
            'generator_version': 'v8_improved',
            'total_tests': len(tests),
            'entities': [entity.name for entity in entities],
            'tests': tests
        }
        
        # 添加配置信息
        if config:
            test_suite['config'] = config
        
        # 添加统计信息
        test_types = {}
        constraint_satisfied = 0
        constraint_violated = 0
        
        for test in tests:
            test_type = test['test_type']
            test_types[test_type] = test_types.get(test_type, 0) + 1
            
            # 统计约束满足情况
            if test_type == 'negative':
                constraint_violated += 1
            else:
                constraint_satisfied += 1
        
        test_suite['statistics'] = {
            'by_type': test_types,
            'by_entity': {
                entity.name: len([t for t in tests if t['entity'] == entity.name])
                for entity in entities
            },
            'constraint_satisfaction': {
                'satisfied': constraint_satisfied,
                'violated': constraint_violated
            }
        }
        
        # 添加质量报告
        quality_report = self._generate_quality_report(tests, entities)
        test_suite['quality_report'] = quality_report
        
        return test_suite
    
    def _generate_quality_report(self, tests: List[Dict[str, Any]], entities: List[Entity]) -> Dict[str, Any]:
        """生成质量报告"""
        report = {
            'total_tests': len(tests),
            'test_types': {},
            'constraint_coverage': {},
            'boundary_coverage': {},
            'issues': []
        }
        
        # 分析测试类型分布
        for test in tests:
            test_type = test['test_type']
            if test_type not in report['test_types']:
                report['test_types'][test_type] = 0
            report['test_types'][test_type] += 1
        
        # 分析约束覆盖
        for entity in entities:
            if entity.constraints:
                report['constraint_coverage'][entity.name] = {
                    'total_constraints': len(entity.constraints),
                    'covered': len([t for t in tests if t['entity'] == entity.name and 'constraint' in t])
                }
        
        # 分析边界覆盖
        for entity in entities:
            boundary_attrs = [attr for attr in entity.attributes 
                            if attr.type in ['integer', 'real', 'float']]
            if boundary_attrs:
                boundary_tests = [t for t in tests 
                                if t['entity'] == entity.name and t['test_type'] == 'boundary']
                report['boundary_coverage'][entity.name] = {
                    'total_boundaries': len(boundary_attrs) * 2,  # min和max
                    'covered': len(boundary_tests)
                }
        
        return report