"""
Core Test Generator Module
主测试生成器
"""

import logging
from typing import List, Dict, Any
from datetime import datetime
from .models import Entity, Test
from .value_generator import ValueGenerator
from .constraint_handler import ConstraintHandler
from .test_strategies import (
    FunctionalTestStrategy,
    BoundaryTestStrategy,
    NegativeTestStrategy,
    ConstraintTestStrategy
)

logger = logging.getLogger(__name__)


class TestGenerator:
    """主测试生成器"""
    
    def __init__(self):
        self.value_generator = ValueGenerator()
        self.constraint_handler = ConstraintHandler()
        
        # 初始化测试策略
        self.strategies = {
            'functional': FunctionalTestStrategy(self.value_generator, self.constraint_handler),
            'boundary': BoundaryTestStrategy(self.value_generator, self.constraint_handler),
            'negative': NegativeTestStrategy(self.value_generator, self.constraint_handler),
            'constraint': ConstraintTestStrategy(self.value_generator, self.constraint_handler)
        }
    
    def generate_tests(self, entities: List[Entity]) -> List[Dict[str, Any]]:
        """生成测试用例"""
        all_tests = []
        
        for entity in entities:
            logger.info(f"Generating tests for entity: {entity.name}")
            
            # 使用各种策略生成测试
            tests = []
            
            # 功能测试
            tests.extend(self.strategies['functional'].generate(entity, count=3))
            
            # 边界测试
            tests.extend(self.strategies['boundary'].generate(entity, count=2))
            
            # 负面测试
            tests.extend(self.strategies['negative'].generate(entity, count=2))
            
            # 约束测试
            tests.extend(self.strategies['constraint'].generate(entity))
            
            # 为每个测试添加元信息
            for i, test in enumerate(tests):
                test.test_id = f"{entity.name}_test_{i+1}"
                test.entity = entity.name
                test.timestamp = datetime.now().isoformat()
                
                # 转换为字典格式
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
                
                all_tests.append(test_dict)
        
        return all_tests
    
    def generate_test_suite(self, entities: List[Entity], config: Dict[str, Any] = None) -> Dict[str, Any]:
        """生成完整的测试套件"""
        tests = self.generate_tests(entities)
        
        # 构建测试套件
        test_suite = {
            'generation_time': datetime.now().isoformat(),
            'total_tests': len(tests),
            'entities': [entity.name for entity in entities],
            'tests': tests
        }
        
        # 添加配置信息
        if config:
            test_suite['config'] = config
        
        # 添加统计信息
        test_types = {}
        for test in tests:
            test_type = test['test_type']
            test_types[test_type] = test_types.get(test_type, 0) + 1
        
        test_suite['statistics'] = {
            'by_type': test_types,
            'by_entity': {
                entity.name: len([t for t in tests if t['entity'] == entity.name])
                for entity in entities
            }
        }
        
        return test_suite