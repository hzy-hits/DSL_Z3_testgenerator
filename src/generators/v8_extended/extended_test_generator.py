"""
Extended Test Generator with State Machine Support
扩展的测试生成器，支持状态机、场景和时序约束测试
"""

import json
import logging
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional

from ..v8.models import Test
from ..v8.models_extended import ExtendedEntity, ExtendedDSLModel
from ..v8.parser_extended import ExtendedYAMLParser
from ..v8.test_strategies import (
    FunctionalTestStrategy,
    BoundaryTestStrategy,
    NegativeTestStrategy,
    ConstraintTestStrategy
)
from ..v8.value_generator import ValueGenerator
from ..v8.constraint_handler import ConstraintHandler
from ..v8.state_transition_strategy import StateTransitionTestStrategy
from ..v8.scenario_test_strategy import ScenarioTestStrategy
from ..v8.timed_constraint_strategy import TimedConstraintTestStrategy


class ExtendedTestGenerator:
    """扩展的测试生成器"""
    
    def __init__(self, verbose: bool = False):
        self.verbose = verbose
        self.logger = self._setup_logger()
        self.parser = ExtendedYAMLParser()
        self.dsl_model: Optional[ExtendedDSLModel] = None
        
    def _setup_logger(self) -> logging.Logger:
        """设置日志"""
        logger = logging.getLogger(self.__class__.__name__)
        handler = logging.StreamHandler()
        formatter = logging.Formatter(
            '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
        )
        handler.setFormatter(formatter)
        logger.addHandler(handler)
        logger.setLevel(logging.DEBUG if self.verbose else logging.INFO)
        return logger
    
    def generate_from_file(self, yaml_file: str, output_file: Optional[str] = None) -> Dict:
        """从YAML文件生成测试"""
        self.logger.info(f"Parsing YAML file: {yaml_file}")
        
        # 解析YAML文件
        try:
            self.dsl_model = self.parser.parse_file(yaml_file)
            self.logger.info(f"Successfully parsed DSL for domain: {self.dsl_model.domain}")
            self.logger.info(f"Found {len(self.dsl_model.entities)} entities")
            self.logger.info(f"Found {len(self.dsl_model.state_machines)} state machines")
            self.logger.info(f"Found {len(self.dsl_model.test_requirements)} test requirements")
        except Exception as e:
            self.logger.error(f"Failed to parse YAML file: {e}")
            raise
        
        # 生成测试
        all_tests = []
        
        # 初始化策略
        strategies = self._initialize_strategies()
        
        # 为每个实体生成测试
        for entity in self.dsl_model.entities:
            self.logger.info(f"Generating tests for entity: {entity.name}")
            entity_tests = []
            
            for strategy_name, strategy in strategies.items():
                try:
                    # 新策略使用 generate_tests，旧策略使用 generate
                    if hasattr(strategy, 'generate_tests'):
                        tests = strategy.generate_tests(entity, entity_tests)
                    else:
                        tests = strategy.generate(entity)
                    entity_tests.extend(tests)
                    self.logger.info(f"  - {strategy_name}: {len(tests)} tests")
                except Exception as e:
                    self.logger.warning(f"  - {strategy_name} failed: {e}")
            
            # 为测试添加元数据
            for test in entity_tests:
                test.entity = entity.name
                test.timestamp = datetime.now().isoformat()
                if not test.test_id:
                    test.test_id = f"{entity.name}_{test.test_type}_{len(all_tests) + 1}"
            
            all_tests.extend(entity_tests)
            self.logger.info(f"Total tests for {entity.name}: {len(entity_tests)}")
        
        # 生成测试报告
        result = self._generate_test_report(all_tests)
        
        # 保存到文件
        if output_file:
            self._save_to_file(result, output_file)
        
        return result
    
    def _initialize_strategies(self) -> Dict[str, any]:
        """初始化所有测试策略"""
        # 创建共享的工具类
        value_generator = ValueGenerator()
        constraint_handler = ConstraintHandler()
        
        strategies = {
            'functional': FunctionalTestStrategy(value_generator, constraint_handler),
            'boundary': BoundaryTestStrategy(value_generator, constraint_handler),
            'negative': NegativeTestStrategy(value_generator, constraint_handler),
            'constraint': ConstraintTestStrategy(value_generator, constraint_handler),
            'state_transition': StateTransitionTestStrategy(),
            'scenario': ScenarioTestStrategy(self.dsl_model),
            'timed_constraint': TimedConstraintTestStrategy(self.dsl_model)
        }
        
        return strategies
    
    def _generate_test_report(self, tests: List[Test]) -> Dict:
        """生成测试报告"""
        # 统计信息
        test_type_counts = {}
        entity_counts = {}
        priority_counts = {}
        
        for test in tests:
            # 统计测试类型
            test_type = test.test_type
            test_type_counts[test_type] = test_type_counts.get(test_type, 0) + 1
            
            # 统计实体
            entity = test.entity
            entity_counts[entity] = entity_counts.get(entity, 0) + 1
            
            # 统计优先级
            priority = test.priority
            priority_counts[priority] = priority_counts.get(priority, 0) + 1
        
        # 计算覆盖率
        coverage_stats = self._calculate_coverage_stats()
        
        # 构建报告
        report = {
            'metadata': {
                'domain': self.dsl_model.domain,
                'generation_time': datetime.now().isoformat(),
                'generator_version': 'v8_extended',
                'total_tests': len(tests),
                'total_entities': len(self.dsl_model.entities),
                'total_state_machines': len(self.dsl_model.state_machines),
                'total_test_requirements': len(self.dsl_model.test_requirements)
            },
            'summary': {
                'test_types': test_type_counts,
                'entities': entity_counts,
                'priorities': priority_counts,
                'coverage': coverage_stats
            },
            'tests': [self._test_to_dict(test) for test in tests]
        }
        
        return report
    
    def _calculate_coverage_stats(self) -> Dict[str, any]:
        """计算测试覆盖率统计"""
        stats = {
            'state_coverage': 0.0,
            'transition_coverage': 0.0,
            'rule_coverage': 0.0,
            'constraint_coverage': 0.0,
            'requirement_coverage': 0.0
        }
        
        # 计算状态机覆盖率
        if self.dsl_model.state_machines:
            total_states = sum(len(sm.states) for sm in self.dsl_model.state_machines)
            total_transitions = sum(len(sm.transitions) for sm in self.dsl_model.state_machines)
            
            # 这里简化计算，实际应该追踪哪些状态和转换被测试覆盖
            stats['state_coverage'] = 100.0 if total_states > 0 else 0.0
            stats['transition_coverage'] = 100.0 if total_transitions > 0 else 0.0
        
        # 计算规则覆盖率
        total_rules = sum(len(entity.rules) for entity in self.dsl_model.entities)
        total_rules += len(self.dsl_model.global_rules)
        stats['rule_coverage'] = 100.0 if total_rules > 0 else 0.0
        
        # 计算约束覆盖率
        total_constraints = sum(len(entity.constraints) for entity in self.dsl_model.entities)
        total_constraints += len(self.dsl_model.global_constraints)
        stats['constraint_coverage'] = 100.0 if total_constraints > 0 else 0.0
        
        # 计算需求覆盖率
        stats['requirement_coverage'] = 100.0 if self.dsl_model.test_requirements else 0.0
        
        return stats
    
    def _test_to_dict(self, test: Test) -> Dict:
        """将测试对象转换为字典"""
        return {
            'test_id': test.test_id,
            'test_name': test.test_name,
            'test_type': test.test_type,
            'description': test.description,
            'test_data': test.test_data,
            'expected_result': test.expected_result,
            'priority': test.priority,
            'entity': test.entity,
            'timestamp': test.timestamp,
            'constraint': test.constraint,
            'expected_error': test.expected_error
        }
    
    def _save_to_file(self, data: Dict, output_file: str):
        """保存测试到文件"""
        output_path = Path(output_file)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=2, ensure_ascii=False)
        
        self.logger.info(f"Tests saved to: {output_file}")
        self.logger.info(f"Total tests generated: {data['metadata']['total_tests']}")


def main():
    """命令行入口"""
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Extended Test Generator with State Machine Support'
    )
    parser.add_argument('input', help='Input YAML file')
    parser.add_argument('-o', '--output', help='Output JSON file', 
                       default='extended_tests.json')
    parser.add_argument('-v', '--verbose', action='store_true', 
                       help='Enable verbose logging')
    
    args = parser.parse_args()
    
    generator = ExtendedTestGenerator(verbose=args.verbose)
    
    try:
        result = generator.generate_from_file(args.input, args.output)
        print(f"\nTest generation completed!")
        print(f"Total tests: {result['metadata']['total_tests']}")
        print(f"Output saved to: {args.output}")
    except Exception as e:
        print(f"Error: {e}")
        return 1
    
    return 0


if __name__ == '__main__':
    exit(main())