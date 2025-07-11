"""
Test Strategy Module - V8
高级测试生成策略，包括属性基测试和智能策略选择
"""

from abc import ABC, abstractmethod
from typing import Any, Dict, List, Optional, Set, Tuple
import random
from enum import Enum
import itertools
import logging

logger = logging.getLogger(__name__)


class TestType(Enum):
    """测试类型枚举"""
    FUNCTIONAL = "functional"
    BOUNDARY = "boundary"
    NEGATIVE = "negative"
    CONSTRAINT_SATISFACTION = "constraint_satisfaction"
    CONSTRAINT_VIOLATION = "constraint_violation"
    RULE_ACTIVATION = "rule_activation"
    RULE_DEACTIVATION = "rule_deactivation"
    COLLECTION_EMPTY = "collection_empty"
    COLLECTION_SINGLE = "collection_single"
    COLLECTION_MULTIPLE = "collection_multiple"
    COMBINATORIAL = "combinatorial"
    STATE_TRANSITION = "state_transition"
    SCENARIO = "scenario"
    PROPERTY_BASED = "property_based"
    METAMORPHIC = "metamorphic"
    SECURITY = "security"
    PERFORMANCE = "performance"


class TestStrategy(ABC):
    """测试策略基类"""
    
    @abstractmethod
    def generate_tests(self, entity: Dict[str, Any], context: Dict[str, Any]) -> List[Dict[str, Any]]:
        """生成测试用例"""
        pass
    
    @abstractmethod
    def get_test_type(self) -> TestType:
        """返回测试类型"""
        pass
    
    @abstractmethod
    def estimate_priority(self, entity: Dict[str, Any]) -> int:
        """估算测试优先级 (1-10)"""
        pass


class PropertyBasedTestStrategy(TestStrategy):
    """
    属性基测试策略
    生成验证系统不变性和属性的测试
    """
    
    def __init__(self):
        self.properties = {
            'idempotence': self._test_idempotence,
            'commutativity': self._test_commutativity,
            'associativity': self._test_associativity,
            'invariants': self._test_invariants,
            'monotonicity': self._test_monotonicity
        }
    
    def generate_tests(self, entity: Dict[str, Any], context: Dict[str, Any]) -> List[Dict[str, Any]]:
        tests = []
        
        # 识别适用的属性
        applicable_properties = self._identify_applicable_properties(entity, context)
        
        for prop_name in applicable_properties:
            if prop_name in self.properties:
                prop_tests = self.properties[prop_name](entity, context)
                tests.extend(prop_tests)
        
        return tests
    
    def get_test_type(self) -> TestType:
        return TestType.PROPERTY_BASED
    
    def estimate_priority(self, entity: Dict[str, Any]) -> int:
        # 属性基测试对于有复杂约束的实体优先级更高
        constraints = entity.get('constraints', [])
        if len(constraints) > 5:
            return 9
        elif len(constraints) > 2:
            return 7
        return 5
    
    def _identify_applicable_properties(self, entity: Dict[str, Any], 
                                       context: Dict[str, Any]) -> List[str]:
        """识别适用的属性测试"""
        properties = []
        
        # 检查幂等性（适用于更新操作）
        if self._has_update_operations(entity):
            properties.append('idempotence')
        
        # 检查不变量（适用于有约束的实体）
        if entity.get('constraints'):
            properties.append('invariants')
        
        # 检查单调性（适用于数值属性）
        if self._has_numeric_attributes(entity):
            properties.append('monotonicity')
        
        return properties
    
    def _test_idempotence(self, entity: Dict[str, Any], context: Dict[str, Any]) -> List[Dict[str, Any]]:
        """测试幂等性：f(f(x)) = f(x)"""
        tests = []
        
        # 生成基础数据
        base_data = self._generate_base_data(entity)
        
        # 创建幂等性测试
        test = {
            'test_name': f"{entity['name']}_idempotence_test",
            'test_type': 'property_based_idempotence',
            'description': f"Verify idempotence property for {entity['name']}",
            'test_data': base_data,
            'property': 'idempotence',
            'operations': [
                {'action': 'update', 'data': base_data},
                {'action': 'update', 'data': base_data}
            ],
            'expected_result': 'Same result after repeated operations',
            'priority': 7
        }
        tests.append(test)
        
        return tests
    
    def _test_invariants(self, entity: Dict[str, Any], context: Dict[str, Any]) -> List[Dict[str, Any]]:
        """测试不变量：在所有操作后约束始终成立"""
        tests = []
        
        for constraint in entity.get('constraints', []):
            # 生成满足约束的数据
            valid_data = self._generate_constraint_satisfying_data(entity, constraint)
            
            # 创建不变量测试
            test = {
                'test_name': f"{entity['name']}_invariant_{constraint['id']}_test",
                'test_type': 'property_based_invariant',
                'description': f"Verify invariant '{constraint['expression']}' holds",
                'test_data': valid_data,
                'property': 'invariant',
                'invariant': constraint['expression'],
                'operations': self._generate_invariant_preserving_operations(entity, constraint),
                'expected_result': 'Constraint satisfied after all operations',
                'priority': 8
            }
            tests.append(test)
        
        return tests
    
    def _test_monotonicity(self, entity: Dict[str, Any], context: Dict[str, Any]) -> List[Dict[str, Any]]:
        """测试单调性：输入增加时输出也增加（或减少）"""
        tests = []
        
        numeric_attrs = self._get_numeric_attributes(entity)
        
        for attr in numeric_attrs:
            # 生成递增序列
            sequence = self._generate_monotonic_sequence(attr)
            
            test = {
                'test_name': f"{entity['name']}_{attr['name']}_monotonicity_test",
                'test_type': 'property_based_monotonicity',
                'description': f"Verify monotonicity for {attr['name']}",
                'test_sequence': sequence,
                'property': 'monotonicity',
                'attribute': attr['name'],
                'expected_behavior': 'monotonic_increase',
                'priority': 6
            }
            tests.append(test)
        
        return tests
    
    def _test_commutativity(self, entity: Dict[str, Any], context: Dict[str, Any]) -> List[Dict[str, Any]]:
        """测试交换律：f(a,b) = f(b,a)"""
        # 实现交换律测试
        return []
    
    def _test_associativity(self, entity: Dict[str, Any], context: Dict[str, Any]) -> List[Dict[str, Any]]:
        """测试结合律：f(f(a,b),c) = f(a,f(b,c))"""
        # 实现结合律测试
        return []
    
    # Helper methods
    def _has_update_operations(self, entity: Dict[str, Any]) -> bool:
        """检查实体是否有更新操作"""
        # 简化实现：检查属性是否可变
        return any(not attr.get('immutable', False) for attr in entity.get('attributes', []))
    
    def _has_numeric_attributes(self, entity: Dict[str, Any]) -> bool:
        """检查实体是否有数值属性"""
        return any(attr.get('type') in ['int', 'float', 'decimal'] 
                  for attr in entity.get('attributes', []))
    
    def _get_numeric_attributes(self, entity: Dict[str, Any]) -> List[Dict[str, Any]]:
        """获取数值属性"""
        return [attr for attr in entity.get('attributes', [])
                if attr.get('type') in ['int', 'float', 'decimal']]
    
    def _generate_base_data(self, entity: Dict[str, Any]) -> Dict[str, Any]:
        """生成基础测试数据"""
        # 简化实现
        return {attr['name']: f"{attr['name']}_value" 
                for attr in entity.get('attributes', [])}
    
    def _generate_constraint_satisfying_data(self, entity: Dict[str, Any], 
                                           constraint: Dict[str, Any]) -> Dict[str, Any]:
        """生成满足约束的数据"""
        # 简化实现
        return self._generate_base_data(entity)
    
    def _generate_invariant_preserving_operations(self, entity: Dict[str, Any], 
                                                constraint: Dict[str, Any]) -> List[Dict[str, Any]]:
        """生成保持不变量的操作序列"""
        # 简化实现
        return [
            {'action': 'create', 'preserve_constraint': True},
            {'action': 'update', 'preserve_constraint': True},
            {'action': 'transform', 'preserve_constraint': True}
        ]
    
    def _generate_monotonic_sequence(self, attribute: Dict[str, Any]) -> List[Any]:
        """生成单调序列"""
        attr_type = attribute.get('type', 'int')
        
        if attr_type == 'int':
            return list(range(1, 11))
        elif attr_type == 'float':
            return [i * 0.5 for i in range(1, 11)]
        else:
            return []


class MetamorphicTestStrategy(TestStrategy):
    """
    蜕变测试策略
    通过输入变换验证输出关系
    """
    
    def generate_tests(self, entity: Dict[str, Any], context: Dict[str, Any]) -> List[Dict[str, Any]]:
        tests = []
        
        # 识别蜕变关系
        relations = self._identify_metamorphic_relations(entity)
        
        for relation in relations:
            base_input = self._generate_base_input(entity)
            transformed_input = self._apply_transformation(base_input, relation)
            
            test = {
                'test_name': f"{entity['name']}_{relation['name']}_metamorphic_test",
                'test_type': 'metamorphic',
                'description': f"Verify metamorphic relation: {relation['description']}",
                'base_input': base_input,
                'transformed_input': transformed_input,
                'relation': relation['formula'],
                'expected_relation': relation['expected'],
                'priority': 7
            }
            tests.append(test)
        
        return tests
    
    def get_test_type(self) -> TestType:
        return TestType.METAMORPHIC
    
    def estimate_priority(self, entity: Dict[str, Any]) -> int:
        # 蜕变测试对于有复杂计算的实体优先级更高
        if self._has_calculations(entity):
            return 8
        return 5
    
    def _identify_metamorphic_relations(self, entity: Dict[str, Any]) -> List[Dict[str, Any]]:
        """识别蜕变关系"""
        relations = []
        
        # 添加关系：输入翻倍
        if self._has_numeric_attributes(entity):
            relations.append({
                'name': 'input_doubling',
                'description': 'Doubling input values',
                'formula': 'f(2x) = 2*f(x) for linear operations',
                'transformation': lambda x: x * 2,
                'expected': 'proportional_output'
            })
        
        # 添加关系：输入排列
        if self._has_collection_attributes(entity):
            relations.append({
                'name': 'permutation',
                'description': 'Permuting collection elements',
                'formula': 'f(permute(x)) = f(x) for order-independent operations',
                'transformation': lambda x: random.sample(x, len(x)),
                'expected': 'same_output'
            })
        
        return relations
    
    def _has_calculations(self, entity: Dict[str, Any]) -> bool:
        """检查实体是否涉及计算"""
        # 简化实现：检查是否有数值属性和规则
        return (self._has_numeric_attributes(entity) and 
                len(entity.get('rules', [])) > 0)
    
    def _has_numeric_attributes(self, entity: Dict[str, Any]) -> bool:
        """检查是否有数值属性"""
        return any(attr.get('type') in ['int', 'float', 'decimal'] 
                  for attr in entity.get('attributes', []))
    
    def _has_collection_attributes(self, entity: Dict[str, Any]) -> bool:
        """检查是否有集合属性"""
        return any(attr.get('is_collection', False) 
                  for attr in entity.get('attributes', []))
    
    def _generate_base_input(self, entity: Dict[str, Any]) -> Dict[str, Any]:
        """生成基础输入"""
        return {attr['name']: self._generate_attribute_value(attr)
                for attr in entity.get('attributes', [])}
    
    def _generate_attribute_value(self, attribute: Dict[str, Any]) -> Any:
        """生成属性值"""
        attr_type = attribute.get('type', 'string')
        
        if attr_type == 'int':
            return random.randint(1, 100)
        elif attr_type == 'float':
            return round(random.uniform(1, 100), 2)
        elif attr_type == 'string':
            return f"{attribute['name']}_value"
        elif attribute.get('is_collection'):
            return [f"item_{i}" for i in range(3)]
        else:
            return None
    
    def _apply_transformation(self, base_input: Dict[str, Any], 
                            relation: Dict[str, Any]) -> Dict[str, Any]:
        """应用变换"""
        transform_func = relation.get('transformation', lambda x: x)
        transformed = {}
        
        for key, value in base_input.items():
            if isinstance(value, (int, float)):
                transformed[key] = transform_func(value)
            elif isinstance(value, list):
                transformed[key] = transform_func(value)
            else:
                transformed[key] = value
        
        return transformed


class SecurityTestStrategy(TestStrategy):
    """
    安全测试策略
    生成安全相关的测试用例
    """
    
    def generate_tests(self, entity: Dict[str, Any], context: Dict[str, Any]) -> List[Dict[str, Any]]:
        tests = []
        
        # SQL注入测试
        tests.extend(self._generate_sql_injection_tests(entity))
        
        # XSS测试
        tests.extend(self._generate_xss_tests(entity))
        
        # 权限越界测试
        tests.extend(self._generate_authorization_tests(entity))
        
        # 输入验证测试
        tests.extend(self._generate_input_validation_tests(entity))
        
        return tests
    
    def get_test_type(self) -> TestType:
        return TestType.SECURITY
    
    def estimate_priority(self, entity: Dict[str, Any]) -> int:
        # 安全测试始终高优先级
        return 9
    
    def _generate_sql_injection_tests(self, entity: Dict[str, Any]) -> List[Dict[str, Any]]:
        """生成SQL注入测试"""
        tests = []
        sql_payloads = [
            "' OR '1'='1",
            "'; DROP TABLE users; --",
            "1' UNION SELECT NULL--",
            "' OR 1=1--"
        ]
        
        string_attrs = [attr for attr in entity.get('attributes', [])
                       if attr.get('type') == 'string']
        
        for attr in string_attrs:
            for payload in sql_payloads:
                test = {
                    'test_name': f"{entity['name']}_{attr['name']}_sql_injection_test",
                    'test_type': 'security_sql_injection',
                    'description': f"Test SQL injection vulnerability in {attr['name']}",
                    'test_data': {attr['name']: payload},
                    'attack_type': 'sql_injection',
                    'expected_result': 'Input rejected or safely handled',
                    'priority': 9
                }
                tests.append(test)
        
        return tests[:3]  # 限制数量
    
    def _generate_xss_tests(self, entity: Dict[str, Any]) -> List[Dict[str, Any]]:
        """生成XSS测试"""
        tests = []
        xss_payloads = [
            "<script>alert('XSS')</script>",
            "<img src=x onerror=alert('XSS')>",
            "javascript:alert('XSS')"
        ]
        
        string_attrs = [attr for attr in entity.get('attributes', [])
                       if attr.get('type') == 'string']
        
        for attr in string_attrs[:2]:  # 限制测试数量
            for payload in xss_payloads[:2]:
                test = {
                    'test_name': f"{entity['name']}_{attr['name']}_xss_test",
                    'test_type': 'security_xss',
                    'description': f"Test XSS vulnerability in {attr['name']}",
                    'test_data': {attr['name']: payload},
                    'attack_type': 'xss',
                    'expected_result': 'Input sanitized or rejected',
                    'priority': 9
                }
                tests.append(test)
        
        return tests
    
    def _generate_authorization_tests(self, entity: Dict[str, Any]) -> List[Dict[str, Any]]:
        """生成授权测试"""
        tests = []
        
        # 检查是否有权限相关属性
        if any('permission' in attr.get('name', '').lower() or 
               'role' in attr.get('name', '').lower()
               for attr in entity.get('attributes', [])):
            
            test = {
                'test_name': f"{entity['name']}_unauthorized_access_test",
                'test_type': 'security_authorization',
                'description': f"Test unauthorized access to {entity['name']}",
                'test_scenarios': [
                    {'user_role': 'guest', 'action': 'read', 'expected': 'denied'},
                    {'user_role': 'guest', 'action': 'write', 'expected': 'denied'},
                    {'user_role': 'user', 'action': 'delete', 'expected': 'denied'}
                ],
                'priority': 9
            }
            tests.append(test)
        
        return tests
    
    def _generate_input_validation_tests(self, entity: Dict[str, Any]) -> List[Dict[str, Any]]:
        """生成输入验证测试"""
        tests = []
        
        # 缓冲区溢出测试
        for attr in entity.get('attributes', []):
            if attr.get('type') == 'string':
                test = {
                    'test_name': f"{entity['name']}_{attr['name']}_buffer_overflow_test",
                    'test_type': 'security_input_validation',
                    'description': f"Test buffer overflow in {attr['name']}",
                    'test_data': {attr['name']: 'A' * 10000},
                    'attack_type': 'buffer_overflow',
                    'expected_result': 'Input length validated',
                    'priority': 8
                }
                tests.append(test)
                break  # 只生成一个
        
        return tests


class TestStrategyFactory:
    """
    测试策略工厂
    负责创建和管理测试策略
    """
    
    def __init__(self):
        self.strategies = {
            TestType.PROPERTY_BASED: PropertyBasedTestStrategy(),
            TestType.METAMORPHIC: MetamorphicTestStrategy(),
            TestType.SECURITY: SecurityTestStrategy()
        }
        
        # 注册基础策略
        self._register_basic_strategies()
    
    def get_strategy(self, test_type: TestType) -> Optional[TestStrategy]:
        """获取指定类型的测试策略"""
        return self.strategies.get(test_type)
    
    def get_applicable_strategies(self, entity: Dict[str, Any], 
                                 context: Dict[str, Any]) -> List[TestStrategy]:
        """获取适用于实体的所有策略"""
        applicable = []
        
        for strategy in self.strategies.values():
            if self._is_strategy_applicable(strategy, entity, context):
                applicable.append(strategy)
        
        # 按优先级排序
        applicable.sort(key=lambda s: s.estimate_priority(entity), reverse=True)
        
        return applicable
    
    def generate_test_suite(self, entity: Dict[str, Any], 
                          context: Dict[str, Any],
                          max_tests_per_strategy: int = 10) -> List[Dict[str, Any]]:
        """生成完整的测试套件"""
        test_suite = []
        
        # 获取适用策略
        strategies = self.get_applicable_strategies(entity, context)
        
        for strategy in strategies:
            try:
                tests = strategy.generate_tests(entity, context)
                # 限制每种策略的测试数量
                test_suite.extend(tests[:max_tests_per_strategy])
            except Exception as e:
                logger.warning(f"Strategy {strategy.__class__.__name__} failed: {e}")
        
        return test_suite
    
    def _register_basic_strategies(self):
        """注册基础测试策略"""
        # 这里可以添加更多基础策略
        # 如：FunctionalTestStrategy, BoundaryTestStrategy等
        pass
    
    def _is_strategy_applicable(self, strategy: TestStrategy, 
                               entity: Dict[str, Any], 
                               context: Dict[str, Any]) -> bool:
        """检查策略是否适用于实体"""
        # 基于实体特征判断策略是否适用
        try:
            # 尝试生成测试，如果能生成则适用
            tests = strategy.generate_tests(entity, context)
            return len(tests) > 0
        except:
            return False