"""
Timed Constraint Test Strategy
时序约束测试策略 - 测试时间相关的约束和规则
"""

from typing import List, Dict, Any, Optional, Tuple
from .models import Test
from .models_extended import ExtendedEntity, ExtendedDSLModel, TimedConstraint, TestRequirement
from abc import ABC
from .value_generator import ValueGenerator
import re


class TimedConstraintTestStrategy:
    """时序约束测试策略"""
    
    def __init__(self, dsl_model: Optional[ExtendedDSLModel] = None):
        self.value_generator = ValueGenerator()
        self.dsl_model = dsl_model
    
    def generate_tests(self, entity: ExtendedEntity, existing_tests: List[Test]) -> List[Test]:
        """生成时序约束测试"""
        tests = []
        
        # 1. 基于显式时序约束生成测试
        tests.extend(self._generate_explicit_timed_tests(entity))
        
        # 2. 基于时间相关规则生成测试
        tests.extend(self._generate_rule_based_timed_tests(entity))
        
        # 3. 基于时间窗口的边界测试
        tests.extend(self._generate_time_boundary_tests(entity))
        
        # 4. 生成并发时序测试
        tests.extend(self._generate_concurrent_timing_tests(entity))
        
        # 5. 生成时间累积效应测试
        tests.extend(self._generate_cumulative_timing_tests(entity))
        
        return tests
    
    def _generate_explicit_timed_tests(self, entity: ExtendedEntity) -> List[Test]:
        """基于显式时序约束生成测试"""
        tests = []
        
        # 处理实体的时序约束
        for constraint in entity.timed_constraints:
            # 测试在时间窗口内满足约束
            tests.append(self._create_within_window_test(entity, constraint))
            
            # 测试在时间窗口外违反约束
            tests.append(self._create_outside_window_test(entity, constraint))
            
            # 测试时间窗口边界
            tests.append(self._create_window_boundary_test(entity, constraint))
        
        return tests
    
    def _generate_rule_based_timed_tests(self, entity: ExtendedEntity) -> List[Test]:
        """基于包含时间条件的规则生成测试"""
        tests = []
        
        # 分析规则中的时间条件
        time_rules = self._extract_time_related_rules(entity)
        
        for rule in time_rules:
            time_conditions = self._extract_time_conditions(rule)
            
            for condition_type, time_value, attribute in time_conditions:
                # 测试满足时间条件
                tests.append(self._create_time_condition_satisfied_test(
                    entity, rule, condition_type, time_value, attribute
                ))
                
                # 测试不满足时间条件
                tests.append(self._create_time_condition_violated_test(
                    entity, rule, condition_type, time_value, attribute
                ))
        
        return tests
    
    def _generate_time_boundary_tests(self, entity: ExtendedEntity) -> List[Test]:
        """生成时间边界测试"""
        tests = []
        
        # 查找所有时间相关的属性
        time_attributes = [attr for attr in entity.attributes 
                          if 'time' in attr.name.lower() or 'minutes' in attr.name.lower()]
        
        for attr in time_attributes:
            # 获取时间边界值
            boundaries = self._get_time_boundaries(attr, entity)
            
            for boundary_name, boundary_value in boundaries.items():
                test = Test(
                    test_name=f"{entity.name}_time_boundary_{attr.name}_{boundary_name}",
                    test_type="timed_constraint_boundary",
                    description=f"Test time boundary for {attr.name}: {boundary_name} = {boundary_value}",
                    test_data=self._create_boundary_test_data(entity, attr, boundary_value),
                    expected_result="pass" if boundary_name != "invalid" else "fail",
                    priority=8,
                    entity=entity.name
                )
                tests.append(test)
        
        return tests
    
    def _generate_concurrent_timing_tests(self, entity: ExtendedEntity) -> List[Test]:
        """生成并发时序测试"""
        tests = []
        
        # 识别可能存在并发的场景
        concurrent_scenarios = self._identify_concurrent_scenarios(entity)
        
        for scenario_name, scenario_config in concurrent_scenarios.items():
            test = Test(
                test_name=f"{entity.name}_concurrent_timing_{scenario_name}",
                test_type="timed_constraint_concurrent",
                description=f"Test concurrent timing scenario: {scenario_name}",
                test_data=self._create_concurrent_test_data(entity, scenario_config),
                expected_result="pass",
                priority=8,
                entity=entity.name
            )
            tests.append(test)
        
        return tests
    
    def _generate_cumulative_timing_tests(self, entity: ExtendedEntity) -> List[Test]:
        """生成时间累积效应测试"""
        tests = []
        
        # 查找涉及时间累积的规则
        cumulative_rules = self._find_cumulative_time_rules(entity)
        
        for rule in cumulative_rules:
            # 测试时间累积触发规则
            test = Test(
                test_name=f"{entity.name}_cumulative_timing_{rule.get('name', 'rule')}",
                test_type="timed_constraint_cumulative",
                description=f"Test cumulative timing effect for rule: {rule.get('name', '')}",
                test_data=self._create_cumulative_test_data(entity, rule),
                expected_result="pass",
                priority=7,
                entity=entity.name
            )
            tests.append(test)
        
        return tests
    
    def _create_within_window_test(self, entity: ExtendedEntity, 
                                  constraint: TimedConstraint) -> Test:
        """创建时间窗口内的测试"""
        test_data = self._generate_base_test_data(entity)
        
        # 设置满足时间窗口的条件
        time_value = constraint.time_window // 2  # 使用窗口中间值
        self._apply_time_constraint(test_data, constraint, time_value, True)
        
        test_data['timing_test'] = {
            'type': 'within_window',
            'constraint': constraint.name,
            'time_window': constraint.time_window,
            'test_time': time_value,
            'expected_action': constraint.action
        }
        
        return Test(
            test_name=f"{entity.name}_timed_{constraint.name}_within_window",
            test_type="timed_constraint_satisfied",
            description=f"Test {constraint.name} within time window ({time_value} < {constraint.time_window} minutes)",
            test_data=test_data,
            expected_result="pass",
            priority=9,
            entity=entity.name
        )
    
    def _create_outside_window_test(self, entity: ExtendedEntity,
                                   constraint: TimedConstraint) -> Test:
        """创建时间窗口外的测试"""
        test_data = self._generate_base_test_data(entity)
        
        # 设置超出时间窗口的条件
        time_value = constraint.time_window + 10
        self._apply_time_constraint(test_data, constraint, time_value, False)
        
        test_data['timing_test'] = {
            'type': 'outside_window',
            'constraint': constraint.name,
            'time_window': constraint.time_window,
            'test_time': time_value,
            'expected_action': 'none'
        }
        
        return Test(
            test_name=f"{entity.name}_timed_{constraint.name}_outside_window",
            test_type="timed_constraint_violated",
            description=f"Test {constraint.name} outside time window ({time_value} > {constraint.time_window} minutes)",
            test_data=test_data,
            expected_result="pass",
            priority=8,
            entity=entity.name
        )
    
    def _create_window_boundary_test(self, entity: ExtendedEntity,
                                    constraint: TimedConstraint) -> Test:
        """创建时间窗口边界测试"""
        test_data = self._generate_base_test_data(entity)
        
        # 测试精确的边界值
        time_value = constraint.time_window
        self._apply_time_constraint(test_data, constraint, time_value, True)
        
        test_data['timing_test'] = {
            'type': 'at_boundary',
            'constraint': constraint.name,
            'time_window': constraint.time_window,
            'test_time': time_value,
            'expected_action': constraint.action
        }
        
        return Test(
            test_name=f"{entity.name}_timed_{constraint.name}_at_boundary",
            test_type="timed_constraint_boundary",
            description=f"Test {constraint.name} at time window boundary ({time_value} == {constraint.time_window} minutes)",
            test_data=test_data,
            expected_result="pass",
            priority=9,
            entity=entity.name
        )
    
    def _create_time_condition_satisfied_test(self, entity: ExtendedEntity, rule: Dict[str, Any],
                                            condition_type: str, time_value: int, 
                                            attribute: str) -> Test:
        """创建满足时间条件的测试"""
        test_data = self._generate_base_test_data(entity)
        
        # 设置满足条件的时间值
        if condition_type == '>':
            test_data[attribute] = time_value + 5
        elif condition_type == '>=':
            test_data[attribute] = time_value
        elif condition_type == '<':
            test_data[attribute] = time_value - 5
        elif condition_type == '<=':
            test_data[attribute] = time_value
        elif condition_type == '==':
            test_data[attribute] = time_value
        
        # 确保满足规则的其他条件
        self._ensure_rule_conditions(test_data, rule, entity)
        
        test_data['rule_timing'] = {
            'rule_name': rule.get('name', ''),
            'condition_type': condition_type,
            'time_attribute': attribute,
            'threshold': time_value,
            'actual_value': test_data[attribute],
            'expected_triggered': True
        }
        
        return Test(
            test_name=f"{entity.name}_timed_rule_{rule.get('name', 'rule')}_satisfied",
            test_type="timed_constraint_rule_triggered",
            description=f"Test time-based rule triggered: {rule.get('name', '')} when {attribute} {condition_type} {time_value}",
            test_data=test_data,
            expected_result="pass",
            priority=8,
            entity=entity.name
        )
    
    def _create_time_condition_violated_test(self, entity: ExtendedEntity, rule: Dict[str, Any],
                                           condition_type: str, time_value: int,
                                           attribute: str) -> Test:
        """创建不满足时间条件的测试"""
        test_data = self._generate_base_test_data(entity)
        
        # 设置不满足条件的时间值
        if condition_type == '>':
            test_data[attribute] = time_value - 5
        elif condition_type == '>=':
            test_data[attribute] = time_value - 1
        elif condition_type == '<':
            test_data[attribute] = time_value + 5
        elif condition_type == '<=':
            test_data[attribute] = time_value + 1
        elif condition_type == '==':
            test_data[attribute] = time_value + 1
        
        test_data['rule_timing'] = {
            'rule_name': rule.get('name', ''),
            'condition_type': condition_type,
            'time_attribute': attribute,
            'threshold': time_value,
            'actual_value': test_data[attribute],
            'expected_triggered': False
        }
        
        return Test(
            test_name=f"{entity.name}_timed_rule_{rule.get('name', 'rule')}_not_triggered",
            test_type="timed_constraint_rule_not_triggered",
            description=f"Test time-based rule not triggered: {rule.get('name', '')} when {attribute} violates {condition_type} {time_value}",
            test_data=test_data,
            expected_result="pass",
            priority=7,
            entity=entity.name
        )
    
    def _create_boundary_test_data(self, entity: ExtendedEntity, attr, 
                                  boundary_value: int) -> Dict[str, Any]:
        """创建边界测试数据"""
        test_data = self._generate_base_test_data(entity)
        test_data[attr.name] = boundary_value
        
        test_data['boundary_test'] = {
            'attribute': attr.name,
            'boundary_value': boundary_value,
            'boundary_type': self._identify_boundary_type(boundary_value, attr)
        }
        
        return test_data
    
    def _create_concurrent_test_data(self, entity: ExtendedEntity,
                                   scenario_config: Dict[str, Any]) -> Dict[str, Any]:
        """创建并发测试数据"""
        test_data = {
            'concurrent_events': []
        }
        
        # 生成多个并发事件
        for i in range(scenario_config.get('event_count', 3)):
            event_data = self._generate_base_test_data(entity)
            event_data['event_id'] = i + 1
            event_data['timestamp'] = scenario_config.get('base_time', 0) + i
            
            # 设置并发相关的属性
            for attr_name, attr_value in scenario_config.get('attributes', {}).items():
                if attr_name in [a.name for a in entity.attributes]:
                    event_data[attr_name] = attr_value
            
            test_data['concurrent_events'].append(event_data)
        
        test_data['scenario'] = scenario_config.get('name', 'concurrent_test')
        test_data['expected_behavior'] = scenario_config.get('expected', 'serialized_processing')
        
        return test_data
    
    def _create_cumulative_test_data(self, entity: ExtendedEntity,
                                   rule: Dict[str, Any]) -> Dict[str, Any]:
        """创建累积时间测试数据"""
        test_data = {
            'timeline': []
        }
        
        # 解析累积条件
        condition = rule.get('condition', '')
        threshold = self._extract_cumulative_threshold(condition)
        
        # 生成时间线事件
        cumulative_time = 0
        event_count = 0
        
        while cumulative_time < threshold + 10:
            event = self._generate_base_test_data(entity)
            event['timestamp'] = cumulative_time
            event['event_number'] = event_count + 1
            
            test_data['timeline'].append(event)
            
            cumulative_time += 5  # 每5分钟一个事件
            event_count += 1
        
        test_data['rule_name'] = rule.get('name', '')
        test_data['cumulative_threshold'] = threshold
        test_data['expected_trigger_at'] = threshold
        
        return test_data
    
    def _generate_base_test_data(self, entity: ExtendedEntity) -> Dict[str, Any]:
        """生成基础测试数据"""
        test_data = {}
        
        for attr in entity.attributes:
            test_data[attr.name] = self.value_generator.generate_valid_value(attr)
        
        return test_data
    
    def _extract_time_related_rules(self, entity: ExtendedEntity) -> List[Dict[str, Any]]:
        """提取时间相关的规则"""
        time_rules = []
        time_keywords = ['time', '时间', 'minute', '分钟', 'hour', '小时', 'delay', '延迟']
        
        # 从实体规则中查找
        for rule in entity.rules:
            rule_text = str(rule)
            if any(keyword in rule_text.lower() for keyword in time_keywords):
                time_rules.append(rule)
        
        # 从全局规则中查找（如果有DSL模型）
        if self.dsl_model:
            for rule in self.dsl_model.global_rules:
                rule_text = str(rule)
                if any(keyword in rule_text.lower() for keyword in time_keywords):
                    # 检查规则是否与当前实体相关
                    if self._is_rule_relevant_to_entity(rule, entity):
                        time_rules.append(rule)
        
        return time_rules
    
    def _extract_time_conditions(self, rule: Dict[str, Any]) -> List[Tuple[str, int, str]]:
        """从规则中提取时间条件"""
        conditions = []
        condition_text = rule.get('condition', '')
        
        # 匹配时间比较模式
        patterns = [
            r'(\w+_(?:time|minutes))\s*([><=]+)\s*(\d+)',
            r'(\w+)\s*([><=]+)\s*(\d+)\s*(?:分钟|minutes)',
            r'time.*?(\w+)\s*([><=]+)\s*(\d+)'
        ]
        
        for pattern in patterns:
            matches = re.findall(pattern, condition_text)
            for attr, op, value in matches:
                conditions.append((op, int(value), attr))
        
        return conditions
    
    def _get_time_boundaries(self, attr, entity: ExtendedEntity) -> Dict[str, int]:
        """获取时间属性的边界值"""
        boundaries = {}
        
        # 从属性定义获取边界
        if hasattr(attr, 'min') and attr.min is not None:
            boundaries['min'] = attr.min
            boundaries['min_minus_1'] = attr.min - 1
        
        if hasattr(attr, 'max') and attr.max is not None:
            boundaries['max'] = attr.max
            boundaries['max_plus_1'] = attr.max + 1
        
        # 从约束中提取边界
        for constraint in entity.constraints:
            if attr.name in constraint:
                extracted = self._extract_boundary_from_constraint(constraint, attr.name)
                boundaries.update(extracted)
        
        # 添加常见的时间边界
        if 'minute' in attr.name.lower():
            boundaries.update({
                'one_hour': 60,
                'half_hour': 30,
                'ten_minutes': 10
            })
        
        return boundaries
    
    def _identify_concurrent_scenarios(self, entity: ExtendedEntity) -> Dict[str, Dict[str, Any]]:
        """识别并发场景"""
        scenarios = {}
        
        # 场景1：多个派单请求
        if 'dispatch' in entity.name.lower():
            scenarios['multiple_dispatch_requests'] = {
                'name': 'multiple_dispatch_requests',
                'event_count': 3,
                'base_time': 0,
                'attributes': {'dispatch_status': 1},
                'expected': 'queue_processing'
            }
        
        # 场景2：同时的状态更新
        if any(sm for sm in entity.state_machines):
            scenarios['concurrent_state_updates'] = {
                'name': 'concurrent_state_updates',
                'event_count': 2,
                'base_time': 0,
                'attributes': {},
                'expected': 'last_write_wins'
            }
        
        return scenarios
    
    def _find_cumulative_time_rules(self, entity: ExtendedEntity) -> List[Dict[str, Any]]:
        """查找涉及时间累积的规则"""
        cumulative_rules = []
        
        cumulative_keywords = ['累积', 'cumulative', 'total', '总计', 'sum', 'elapsed', '经过']
        
        for rule in entity.rules:
            if isinstance(rule, dict):
                condition = rule.get('condition', '')
                if any(keyword in condition.lower() for keyword in cumulative_keywords):
                    cumulative_rules.append(rule)
        
        return cumulative_rules
    
    def _apply_time_constraint(self, test_data: Dict[str, Any], constraint: TimedConstraint,
                             time_value: int, within_window: bool):
        """应用时间约束到测试数据"""
        # 解析约束条件中的时间属性
        condition_attrs = re.findall(r'\b(\w+)\b', constraint.condition)
        
        for attr in condition_attrs:
            if 'time' in attr or 'minute' in attr:
                test_data[attr] = time_value
                break
    
    def _ensure_rule_conditions(self, test_data: Dict[str, Any], rule: Dict[str, Any],
                               entity: ExtendedEntity):
        """确保满足规则的所有条件"""
        condition = rule.get('condition', '')
        
        # 解析AND条件
        and_conditions = re.split(r'\s+and\s+', condition)
        
        for cond in and_conditions:
            # 跳过已处理的时间条件
            if any(keyword in cond for keyword in ['time', 'minute', '分钟']):
                continue
            
            # 处理其他条件
            equals = re.findall(r'(\w+)\s*==\s*(\w+)', cond)
            for attr, value in equals:
                if attr in [a.name for a in entity.attributes]:
                    if value.isdigit():
                        test_data[attr] = int(value)
                    elif value in ['true', 'false']:
                        test_data[attr] = value == 'true'
                    else:
                        test_data[attr] = value
    
    def _is_rule_relevant_to_entity(self, rule: Dict[str, Any], entity: ExtendedEntity) -> bool:
        """判断规则是否与实体相关"""
        rule_text = str(rule)
        
        # 检查规则中是否提到实体名或实体的属性
        if entity.name in rule_text:
            return True
        
        for attr in entity.attributes:
            if attr.name in rule_text:
                return True
        
        return False
    
    def _identify_boundary_type(self, value: int, attr) -> str:
        """识别边界类型"""
        if hasattr(attr, 'min') and value == attr.min:
            return 'minimum'
        elif hasattr(attr, 'max') and value == attr.max:
            return 'maximum'
        elif value == 0:
            return 'zero'
        elif value < 0:
            return 'negative'
        else:
            return 'custom'
    
    def _extract_boundary_from_constraint(self, constraint: str, attr_name: str) -> Dict[str, int]:
        """从约束中提取边界值"""
        boundaries = {}
        
        # 匹配属性的比较操作
        patterns = [
            f'{attr_name}\\s*>=\\s*(\\d+)',
            f'{attr_name}\\s*>\\s*(\\d+)',
            f'{attr_name}\\s*<=\\s*(\\d+)',
            f'{attr_name}\\s*<\\s*(\\d+)'
        ]
        
        for pattern in patterns:
            match = re.search(pattern, constraint)
            if match:
                value = int(match.group(1))
                if '>=' in pattern:
                    boundaries['constraint_min'] = value
                elif '>' in pattern:
                    boundaries['constraint_min_exclusive'] = value
                elif '<=' in pattern:
                    boundaries['constraint_max'] = value
                elif '<' in pattern:
                    boundaries['constraint_max_exclusive'] = value
        
        return boundaries
    
    def _extract_cumulative_threshold(self, condition: str) -> int:
        """从条件中提取累积阈值"""
        # 尝试匹配累积时间模式
        patterns = [
            r'(?:累积|cumulative|total).*?(\d+)\s*(?:分钟|minutes)',
            r'(?:超过|exceed|greater).*?(\d+)\s*(?:分钟|minutes)',
            r'(\d+)\s*(?:分钟|minutes).*?(?:累积|cumulative|total)'
        ]
        
        for pattern in patterns:
            match = re.search(pattern, condition, re.IGNORECASE)
            if match:
                return int(match.group(1))
        
        # 默认值
        return 30