"""
State Transition Test Strategy
状态转换测试策略
"""

from typing import List, Dict, Any, Optional
from .models import Test
from .models_extended import ExtendedEntity, StateMachine, Transition, State
from abc import ABC
from .value_generator import ValueGenerator
import re


class StateTransitionTestStrategy:
    """状态转换测试策略"""
    
    def __init__(self):
        self.value_generator = ValueGenerator()
    
    def generate_tests(self, entity: ExtendedEntity, existing_tests: List[Test]) -> List[Test]:
        """生成状态转换测试"""
        tests = []
        
        # 获取与该实体相关的所有状态机
        state_machines = entity.state_machines
        
        for state_machine in state_machines:
            # 1. 生成有效状态转换测试
            tests.extend(self._generate_valid_transition_tests(entity, state_machine))
            
            # 2. 生成无效状态转换测试
            tests.extend(self._generate_invalid_transition_tests(entity, state_machine))
            
            # 3. 生成状态转换路径测试
            tests.extend(self._generate_path_tests(entity, state_machine))
            
            # 4. 生成边界条件测试
            tests.extend(self._generate_boundary_condition_tests(entity, state_machine))
        
        return tests
    
    def _generate_valid_transition_tests(self, entity: ExtendedEntity, 
                                       state_machine: StateMachine) -> List[Test]:
        """生成有效状态转换测试"""
        tests = []
        
        for transition in state_machine.transitions:
            for from_state_name in transition.from_state:
                from_state = state_machine.get_state_by_name(from_state_name)
                to_state = state_machine.get_state_by_name(transition.to_state)
                
                if from_state and to_state:
                    # 生成满足转换条件的测试数据
                    test_data = self._generate_transition_data(
                        entity, state_machine, from_state, to_state, transition, True
                    )
                    
                    test = Test(
                        test_name=f"{entity.name}_state_transition_{transition.name}_valid",
                        test_type="state_transition_valid",
                        description=f"Test valid state transition: {from_state.name} -> {to_state.name} via {transition.name}",
                        test_data=test_data,
                        expected_result="pass",
                        priority=9,
                        entity=entity.name
                    )
                    tests.append(test)
        
        return tests
    
    def _generate_invalid_transition_tests(self, entity: ExtendedEntity,
                                         state_machine: StateMachine) -> List[Test]:
        """生成无效状态转换测试"""
        tests = []
        
        # 对每个状态，测试不允许的转换
        for from_state in state_machine.states:
            # 获取该状态允许的所有转换
            valid_transitions = state_machine.get_transitions_from_state(from_state.name)
            valid_to_states = {t.to_state for t in valid_transitions}
            
            # 测试到其他状态的非法转换
            for to_state in state_machine.states:
                if to_state.name != from_state.name and to_state.name not in valid_to_states:
                    test_data = self._generate_transition_data(
                        entity, state_machine, from_state, to_state, None, False
                    )
                    
                    test = Test(
                        test_name=f"{entity.name}_state_transition_{from_state.name}_to_{to_state.name}_invalid",
                        test_type="state_transition_invalid",
                        description=f"Test invalid state transition: {from_state.name} -> {to_state.name} (not allowed)",
                        test_data=test_data,
                        expected_result="fail",
                        expected_error="Invalid state transition",
                        priority=8,
                        entity=entity.name
                    )
                    tests.append(test)
        
        return tests
    
    def _generate_path_tests(self, entity: ExtendedEntity,
                           state_machine: StateMachine) -> List[Test]:
        """生成状态转换路径测试"""
        tests = []
        
        # 获取所有可能的路径
        paths = state_machine.get_all_paths(max_depth=5)
        
        # 为每条路径生成测试
        for i, path in enumerate(paths[:10]):  # 限制最多10条路径
            if len(path) > 1:  # 至少包含2个转换的路径
                path_description = " -> ".join([path[0].from_state[0]] + [t.to_state for t in path])
                
                # 生成路径测试数据
                test_data = self._generate_path_test_data(entity, state_machine, path)
                
                test = Test(
                    test_name=f"{entity.name}_state_path_{i+1}",
                    test_type="state_transition_path",
                    description=f"Test state transition path: {path_description}",
                    test_data=test_data,
                    expected_result="pass",
                    priority=8,
                    entity=entity.name
                )
                tests.append(test)
        
        return tests
    
    def _generate_boundary_condition_tests(self, entity: ExtendedEntity,
                                         state_machine: StateMachine) -> List[Test]:
        """生成边界条件测试"""
        tests = []
        
        for transition in state_machine.transitions:
            if transition.condition:
                # 分析条件中的边界值
                boundary_values = self._extract_boundary_values(transition.condition)
                
                for boundary_type, values in boundary_values.items():
                    for value in values:
                        # 生成边界测试数据
                        test_data = self._generate_boundary_test_data(
                            entity, state_machine, transition, boundary_type, value
                        )
                        
                        test = Test(
                            test_name=f"{entity.name}_state_transition_{transition.name}_boundary_{boundary_type}_{value}",
                            test_type="state_transition_boundary",
                            description=f"Test state transition boundary condition: {transition.name} with {boundary_type}={value}",
                            test_data=test_data,
                            expected_result="pass" if boundary_type != "invalid" else "fail",
                            priority=8,
                            entity=entity.name
                        )
                        tests.append(test)
        
        return tests
    
    def _generate_transition_data(self, entity: ExtendedEntity, state_machine: StateMachine,
                                from_state: State, to_state: State, 
                                transition: Optional[Transition], is_valid: bool) -> Dict[str, Any]:
        """生成状态转换测试数据"""
        test_data = {}
        
        # 设置初始状态
        test_data[state_machine.state_attribute] = from_state.value
        test_data['initial_state'] = from_state.name
        test_data['target_state'] = to_state.name
        
        # 生成其他必需属性的值
        for attr in entity.attributes:
            if attr.name not in test_data:
                test_data[attr.name] = self.value_generator.generate_valid_value(attr)
        
        # 如果有转换条件，生成满足或不满足条件的数据
        if transition and transition.condition and is_valid:
            self._apply_condition_to_data(test_data, transition.condition, True)
        
        # 添加转换信息
        test_data['transition'] = {
            'name': transition.name if transition else 'invalid_transition',
            'condition': transition.condition if transition else '',
            'expected_valid': is_valid
        }
        
        return test_data
    
    def _generate_path_test_data(self, entity: ExtendedEntity, state_machine: StateMachine,
                               path: List[Transition]) -> Dict[str, Any]:
        """生成路径测试数据"""
        test_data = {
            'path_steps': []
        }
        
        # 生成初始数据
        for attr in entity.attributes:
            test_data[attr.name] = self.value_generator.generate_valid_value(attr)
        
        # 设置初始状态
        initial_state = state_machine.get_state_by_name(path[0].from_state[0])
        if initial_state:
            test_data[state_machine.state_attribute] = initial_state.value
        
        # 为每个转换步骤生成数据
        for i, transition in enumerate(path):
            step_data = {
                'step': i + 1,
                'transition': transition.name,
                'from_state': transition.from_state[0],
                'to_state': transition.to_state,
                'condition': transition.condition
            }
            
            # 确保满足转换条件
            if transition.condition:
                self._apply_condition_to_data(test_data, transition.condition, True)
                step_data['condition_values'] = self._extract_condition_values(test_data, transition.condition)
            
            test_data['path_steps'].append(step_data)
        
        return test_data
    
    def _generate_boundary_test_data(self, entity: ExtendedEntity, state_machine: StateMachine,
                                   transition: Transition, boundary_type: str, 
                                   value: Any) -> Dict[str, Any]:
        """生成边界测试数据"""
        test_data = {}
        
        # 生成基本数据
        for attr in entity.attributes:
            test_data[attr.name] = self.value_generator.generate_valid_value(attr)
        
        # 设置起始状态
        from_state = state_machine.get_state_by_name(transition.from_state[0])
        if from_state:
            test_data[state_machine.state_attribute] = from_state.value
        
        # 应用边界值
        if boundary_type in transition.condition:
            # 找到条件中涉及的属性并设置边界值
            for attr in entity.attributes:
                if attr.name in transition.condition:
                    test_data[attr.name] = value
                    break
        
        test_data['boundary_test'] = {
            'type': boundary_type,
            'value': value,
            'transition': transition.name
        }
        
        return test_data
    
    def _apply_condition_to_data(self, test_data: Dict[str, Any], condition: str, satisfy: bool):
        """根据条件修改测试数据"""
        # 解析简单的比较条件
        comparisons = re.findall(r'(\w+)\s*([><=!]+)\s*(\d+)', condition)
        
        for attr_name, operator, value in comparisons:
            value = int(value)
            
            if satisfy:
                # 生成满足条件的值
                if operator == '>':
                    test_data[attr_name] = value + 10
                elif operator == '>=':
                    test_data[attr_name] = value
                elif operator == '<':
                    test_data[attr_name] = value - 10
                elif operator == '<=':
                    test_data[attr_name] = value
                elif operator == '==':
                    test_data[attr_name] = value
                elif operator == '!=':
                    test_data[attr_name] = value + 1
            else:
                # 生成不满足条件的值
                if operator == '>':
                    test_data[attr_name] = value - 10
                elif operator == '>=':
                    test_data[attr_name] = value - 1
                elif operator == '<':
                    test_data[attr_name] = value + 10
                elif operator == '<=':
                    test_data[attr_name] = value + 1
                elif operator == '==':
                    test_data[attr_name] = value + 1
                elif operator == '!=':
                    test_data[attr_name] = value
    
    def _extract_boundary_values(self, condition: str) -> Dict[str, List[Any]]:
        """从条件中提取边界值"""
        boundary_values = {}
        
        # 提取数值比较
        comparisons = re.findall(r'(\w+)\s*([><=]+)\s*(\d+)', condition)
        
        for attr_name, operator, value in comparisons:
            value = int(value)
            
            if operator in ['>', '>=']:
                boundary_values[f"{attr_name}_min"] = [value - 1, value, value + 1]
            elif operator in ['<', '<=']:
                boundary_values[f"{attr_name}_max"] = [value - 1, value, value + 1]
            elif operator == '==':
                boundary_values[f"{attr_name}_exact"] = [value]
        
        return boundary_values
    
    def _extract_condition_values(self, test_data: Dict[str, Any], condition: str) -> Dict[str, Any]:
        """从测试数据中提取条件相关的值"""
        condition_values = {}
        
        # 找出条件中涉及的所有属性
        attr_names = re.findall(r'\b(\w+)\b', condition)
        
        for attr_name in attr_names:
            if attr_name in test_data:
                condition_values[attr_name] = test_data[attr_name]
        
        return condition_values