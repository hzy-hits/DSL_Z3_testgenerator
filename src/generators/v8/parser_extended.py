"""
Extended YAML Parser Module with State Machine Support
扩展的YAML解析器，支持状态机和测试需求
"""

import yaml
from typing import List, Dict, Any, Union
from .models import Attribute
from .models_extended import (
    ExtendedEntity, State, Transition, StateMachine, 
    TestRequirement, TimedConstraint, ExtendedDSLModel
)


class ExtendedYAMLParser:
    """扩展的YAML解析器"""
    
    def parse_file(self, file_path: str) -> ExtendedDSLModel:
        """解析YAML文件，返回扩展的DSL模型"""
        with open(file_path, 'r', encoding='utf-8') as f:
            data = yaml.safe_load(f)
        
        model = ExtendedDSLModel(
            domain=data.get('domain', 'Unknown Domain')
        )
        
        # 解析全局约束
        global_constraints = data.get('constraints', [])
        if isinstance(global_constraints, list):
            model.global_constraints = [str(c) for c in global_constraints]
        
        # 解析全局规则
        global_rules = data.get('rules', [])
        if isinstance(global_rules, list):
            model.global_rules = global_rules
        
        # 解析实体
        entities_data = data.get('entities', [])
        if isinstance(entities_data, list):
            for entity_data in entities_data:
                if isinstance(entity_data, dict) and 'name' in entity_data:
                    entity = self._parse_extended_entity(entity_data)
                    model.entities.append(entity)
        
        # 解析全局状态机
        state_machines_data = data.get('state_machines', [])
        if isinstance(state_machines_data, list):
            for sm_data in state_machines_data:
                state_machine = self._parse_state_machine(sm_data)
                model.state_machines.append(state_machine)
                
                # 将状态机关联到对应的实体
                entity = model.get_entity_by_name(state_machine.entity)
                if entity:
                    entity.state_machines.append(state_machine)
        
        # 解析测试需求
        test_requirements_data = data.get('test_requirements', [])
        if isinstance(test_requirements_data, list):
            for req_data in test_requirements_data:
                test_req = self._parse_test_requirement(req_data)
                model.test_requirements.append(test_req)
        
        # 从规则中提取时序约束
        self._extract_timed_constraints(model)
        
        return model
    
    def _parse_extended_entity(self, entity_data: Dict[str, Any]) -> ExtendedEntity:
        """解析扩展的实体"""
        entity = ExtendedEntity(name=entity_data['name'])
        
        # 解析属性
        attributes_data = entity_data.get('attributes', [])
        if isinstance(attributes_data, list):
            for attr_data in attributes_data:
                if isinstance(attr_data, dict) and 'name' in attr_data:
                    attr = self._parse_attribute(attr_data)
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
        """解析属性（复用原有逻辑）"""
        attr_type = attr_data.get('type', 'string')
        
        # 处理集合类型
        is_collection = False
        if attr_type.startswith('array[') or attr_type.startswith('set['):
            is_collection = True
            base_type = attr_type[attr_type.index('[')+1:attr_type.index(']')]
            attr_type = base_type
        elif attr_type in ['array', 'list', 'set']:
            is_collection = True
        
        # 处理real类型
        if attr_type == 'real':
            attr_type = 'float'
        
        # 处理枚举值
        enum_values = attr_data.get('enum_values', attr_data.get('enum'))
        
        return Attribute(
            name=attr_data.get('name', 'unnamed'),
            type=attr_type,
            required=attr_data.get('required', True),
            enum=enum_values,
            is_collection=is_collection,
            is_temporal=attr_type in ['date', 'datetime', 'timestamp'],
            min_size=attr_data.get('min_size'),
            max_size=attr_data.get('max_size')
        )
    
    def _parse_state_machine(self, sm_data: Dict[str, Any]) -> StateMachine:
        """解析状态机"""
        state_machine = StateMachine(
            name=sm_data.get('name', ''),
            entity=sm_data.get('entity', ''),
            state_attribute=sm_data.get('state_attribute', '')
        )
        
        # 解析状态
        states_data = sm_data.get('states', [])
        for state_data in states_data:
            state = State(
                name=state_data.get('name', ''),
                value=state_data.get('value', state_data.get('name')),
                description=state_data.get('description', '')
            )
            state_machine.states.append(state)
        
        # 解析转换
        transitions_data = sm_data.get('transitions', [])
        for trans_data in transitions_data:
            from_state = trans_data.get('from', '')
            # 处理from可能是列表的情况
            if isinstance(from_state, list):
                from_state_list = from_state
            else:
                from_state_list = [from_state]
            
            transition = Transition(
                name=trans_data.get('name', ''),
                from_state=from_state_list,
                to_state=trans_data.get('to', ''),
                condition=trans_data.get('condition', ''),
                description=trans_data.get('description', '')
            )
            state_machine.transitions.append(transition)
        
        return state_machine
    
    def _parse_test_requirement(self, req_data: Dict[str, Any]) -> TestRequirement:
        """解析测试需求"""
        # 处理timing_constraints
        timing_constraints = {}
        if req_data.get('type') == 'timed_constraint':
            timing_constraints = {
                'time_window': req_data.get('time_window', 0),
                'condition': req_data.get('condition', ''),
                'action': req_data.get('action', '')
            }
        
        return TestRequirement(
            name=req_data.get('name', ''),
            type=req_data.get('type', ''),
            focus=req_data.get('focus', []),
            description=req_data.get('description', ''),
            conditions=req_data.get('conditions', []),
            timing_constraints=timing_constraints
        )
    
    def _extract_timed_constraints(self, model: ExtendedDSLModel):
        """从规则中提取时序约束"""
        # 查找包含时间窗口的规则
        time_related_keywords = ['分钟', 'minutes', '小时', 'hours', '时间', 'time']
        
        for rule in model.global_rules:
            if isinstance(rule, dict):
                rule_name = rule.get('name', '')
                condition = rule.get('condition', '')
                description = rule.get('description', '')
                
                # 检查是否包含时间相关的关键词
                if any(keyword in str(rule) for keyword in time_related_keywords):
                    # 尝试从条件中提取时间窗口
                    time_window = self._extract_time_window(condition)
                    if time_window:
                        timed_constraint = TimedConstraint(
                            name=rule_name,
                            condition=condition,
                            time_window=time_window,
                            action=rule.get('action', ''),
                            description=description
                        )
                        # 添加到相关实体
                        for entity in model.entities:
                            # 简单判断：如果条件中包含实体的某个属性，就认为相关
                            if any(attr.name in condition for attr in entity.attributes):
                                entity.timed_constraints.append(timed_constraint)
                                break
    
    def _extract_time_window(self, condition: str) -> int:
        """从条件中提取时间窗口（分钟）"""
        import re
        
        # 匹配数字+分钟
        minutes_match = re.search(r'(\d+)\s*(?:分钟|minutes)', condition)
        if minutes_match:
            return int(minutes_match.group(1))
        
        # 匹配数字+小时
        hours_match = re.search(r'(\d+)\s*(?:小时|hours)', condition)
        if hours_match:
            return int(hours_match.group(1)) * 60
        
        # 匹配比较操作符中的数字
        comparison_match = re.search(r'(?:>|<|>=|<=)\s*(\d+)', condition)
        if comparison_match and ('time' in condition or '分钟' in condition):
            return int(comparison_match.group(1))
        
        return 0