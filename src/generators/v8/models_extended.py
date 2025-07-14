"""
Extended Data Models for V8 Generator with State Machine Support
扩展的数据模型定义，支持状态机和测试需求
"""

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Union

# Import original models
from .models import Attribute, Entity, Test


@dataclass
class State:
    """状态定义"""
    name: str
    value: Union[int, str]
    description: str = ""


@dataclass
class Transition:
    """状态转换定义"""
    name: str
    from_state: Union[str, List[str]]  # 支持单个状态或多个状态
    to_state: str
    condition: str = ""
    description: str = ""
    
    def __post_init__(self):
        """确保from_state始终是列表"""
        if isinstance(self.from_state, str):
            self.from_state = [self.from_state]


@dataclass
class StateMachine:
    """状态机定义"""
    name: str
    entity: str
    state_attribute: str
    states: List[State] = field(default_factory=list)
    transitions: List[Transition] = field(default_factory=list)
    
    def get_state_by_name(self, name: str) -> Optional[State]:
        """根据名称获取状态"""
        for state in self.states:
            if state.name == name:
                return state
        return None
    
    def get_state_by_value(self, value: Union[int, str]) -> Optional[State]:
        """根据值获取状态"""
        for state in self.states:
            if state.value == value:
                return state
        return None
    
    def get_transitions_from_state(self, state_name: str) -> List[Transition]:
        """获取从指定状态出发的所有转换"""
        transitions = []
        for transition in self.transitions:
            if state_name in transition.from_state:
                transitions.append(transition)
        return transitions
    
    def get_all_paths(self, max_depth: int = 10) -> List[List[Transition]]:
        """获取所有可能的状态转换路径"""
        paths = []
        
        # 找到所有初始状态（没有入边的状态）
        target_states = {t.to_state for t in self.transitions}
        source_states = set()
        for t in self.transitions:
            source_states.update(t.from_state)
        initial_states = source_states - target_states
        
        # 如果没有明确的初始状态，使用第一个状态
        if not initial_states and self.states:
            initial_states = {self.states[0].name}
        
        # 深度优先搜索所有路径
        for initial in initial_states:
            self._dfs_paths(initial, [], paths, set(), max_depth)
        
        return paths
    
    def _dfs_paths(self, current_state: str, current_path: List[Transition], 
                   all_paths: List[List[Transition]], visited: set, max_depth: int):
        """深度优先搜索状态转换路径"""
        if len(current_path) >= max_depth:
            return
        
        # 获取当前状态的所有可能转换
        transitions = self.get_transitions_from_state(current_state)
        
        if not transitions:
            # 到达终止状态，保存路径
            if current_path:
                all_paths.append(current_path.copy())
        else:
            for transition in transitions:
                # 避免循环
                if transition.to_state not in visited:
                    visited.add(transition.to_state)
                    current_path.append(transition)
                    self._dfs_paths(transition.to_state, current_path, all_paths, visited, max_depth)
                    current_path.pop()
                    visited.remove(transition.to_state)


@dataclass
class TestRequirement:
    """测试需求定义"""
    name: str
    type: str  # boundary, equivalence, state_machine, scenario, timed_constraint
    focus: List[str] = field(default_factory=list)  # 关注的属性或状态机
    description: str = ""
    conditions: List[str] = field(default_factory=list)  # 特定条件
    timing_constraints: Dict[str, Any] = field(default_factory=dict)  # 时间约束


@dataclass
class TimedConstraint:
    """时序约束定义"""
    name: str
    condition: str  # 触发条件
    time_window: int  # 时间窗口（分钟）
    action: str  # 必须发生的动作
    description: str = ""


@dataclass
class ExtendedEntity(Entity):
    """扩展的实体定义"""
    state_machines: List[StateMachine] = field(default_factory=list)
    test_requirements: List[TestRequirement] = field(default_factory=list)
    timed_constraints: List[TimedConstraint] = field(default_factory=list)
    
    def get_state_machine_by_attribute(self, attribute_name: str) -> Optional[StateMachine]:
        """根据状态属性获取状态机"""
        for sm in self.state_machines:
            if sm.state_attribute == attribute_name:
                return sm
        return None


@dataclass 
class ScenarioStep:
    """场景步骤定义"""
    action: str  # 动作描述
    entity: str  # 涉及的实体
    state_change: Optional[Dict[str, Any]] = None  # 状态变化
    expected_result: Dict[str, Any] = field(default_factory=dict)  # 期望结果
    timing: Optional[int] = None  # 相对时间（分钟）


@dataclass
class TestScenario:
    """测试场景定义"""
    name: str
    description: str
    steps: List[ScenarioStep] = field(default_factory=list)
    initial_state: Dict[str, Any] = field(default_factory=dict)
    expected_final_state: Dict[str, Any] = field(default_factory=dict)


@dataclass
class ExtendedDSLModel:
    """扩展的DSL模型"""
    domain: str
    entities: List[ExtendedEntity] = field(default_factory=list)
    state_machines: List[StateMachine] = field(default_factory=list)
    test_requirements: List[TestRequirement] = field(default_factory=list)
    global_constraints: List[str] = field(default_factory=list)
    global_rules: List[Dict[str, Any]] = field(default_factory=list)
    
    def get_entity_by_name(self, name: str) -> Optional[ExtendedEntity]:
        """根据名称获取实体"""
        for entity in self.entities:
            if entity.name == name:
                return entity
        return None
    
    def get_state_machine_by_name(self, name: str) -> Optional[StateMachine]:
        """根据名称获取状态机"""
        for sm in self.state_machines:
            if sm.name == name:
                return sm
        return None