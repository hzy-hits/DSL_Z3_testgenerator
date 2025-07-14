"""
Scenario Test Strategy
场景测试策略 - 生成业务流程测试
"""

from typing import List, Dict, Any, Optional, Tuple
from .models import Test
from .models_extended import ExtendedEntity, ExtendedDSLModel, TestRequirement, ScenarioStep, TestScenario
from abc import ABC
from .value_generator import ValueGenerator
import re


class ScenarioTestStrategy:
    """场景测试策略"""
    
    def __init__(self, dsl_model: Optional[ExtendedDSLModel] = None):
        self.value_generator = ValueGenerator()
        self.dsl_model = dsl_model
        # 预定义的业务场景模板
        self.scenario_templates = {
            'dispatch_flow': self._create_dispatch_flow_scenario,
            'order_lifecycle': self._create_order_lifecycle_scenario,
            'rejection_handling': self._create_rejection_handling_scenario,
            'modification_flow': self._create_modification_flow_scenario,
            'timeout_handling': self._create_timeout_handling_scenario
        }
    
    def generate_tests(self, entity: ExtendedEntity, existing_tests: List[Test]) -> List[Test]:
        """生成场景测试"""
        tests = []
        
        # 1. 基于测试需求生成场景测试
        if self.dsl_model:
            tests.extend(self._generate_requirement_based_scenarios(entity))
        
        # 2. 基于业务规则生成场景测试
        tests.extend(self._generate_rule_based_scenarios(entity))
        
        # 3. 基于预定义模板生成场景测试
        tests.extend(self._generate_template_based_scenarios(entity))
        
        # 4. 生成端到端流程测试
        tests.extend(self._generate_e2e_scenarios(entity))
        
        return tests
    
    def _generate_requirement_based_scenarios(self, entity: ExtendedEntity) -> List[Test]:
        """基于测试需求生成场景"""
        tests = []
        
        if not self.dsl_model:
            return tests
        
        # 查找场景类型的测试需求
        scenario_requirements = [req for req in self.dsl_model.test_requirements 
                               if req.type == 'scenario']
        
        for req in scenario_requirements:
            # 检查是否与当前实体相关
            if self._is_requirement_relevant(req, entity):
                scenario = self._create_scenario_from_requirement(req, entity)
                test = self._scenario_to_test(scenario, entity.name)
                tests.append(test)
        
        return tests
    
    def _generate_rule_based_scenarios(self, entity: ExtendedEntity) -> List[Test]:
        """基于业务规则生成场景"""
        tests = []
        
        # 分析规则之间的关联，生成组合场景
        rule_chains = self._analyze_rule_chains(entity)
        
        for i, chain in enumerate(rule_chains[:5]):  # 限制生成5个规则链场景
            scenario = self._create_scenario_from_rule_chain(chain, entity)
            test = self._scenario_to_test(scenario, entity.name)
            tests.append(test)
        
        return tests
    
    def _generate_template_based_scenarios(self, entity: ExtendedEntity) -> List[Test]:
        """基于预定义模板生成场景"""
        tests = []
        
        # 根据实体类型选择合适的模板
        entity_type = self._identify_entity_type(entity)
        
        for template_name, template_func in self.scenario_templates.items():
            if self._is_template_applicable(template_name, entity_type):
                scenario = template_func(entity)
                if scenario:
                    test = self._scenario_to_test(scenario, entity.name)
                    tests.append(test)
        
        return tests
    
    def _generate_e2e_scenarios(self, entity: ExtendedEntity) -> List[Test]:
        """生成端到端场景测试"""
        tests = []
        
        # 如果实体有状态机，生成完整生命周期测试
        if entity.state_machines:
            for state_machine in entity.state_machines:
                scenario = self._create_lifecycle_scenario(entity, state_machine)
                test = self._scenario_to_test(scenario, entity.name)
                tests.append(test)
        
        return tests
    
    def _create_scenario_from_requirement(self, req: TestRequirement, 
                                        entity: ExtendedEntity) -> TestScenario:
        """从测试需求创建场景"""
        scenario = TestScenario(
            name=f"{req.name}_scenario",
            description=req.description
        )
        
        # 根据需求条件创建步骤
        for i, condition in enumerate(req.conditions):
            step = ScenarioStep(
                action=f"Apply condition: {condition}",
                entity=entity.name,
                timing=i * 5  # 每步间隔5分钟
            )
            
            # 解析条件以设置状态变化
            state_change = self._parse_condition_to_state_change(condition, entity)
            step.state_change = state_change
            
            scenario.steps.append(step)
        
        return scenario
    
    def _create_scenario_from_rule_chain(self, rule_chain: List[Dict[str, Any]], 
                                       entity: ExtendedEntity) -> TestScenario:
        """从规则链创建场景"""
        chain_names = [rule.get('name', 'rule') for rule in rule_chain]
        scenario = TestScenario(
            name=f"rule_chain_{'_'.join(chain_names[:3])}",
            description=f"Test rule chain: {' -> '.join(chain_names)}"
        )
        
        cumulative_state = {}
        
        for i, rule in enumerate(rule_chain):
            # 创建触发规则的步骤
            step = ScenarioStep(
                action=f"Trigger rule: {rule.get('name', '')}",
                entity=entity.name,
                timing=i * 10
            )
            
            # 设置满足规则条件的状态
            condition = rule.get('condition', '')
            state_change = self._parse_condition_to_state_change(condition, entity)
            cumulative_state.update(state_change)
            step.state_change = cumulative_state.copy()
            
            # 设置期望结果（规则的动作）
            action = rule.get('action', '')
            step.expected_result = self._parse_action_to_result(action)
            
            scenario.steps.append(step)
        
        return scenario
    
    def _create_dispatch_flow_scenario(self, entity: ExtendedEntity) -> Optional[TestScenario]:
        """创建派单流程场景"""
        if 'dispatch' not in entity.name.lower() and 'order' not in entity.name.lower():
            return None
        
        scenario = TestScenario(
            name="complete_dispatch_flow",
            description="完整的派单流程测试：从创建预约到派单成功"
        )
        
        # 步骤1：创建预约单
        scenario.steps.append(ScenarioStep(
            action="创建新的预约单",
            entity="ReserveOrder",
            state_change={'reserve_status': 1, 'service_time_minutes': 180},
            expected_result={'reserve_order_created': True},
            timing=0
        ))
        
        # 步骤2：系统派单
        scenario.steps.append(ScenarioStep(
            action="系统自动派单",
            entity="DispatchOrder",
            state_change={'dispatch_status': 2, 'dispatch_type': 1},
            expected_result={'dispatch_success': True, 'notification_sent': True},
            timing=5
        ))
        
        # 步骤3：服务人员查看
        scenario.steps.append(ScenarioStep(
            action="服务人员查看订单",
            entity="TakeOrderRecord",
            state_change={'record_status': 2, 'view_time_minutes': 10},
            expected_result={'order_viewed': True},
            timing=10
        ))
        
        # 步骤4：服务人员接单
        scenario.steps.append(ScenarioStep(
            action="服务人员确认接单",
            entity="TakeOrderRecord",
            state_change={'record_status': 3},
            expected_result={'order_accepted': True, 'inventory_updated': True},
            timing=15
        ))
        
        return scenario
    
    def _create_order_lifecycle_scenario(self, entity: ExtendedEntity) -> Optional[TestScenario]:
        """创建订单生命周期场景"""
        if 'order' not in entity.name.lower():
            return None
        
        scenario = TestScenario(
            name="order_complete_lifecycle",
            description="订单完整生命周期测试：从创建到完成"
        )
        
        # 包含创建、派单、接单、服务、完成的完整流程
        lifecycle_steps = [
            ("创建订单", {'order_status': 1}, 0),
            ("派单成功", {'order_status': 2}, 10),
            ("服务人员接单", {'order_status': 3}, 20),
            ("开始服务", {'order_status': 4}, 180),
            ("完成服务", {'order_status': 5}, 240)
        ]
        
        for action, state_change, timing in lifecycle_steps:
            scenario.steps.append(ScenarioStep(
                action=action,
                entity=entity.name,
                state_change=state_change,
                timing=timing
            ))
        
        return scenario
    
    def _create_rejection_handling_scenario(self, entity: ExtendedEntity) -> Optional[TestScenario]:
        """创建拒单处理场景"""
        if 'dispatch' not in entity.name.lower():
            return None
        
        scenario = TestScenario(
            name="rejection_and_reassignment",
            description="服务人员拒单及重新派单流程"
        )
        
        # 拒单场景步骤
        scenario.steps.extend([
            ScenarioStep(
                action="初始派单",
                entity="DispatchOrder",
                state_change={'dispatch_status': 2, 'service_time_minutes': 120},
                timing=0
            ),
            ScenarioStep(
                action="服务人员拒单",
                entity="TakeOrderRecord",
                state_change={'record_status': 4, 'reject_reason': 1},
                expected_result={'dispatch_status': 4},
                timing=10
            ),
            ScenarioStep(
                action="系统重新派单",
                entity="DispatchOrder",
                state_change={'dispatch_status': 2, 'is_reassignment': True},
                expected_result={'new_provider_assigned': True},
                timing=15
            )
        ])
        
        return scenario
    
    def _create_modification_flow_scenario(self, entity: ExtendedEntity) -> Optional[TestScenario]:
        """创建改约流程场景"""
        if 'order' not in entity.name.lower():
            return None
        
        scenario = TestScenario(
            name="order_modification_flow",
            description="用户修改预约时间的完整流程"
        )
        
        scenario.steps.extend([
            ScenarioStep(
                action="原始预约已派单",
                entity="ReserveOrder",
                state_change={'reserve_status': 2, 'service_time_minutes': 180},
                timing=0
            ),
            ScenarioStep(
                action="用户请求修改时间",
                entity="ReserveOrder",
                state_change={'is_modified': True, 'service_time_minutes': 240},
                expected_result={'modification_allowed': True},
                timing=30
            ),
            ScenarioStep(
                action="系统评估是否需要换人",
                entity="DispatchOrder",
                state_change={'is_reassignment': True},
                expected_result={'provider_evaluation_complete': True},
                timing=31
            ),
            ScenarioStep(
                action="通知相关人员",
                entity="Notification",
                state_change={'message_type': 4, 'is_sent': True},
                expected_result={'notifications_sent': True},
                timing=32
            )
        ])
        
        return scenario
    
    def _create_timeout_handling_scenario(self, entity: ExtendedEntity) -> Optional[TestScenario]:
        """创建超时处理场景"""
        scenario = TestScenario(
            name="dispatch_timeout_handling",
            description="派单超时自动处理流程"
        )
        
        scenario.steps.extend([
            ScenarioStep(
                action="创建预约单",
                entity="ReserveOrder",
                state_change={'reserve_status': 1, 'service_time_minutes': 90},
                timing=0
            ),
            ScenarioStep(
                action="等待10分钟未派单",
                entity="DispatchOrder",
                state_change={'dispatch_status': 1, 'minutes_since_created': 11},
                expected_result={'timeout_notification_sent': True},
                timing=11
            ),
            ScenarioStep(
                action="继续等待至服务前1小时",
                entity="DispatchOrder",
                state_change={'service_time_minutes': 59},
                timing=31
            ),
            ScenarioStep(
                action="系统自动取消",
                entity="DispatchOrder",
                state_change={'dispatch_status': 6},
                expected_result={'auto_cancelled': True, 'cancel_notification_sent': True},
                timing=32
            )
        ])
        
        return scenario
    
    def _create_lifecycle_scenario(self, entity: ExtendedEntity, state_machine) -> TestScenario:
        """基于状态机创建生命周期场景"""
        scenario = TestScenario(
            name=f"{state_machine.name}_complete_lifecycle",
            description=f"Complete lifecycle test for {state_machine.name}"
        )
        
        # 获取一条从初始到结束的完整路径
        paths = state_machine.get_all_paths(max_depth=10)
        if paths:
            # 选择最长的路径
            longest_path = max(paths, key=len)
            
            current_time = 0
            for transition in longest_path:
                step = ScenarioStep(
                    action=f"Execute transition: {transition.name}",
                    entity=entity.name,
                    state_change={state_machine.state_attribute: 
                                state_machine.get_state_by_name(transition.to_state).value},
                    timing=current_time
                )
                
                # 添加转换条件
                if transition.condition:
                    condition_state = self._parse_condition_to_state_change(transition.condition, entity)
                    step.state_change.update(condition_state)
                
                scenario.steps.append(step)
                current_time += 10
        
        return scenario
    
    def _scenario_to_test(self, scenario: TestScenario, entity_name: str) -> Test:
        """将场景转换为测试用例"""
        # 构建测试数据
        test_data = {
            'scenario_name': scenario.name,
            'initial_state': scenario.initial_state,
            'steps': []
        }
        
        for step in scenario.steps:
            step_data = {
                'action': step.action,
                'entity': step.entity,
                'timing': step.timing,
                'state_change': step.state_change,
                'expected_result': step.expected_result
            }
            test_data['steps'].append(step_data)
        
        test_data['expected_final_state'] = scenario.expected_final_state
        
        return Test(
            test_name=f"{entity_name}_scenario_{scenario.name}",
            test_type="scenario",
            description=scenario.description,
            test_data=test_data,
            expected_result="pass",
            priority=9,
            entity=entity_name
        )
    
    def _analyze_rule_chains(self, entity: ExtendedEntity) -> List[List[Dict[str, Any]]]:
        """分析规则之间的关联，找出规则链"""
        rule_chains = []
        rules = entity.rules
        
        # 简单策略：查找动作可能触发其他规则条件的规则链
        for i, rule1 in enumerate(rules):
            chain = [rule1]
            
            # 查找可能被rule1动作触发的规则
            for rule2 in rules[i+1:]:
                if self._can_trigger(rule1, rule2):
                    chain.append(rule2)
                    if len(chain) >= 3:  # 限制链长度
                        break
            
            if len(chain) > 1:
                rule_chains.append(chain)
        
        return rule_chains[:5]  # 返回前5个规则链
    
    def _can_trigger(self, rule1: Dict[str, Any], rule2: Dict[str, Any]) -> bool:
        """判断rule1的动作是否可能触发rule2的条件"""
        action1 = str(rule1.get('action', ''))
        condition2 = str(rule2.get('condition', ''))
        
        # 简单的启发式判断
        # 如果rule1的动作中提到的属性出现在rule2的条件中
        action_attrs = re.findall(r'\b(\w+)\b', action1)
        
        for attr in action_attrs:
            if attr in condition2:
                return True
        
        return False
    
    def _is_requirement_relevant(self, req: TestRequirement, entity: ExtendedEntity) -> bool:
        """判断测试需求是否与实体相关"""
        # 检查focus中是否包含实体名或实体的属性
        for focus_item in req.focus:
            if focus_item == entity.name:
                return True
            if any(attr.name == focus_item for attr in entity.attributes):
                return True
        
        return False
    
    def _identify_entity_type(self, entity: ExtendedEntity) -> str:
        """识别实体类型"""
        entity_name_lower = entity.name.lower()
        
        if 'dispatch' in entity_name_lower:
            return 'dispatch'
        elif 'order' in entity_name_lower:
            return 'order'
        elif 'provider' in entity_name_lower or 'technician' in entity_name_lower:
            return 'provider'
        elif 'notification' in entity_name_lower:
            return 'notification'
        else:
            return 'generic'
    
    def _is_template_applicable(self, template_name: str, entity_type: str) -> bool:
        """判断模板是否适用于实体类型"""
        template_mapping = {
            'dispatch_flow': ['dispatch', 'order'],
            'order_lifecycle': ['order'],
            'rejection_handling': ['dispatch'],
            'modification_flow': ['order'],
            'timeout_handling': ['dispatch', 'order']
        }
        
        return entity_type in template_mapping.get(template_name, [])
    
    def _parse_condition_to_state_change(self, condition: str, entity: ExtendedEntity) -> Dict[str, Any]:
        """解析条件为状态变化"""
        state_change = {}
        
        # 解析等式条件
        equals = re.findall(r'(\w+)\s*==\s*(\w+)', condition)
        for attr, value in equals:
            # 尝试转换为正确的类型
            if value.isdigit():
                state_change[attr] = int(value)
            elif value in ['true', 'false']:
                state_change[attr] = value == 'true'
            else:
                state_change[attr] = value
        
        # 解析比较条件，设置满足条件的值
        comparisons = re.findall(r'(\w+)\s*([><]=?)\s*(\d+)', condition)
        for attr, op, value in comparisons:
            value = int(value)
            if op == '>':
                state_change[attr] = value + 10
            elif op == '>=':
                state_change[attr] = value
            elif op == '<':
                state_change[attr] = value - 10
            elif op == '<=':
                state_change[attr] = value
        
        return state_change
    
    def _parse_action_to_result(self, action: str) -> Dict[str, Any]:
        """解析动作为期望结果"""
        result = {}
        
        # 识别常见的动作模式
        if 'send_notification' in action:
            result['notification_sent'] = True
        if 'update' in action:
            result['state_updated'] = True
        if 'create' in action:
            result['object_created'] = True
        if 'cancel' in action:
            result['cancelled'] = True
        if 'dispatch' in action:
            result['dispatched'] = True
        
        return result