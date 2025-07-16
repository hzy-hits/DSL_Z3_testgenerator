"""
Generic Constraint Test Strategy Module
通用约束测试策略 - 基于DSL定义自动生成约束测试
"""

import re
import random
from typing import List, Dict, Any, Tuple, Optional
from .models import Entity, Test
from .test_strategies import TestStrategy
from .models_extended import ExtendedDSLModel


class GenericConstraintTestStrategy(TestStrategy):
    """通用约束测试策略 - 无需硬编码，完全基于DSL定义"""
    
    def __init__(self, value_generator, constraint_handler, dsl_model: ExtendedDSLModel):
        super().__init__(value_generator, constraint_handler)
        self.dsl_model = dsl_model
    
    def generate(self, entity: Entity) -> List[Test]:
        """为实体生成所有相关的约束测试"""
        tests = []
        
        # 1. 生成全局约束测试
        tests.extend(self._generate_global_constraint_tests(entity))
        
        # 2. 生成实体级约束测试
        tests.extend(self._generate_entity_constraint_tests(entity))
        
        # 3. 生成业务规则测试
        tests.extend(self._generate_business_rule_tests(entity))
        
        # 4. 生成跨实体约束测试
        tests.extend(self._generate_cross_entity_tests(entity))
        
        return tests
    
    def _generate_global_constraint_tests(self, entity: Entity) -> List[Test]:
        """生成全局约束测试"""
        tests = []
        
        for constraint in self.dsl_model.global_constraints:
            # 分析约束中涉及的属性
            involved_attrs = self._extract_attributes_from_constraint(constraint)
            
            # 检查此实体是否涉及这个约束
            entity_attrs = {attr.name for attr in entity.attributes}
            if not any(attr in entity_attrs for attr in involved_attrs):
                continue
            
            # 生成满足约束的测试
            valid_test = self._generate_constraint_satisfaction_test(entity, constraint)
            if valid_test:
                tests.append(valid_test)
            
            # 生成违反约束的测试
            invalid_test = self._generate_constraint_violation_test(entity, constraint)
            if invalid_test:
                tests.append(invalid_test)
            
            # 生成边界值测试
            boundary_tests = self._generate_constraint_boundary_tests(entity, constraint)
            tests.extend(boundary_tests)
        
        return tests
    
    def _generate_entity_constraint_tests(self, entity: Entity) -> List[Test]:
        """生成实体级约束测试"""
        tests = []
        
        for constraint in entity.constraints:
            # 满足约束的测试
            valid_test = self._generate_constraint_satisfaction_test(entity, constraint)
            if valid_test:
                tests.append(valid_test)
            
            # 违反约束的测试
            invalid_test = self._generate_constraint_violation_test(entity, constraint)
            if invalid_test:
                tests.append(invalid_test)
        
        return tests
    
    def _generate_business_rule_tests(self, entity: Entity) -> List[Test]:
        """生成业务规则测试"""
        tests = []
        
        for rule in self.dsl_model.global_rules:
            # 解析规则的条件和动作
            condition = str(rule.get('condition', ''))
            action = str(rule.get('action', ''))
            rule_name = rule.get('name', 'unnamed_rule')
            
            # 检查规则是否与当前实体相关
            if not self._is_rule_relevant_to_entity(rule, entity):
                continue
            
            # 生成规则触发测试（条件满足时）
            trigger_test = self._generate_rule_trigger_test(entity, rule)
            if trigger_test:
                tests.append(trigger_test)
            
            # 生成规则不触发测试（条件不满足时）
            no_trigger_test = self._generate_rule_no_trigger_test(entity, rule)
            if no_trigger_test:
                tests.append(no_trigger_test)
        
        return tests
    
    def _generate_cross_entity_tests(self, entity: Entity) -> List[Test]:
        """生成跨实体约束测试"""
        tests = []
        
        # 分析涉及多个实体的规则
        for rule in self.dsl_model.global_rules:
            condition = str(rule.get('condition', ''))
            
            # 检测跨实体引用（如 order_service_type 和 service_person_skill_daily）
            cross_entity_refs = self._detect_cross_entity_references(condition)
            if not cross_entity_refs:
                continue
            
            # 确保当前实体参与此跨实体规则
            involved_entities = set(ref.split('_')[0] for ref in cross_entity_refs)
            if entity.name.lower() not in involved_entities:
                continue
            
            # 生成跨实体约束测试
            cross_test = self._generate_cross_entity_constraint_test(entity, rule)
            if cross_test:
                tests.append(cross_test)
        
        return tests
    
    def _extract_attributes_from_constraint(self, constraint: str) -> List[str]:
        """从约束表达式中提取属性名"""
        # 使用正则表达式找出所有可能的属性名（标识符）
        pattern = r'\b[a-zA-Z_][a-zA-Z0-9_]*\b'
        tokens = re.findall(pattern, constraint)
        
        # 过滤掉关键字和操作符
        keywords = {'and', 'or', 'not', 'true', 'false', 'if', 'then', 'else', 
                   'min', 'max', 'size', 'len', 'abs', 'sum'}
        attributes = [token for token in tokens if token not in keywords]
        
        return attributes
    
    def _generate_constraint_satisfaction_test(self, entity: Entity, constraint: str) -> Optional[Test]:
        """生成满足约束的测试"""
        # 尝试多次生成满足约束的数据
        for attempt in range(10):
            data = self._generate_valid_data(entity)
            
            # 针对特定约束调整数据
            data = self._adjust_data_for_constraint(data, constraint, entity, satisfy=True)
            
            # 验证约束
            if self.constraint_handler.evaluate(constraint, data):
                return Test(
                    test_name=f"{entity.name}_constraint_satisfied_{attempt}",
                    test_type="constraint_satisfaction",
                    description=f"Test constraint satisfaction: {constraint}",
                    test_data=data,
                    constraint=constraint,
                    expected_result="pass",
                    priority=8
                )
        
        return None
    
    def _generate_constraint_violation_test(self, entity: Entity, constraint: str) -> Optional[Test]:
        """生成违反约束的测试"""
        # 尝试生成违反约束的数据
        for attempt in range(10):
            data = self._generate_valid_data(entity)
            
            # 针对特定约束调整数据以违反它
            data = self._adjust_data_for_constraint(data, constraint, entity, satisfy=False)
            
            # 验证约束确实被违反
            if not self.constraint_handler.evaluate(constraint, data):
                return Test(
                    test_name=f"{entity.name}_constraint_violated_{attempt}",
                    test_type="constraint_violation",
                    description=f"Test constraint violation: {constraint}",
                    test_data=data,
                    constraint=constraint,
                    expected_result="fail",
                    expected_error="constraint_violation",
                    priority=9
                )
        
        return None
    
    def _generate_constraint_boundary_tests(self, entity: Entity, constraint: str) -> List[Test]:
        """生成约束的边界值测试"""
        tests = []
        
        # 解析比较操作符和边界值
        boundaries = self._extract_boundaries_from_constraint(constraint)
        
        for attr_name, operator, value in boundaries:
            # 确保属性属于当前实体
            if not any(attr.name == attr_name for attr in entity.attributes):
                continue
            
            # 生成边界值测试数据
            data = self._generate_valid_data(entity)
            
            # 设置边界值
            if operator in ['<=', '>=']:
                data[attr_name] = value  # 刚好等于边界
            elif operator == '<':
                data[attr_name] = value - 0.01 if isinstance(value, float) else value - 1
            elif operator == '>':
                data[attr_name] = value + 0.01 if isinstance(value, float) else value + 1
            
            test = Test(
                test_name=f"{entity.name}_{attr_name}_boundary_{operator}_{value}",
                test_type="boundary",
                description=f"Test boundary condition: {attr_name} {operator} {value}",
                test_data=data,
                constraint=constraint,
                expected_result="pass",
                priority=7
            )
            tests.append(test)
        
        return tests
    
    def _extract_boundaries_from_constraint(self, constraint: str) -> List[Tuple[str, str, float]]:
        """从约束中提取边界条件"""
        boundaries = []
        
        # 匹配形如 "attribute <= value" 的模式
        pattern = r'(\w+)\s*([<>]=?)\s*([\d.]+)'
        matches = re.findall(pattern, constraint)
        
        for attr, op, val in matches:
            try:
                value = float(val) if '.' in val else int(val)
                boundaries.append((attr, op, value))
            except ValueError:
                continue
        
        return boundaries
    
    def _adjust_data_for_constraint(self, data: Dict[str, Any], constraint: str, 
                                   entity: Entity, satisfy: bool) -> Dict[str, Any]:
        """调整数据以满足或违反约束"""
        # 解析约束中的条件
        boundaries = self._extract_boundaries_from_constraint(constraint)
        
        for attr_name, operator, value in boundaries:
            if attr_name not in data:
                continue
            
            # 找到对应的属性定义
            attr = next((a for a in entity.attributes if a.name == attr_name), None)
            if not attr:
                continue
            
            if satisfy:
                # 调整数据以满足约束
                if operator == '<=':
                    data[attr_name] = min(data[attr_name], value)
                elif operator == '>=':
                    data[attr_name] = max(data[attr_name], value)
                elif operator == '<':
                    if data[attr_name] >= value:
                        data[attr_name] = value - (1 if attr.type in ['int', 'integer'] else 0.1)
                elif operator == '>':
                    if data[attr_name] <= value:
                        data[attr_name] = value + (1 if attr.type in ['int', 'integer'] else 0.1)
            else:
                # 调整数据以违反约束
                if operator == '<=':
                    data[attr_name] = value + (1 if attr.type in ['int', 'integer'] else 0.1)
                elif operator == '>=':
                    data[attr_name] = max(0, value - (1 if attr.type in ['int', 'integer'] else 0.1))
                elif operator == '<':
                    data[attr_name] = value + (1 if attr.type in ['int', 'integer'] else 0.1)
                elif operator == '>':
                    data[attr_name] = max(0, value - (1 if attr.type in ['int', 'integer'] else 0.1))
        
        return data
    
    def _is_rule_relevant_to_entity(self, rule: Dict[str, Any], entity: Entity) -> bool:
        """检查规则是否与实体相关"""
        condition = str(rule.get('condition', ''))
        action = str(rule.get('action', ''))
        
        # 检查条件或动作中是否包含实体的属性
        entity_attrs = {attr.name for attr in entity.attributes}
        rule_attrs = self._extract_attributes_from_constraint(condition + ' ' + action)
        
        # 检查是否有交集
        return bool(entity_attrs.intersection(rule_attrs))
    
    def _generate_rule_trigger_test(self, entity: Entity, rule: Dict[str, Any]) -> Optional[Test]:
        """生成规则触发测试"""
        condition = str(rule.get('condition', ''))
        action = str(rule.get('action', ''))
        rule_name = rule.get('name', 'unnamed_rule')
        
        # 生成满足条件的数据
        data = self._generate_valid_data(entity)
        data = self._adjust_data_for_constraint(data, condition, entity, satisfy=True)
        
        return Test(
            test_name=f"{entity.name}_rule_{rule_name}_triggered",
            test_type="business_rule",
            description=f"Test rule '{rule_name}' when condition is met",
            test_data=data,
            constraint=f"{condition} => {action}",
            expected_result="pass",
            priority=8
        )
    
    def _generate_rule_no_trigger_test(self, entity: Entity, rule: Dict[str, Any]) -> Optional[Test]:
        """生成规则不触发测试"""
        condition = str(rule.get('condition', ''))
        rule_name = rule.get('name', 'unnamed_rule')
        
        # 生成不满足条件的数据
        data = self._generate_valid_data(entity)
        data = self._adjust_data_for_constraint(data, condition, entity, satisfy=False)
        
        return Test(
            test_name=f"{entity.name}_rule_{rule_name}_not_triggered",
            test_type="business_rule",
            description=f"Test rule '{rule_name}' when condition is not met",
            test_data=data,
            constraint=f"NOT ({condition})",
            expected_result="pass",
            priority=7
        )
    
    def _detect_cross_entity_references(self, expression: str) -> List[str]:
        """检测跨实体引用"""
        # 查找形如 entity_attribute 的模式
        pattern = r'\b([a-z]+)_([a-z_]+)\b'
        matches = re.findall(pattern, expression)
        
        cross_refs = []
        for entity_part, attr_part in matches:
            # 检查是否是已知实体的引用
            for entity in self.dsl_model.entities:
                if entity_part == entity.name.lower():
                    cross_refs.append(f"{entity_part}_{attr_part}")
                    break
        
        return cross_refs
    
    def _generate_cross_entity_constraint_test(self, entity: Entity, rule: Dict[str, Any]) -> Optional[Test]:
        """生成跨实体约束测试"""
        condition = str(rule.get('condition', ''))
        action = str(rule.get('action', ''))
        rule_name = rule.get('name', 'unnamed_rule')
        
        # 生成基本数据
        data = self._generate_valid_data(entity)
        
        # 为跨实体引用生成模拟数据
        cross_refs = self._detect_cross_entity_references(condition + ' ' + action)
        for ref in cross_refs:
            if ref not in data:
                # 根据引用类型生成合理的值
                if 'skill' in ref and 'true' in action:
                    data[ref] = True
                elif 'type' in ref:
                    data[ref] = random.randint(1, 5)
                else:
                    data[ref] = random.randint(1, 100)
        
        return Test(
            test_name=f"{entity.name}_cross_entity_{rule_name}",
            test_type="business_rule",
            description=f"Test cross-entity rule: {rule_name}",
            test_data=data,
            constraint=f"{condition} => {action}",
            expected_result="pass",
            priority=9
        )