#!/usr/bin/env python3
"""
统一的 DSL 测试生成器 V2 - 增强版
改进了 DSL 解析和 Z3 求解器的协同，支持更多高级特性
"""

import argparse
import json
import yaml
import z3
from typing import List, Dict, Any, Set, Tuple, Optional, Union
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
import re
from datetime import datetime
import hashlib


class TestType(Enum):
    """测试类型枚举"""
    FUNCTIONAL = "functional"
    BOUNDARY = "boundary"
    NEGATIVE = "negative"
    RULE_ACTIVATION = "rule_activation"
    RULE_DEACTIVATION = "rule_deactivation"
    CONSTRAINT_SATISFACTION = "constraint_satisfaction"
    CONSTRAINT_VIOLATION = "constraint_violation"
    SCENARIO = "scenario"
    STATE_TRANSITION = "state_transition"
    COMBINATORIAL = "combinatorial"


@dataclass
class AttributeMetadata:
    """属性元数据"""
    name: str
    type: str
    min: Optional[Union[int, float]] = None
    max: Optional[Union[int, float]] = None
    enum: Optional[List[Any]] = None
    pattern: Optional[str] = None
    optional: bool = False
    default: Optional[Any] = None
    unique: bool = False
    nullable: bool = False
    description: Optional[str] = None
    
    @property
    def is_numeric(self) -> bool:
        return self.type in ['integer', 'real']
    
    @property
    def is_collection(self) -> bool:
        return self.type.startswith('array[') or self.type.startswith('set[')
    
    @property
    def element_type(self) -> Optional[str]:
        if self.type.startswith('array['):
            return self.type[6:-1]
        elif self.type.startswith('set['):
            return self.type[4:-1]
        return None


@dataclass
class UnifiedTest:
    """统一的测试用例格式"""
    id: str
    name: str
    type: TestType
    description: str
    rationale: str
    test_data: Dict[str, Any]
    expected_result: str
    coverage_points: List[str] = field(default_factory=list)
    constraints_tested: List[str] = field(default_factory=list)
    rules_tested: List[str] = field(default_factory=list)
    priority: int = 5
    tags: List[str] = field(default_factory=list)
    
    def to_dict(self):
        """转换为字典格式"""
        return {
            "id": self.id,
            "name": self.name,
            "type": self.type.value,
            "description": self.description,
            "rationale": self.rationale,
            "test_data": self.test_data,
            "expected_result": self.expected_result,
            "coverage_points": self.coverage_points,
            "constraints_tested": self.constraints_tested,
            "rules_tested": self.rules_tested,
            "priority": self.priority,
            "tags": self.tags
        }


class EnhancedZ3Engine:
    """增强的 Z3 约束求解引擎"""
    
    def __init__(self):
        self.solver = z3.Solver()
        self.optimizer = z3.Optimize()  # 用于找最优解
        self.variables = {}
        self.array_vars = {}
        self.set_vars = {}
        self.optional_vars = {}  # 跟踪可选字段
        self.metadata = {}  # 存储属性元数据
        
    def create_variables_from_entities(self, entities: List[Dict[str, Any]]):
        """从实体定义创建 Z3 变量"""
        for entity in entities:
            entity_name = entity['name'].lower()
            
            for attr in entity.get('attributes', []):
                # 创建属性元数据
                attr_meta = AttributeMetadata(
                    name=attr['name'],
                    type=attr.get('type', 'string'),
                    min=attr.get('min'),
                    max=attr.get('max'),
                    enum=attr.get('enum'),
                    pattern=attr.get('pattern'),
                    optional=attr.get('optional', False),
                    default=attr.get('default'),
                    unique=attr.get('unique', False),
                    nullable=attr.get('nullable', False),
                    description=attr.get('description')
                )
                
                var_name = f"{entity_name}_{attr_meta.name}"
                self.metadata[var_name] = attr_meta
                
                # 创建主变量
                self._create_variable(var_name, attr_meta)
                
                # 如果是可选字段，创建存在标志
                if attr_meta.optional:
                    exists_var = z3.Bool(f"{var_name}_exists")
                    self.optional_vars[var_name] = exists_var
                    
                    # 如果字段不存在，其值应该是默认值或null
                    if attr_meta.default is not None:
                        self._add_optional_constraint(var_name, attr_meta)
    
    def _create_variable(self, var_name: str, attr_meta: AttributeMetadata):
        """创建单个 Z3 变量"""
        attr_type = attr_meta.type
        
        if attr_type == 'integer':
            var = z3.Int(var_name)
            self.variables[var_name] = var
            
            # 添加范围约束
            if attr_meta.min is not None:
                self.solver.add(var >= attr_meta.min)
            if attr_meta.max is not None:
                self.solver.add(var <= attr_meta.max)
                
        elif attr_type == 'real':
            var = z3.Real(var_name)
            self.variables[var_name] = var
            
            if attr_meta.min is not None:
                self.solver.add(var >= attr_meta.min)
            if attr_meta.max is not None:
                self.solver.add(var <= attr_meta.max)
                
        elif attr_type == 'boolean':
            var = z3.Bool(var_name)
            self.variables[var_name] = var
            
        elif attr_type == 'string':
            if attr_meta.enum:
                # 使用整数编码枚举
                var = z3.Int(var_name)
                self.variables[var_name] = var
                self.solver.add(var >= 0)
                self.solver.add(var < len(attr_meta.enum))
            else:
                # 使用字符串理论或整数编码
                var = z3.Int(var_name)
                self.variables[var_name] = var
                
        elif attr_meta.is_collection:
            self._create_collection_variable(var_name, attr_meta)
    
    def _create_collection_variable(self, var_name: str, attr_meta: AttributeMetadata):
        """创建集合类型变量"""
        element_type = attr_meta.element_type
        
        if attr_meta.type.startswith('array['):
            # 数组实现
            self.array_vars[var_name] = {
                'array': z3.Array(var_name, z3.IntSort(), z3.IntSort()),
                'size': z3.Int(f"{var_name}_size"),
                'element_type': element_type,
                'metadata': attr_meta
            }
            
            # 数组大小约束
            size_var = self.array_vars[var_name]['size']
            self.solver.add(size_var >= 0)
            
            if attr_meta.max is not None:
                self.solver.add(size_var <= attr_meta.max)
            elif 'max_size' in attr_meta.__dict__:
                self.solver.add(size_var <= attr_meta.max_size)
            else:
                self.solver.add(size_var <= 100)  # 默认最大100
                
        elif attr_meta.type.startswith('set['):
            # 集合实现（使用特征函数）
            self.set_vars[var_name] = {
                'set': z3.Array(var_name, z3.IntSort(), z3.BoolSort()),
                'size': z3.Int(f"{var_name}_size"),
                'element_type': element_type,
                'metadata': attr_meta
            }
            
            size_var = self.set_vars[var_name]['size']
            self.solver.add(size_var >= 0)
            
            if attr_meta.max is not None:
                self.solver.add(size_var <= attr_meta.max)
            else:
                self.solver.add(size_var <= 50)  # 默认最大50
    
    def _add_optional_constraint(self, var_name: str, attr_meta: AttributeMetadata):
        """添加可选字段的约束"""
        exists_var = self.optional_vars[var_name]
        
        if attr_meta.default is not None:
            # 如果有默认值，不存在时使用默认值
            if var_name in self.variables:
                var = self.variables[var_name]
                default_val = self._convert_default_to_z3(attr_meta.default, attr_meta.type)
                
                # 不存在时等于默认值
                self.solver.add(z3.Implies(z3.Not(exists_var), var == default_val))
    
    def _convert_default_to_z3(self, default_value: Any, attr_type: str):
        """将默认值转换为 Z3 表达式"""
        if attr_type == 'integer':
            return int(default_value)
        elif attr_type == 'real':
            return float(default_value)
        elif attr_type == 'boolean':
            return bool(default_value)
        elif attr_type == 'string':
            # 字符串默认值需要特殊处理
            return 0  # 简化处理
        return default_value
    
    def add_constraint(self, constraint: str, context: Dict[str, Any] = None):
        """添加约束到求解器"""
        z3_constraint = self._parse_constraint(constraint, context)
        if z3_constraint is not None:
            self.solver.add(z3_constraint)
    
    def add_rule(self, rule: Dict[str, Any]):
        """添加规则到求解器"""
        # 支持更复杂的规则格式
        if 'condition' in rule and 'implies' in rule:
            # 新格式：condition -> implies
            condition = self._parse_constraint(rule['condition'])
            implies = self._parse_constraint(rule['implies'])
            
            if condition is not None and implies is not None:
                self.solver.add(z3.Implies(condition, implies))
        else:
            # 旧格式：if -> then
            if_condition = self._parse_constraint(rule.get('if', 'true'))
            then_condition = self._parse_constraint(rule.get('then', 'true'))
            
            if if_condition is not None and then_condition is not None:
                self.solver.add(z3.Or(z3.Not(if_condition), then_condition))
    
    def solve_with_strategy(self, strategy: str = "minimal", 
                          additional_constraints: List[Any] = None) -> Optional[Dict[str, Any]]:
        """使用特定策略求解"""
        self.solver.push()
        
        if additional_constraints:
            for constraint in additional_constraints:
                self.solver.add(constraint)
        
        # 根据策略添加优化目标
        if strategy == "minimal":
            # 最小化数值
            for var_name, var in self.variables.items():
                if var_name in self.metadata:
                    meta = self.metadata[var_name]
                    if meta.is_numeric and not self._is_special_field(var_name):
                        self.optimizer.minimize(var)
                        
        elif strategy == "maximal":
            # 最大化数值
            for var_name, var in self.variables.items():
                if var_name in self.metadata:
                    meta = self.metadata[var_name]
                    if meta.is_numeric and not self._is_special_field(var_name):
                        self.optimizer.maximize(var)
                        
        elif strategy == "realistic":
            # 使用现实的值
            self._add_realistic_constraints()
        
        # 求解
        if self.solver.check() == z3.sat:
            model = self.solver.model()
            values = self._extract_values_from_model(model)
            self.solver.pop()
            return values
        else:
            self.solver.pop()
            return None
    
    def _is_special_field(self, var_name: str) -> bool:
        """检查是否是特殊字段（如ID、时间戳等）"""
        special_patterns = ['_id', '_at', 'created', 'updated', 'timestamp']
        return any(pattern in var_name.lower() for pattern in special_patterns)
    
    def _add_realistic_constraints(self):
        """添加现实约束"""
        for var_name, var in self.variables.items():
            if var_name in self.metadata:
                meta = self.metadata[var_name]
                
                # 金额类字段
                if any(keyword in var_name for keyword in ['amount', 'price', 'cost', 'balance']):
                    if meta.type == 'integer':
                        self.solver.add(var >= 10)
                        self.solver.add(var <= 10000)
                    elif meta.type == 'real':
                        self.solver.add(var >= 10.0)
                        self.solver.add(var <= 10000.0)
                
                # 数量类字段
                elif any(keyword in var_name for keyword in ['count', 'quantity', 'number']):
                    if meta.type == 'integer':
                        self.solver.add(var >= 1)
                        self.solver.add(var <= 100)
                
                # 百分比字段
                elif any(keyword in var_name for keyword in ['percent', 'rate', 'ratio']):
                    if meta.type == 'real':
                        self.solver.add(var >= 0.0)
                        self.solver.add(var <= 100.0)
    
    def _extract_values_from_model(self, model) -> Dict[str, Any]:
        """从 Z3 模型提取值"""
        values = {}
        
        # 提取标量值
        for var_name, var in self.variables.items():
            val = model.eval(var)
            
            # 处理可选字段
            if var_name in self.optional_vars:
                exists = model.eval(self.optional_vars[var_name])
                if z3.is_false(exists):
                    continue  # 跳过不存在的字段
            
            # 转换值
            if z3.is_int_value(val):
                values[var_name] = val.as_long()
            elif z3.is_rational_value(val):
                values[var_name] = float(val.as_fraction())
            elif z3.is_true(val):
                values[var_name] = True
            elif z3.is_false(val):
                values[var_name] = False
            else:
                # 尝试强制求值
                try:
                    if z3.is_bool(var):
                        values[var_name] = z3.is_true(model.eval(var, model_completion=True))
                    else:
                        values[var_name] = str(val)
                except:
                    values[var_name] = str(val)
        
        # 提取数组值
        for var_name, array_info in self.array_vars.items():
            size = model.eval(array_info['size']).as_long()
            values[var_name] = []
            
            # 生成数组元素
            for i in range(min(size, 10)):  # 限制最多10个元素
                elem = model.eval(array_info['array'][i])
                if z3.is_int_value(elem):
                    values[var_name].append(elem.as_long())
        
        # 提取集合值
        for var_name, set_info in self.set_vars.items():
            size = model.eval(set_info['size']).as_long()
            values[var_name] = []
            
            # 生成集合元素
            added = 0
            for i in range(1000):  # 搜索范围
                if added >= min(size, 10):
                    break
                is_member = model.eval(set_info['set'][i])
                if z3.is_true(is_member):
                    values[var_name].append(i)
                    added += 1
        
        return values
    
    def _parse_constraint(self, constraint: str, context: Dict[str, Any] = None) -> Optional[Any]:
        """解析约束表达式为 Z3 表达式（增强版）"""
        if not constraint or constraint == 'true':
            return z3.BoolVal(True)
        if constraint == 'false':
            return z3.BoolVal(False)
        
        # 处理复杂的逻辑表达式
        return self._parse_expression(constraint, context)
    
    def _parse_expression(self, expr: str, context: Dict[str, Any] = None) -> Optional[Any]:
        """递归解析表达式"""
        # 处理布尔值
        if isinstance(expr, bool):
            return z3.BoolVal(expr)
        
        # 确保是字符串
        if not isinstance(expr, str):
            expr = str(expr)
            
        expr = expr.strip()
        
        # 处理括号
        if expr.startswith('(') and expr.endswith(')'):
            return self._parse_expression(expr[1:-1], context)
        
        # 处理逻辑运算符（优先级：not > and > or > ->）
        
        # 蕴含运算符
        if ' -> ' in expr:
            parts = expr.split(' -> ', 1)
            left = self._parse_expression(parts[0], context)
            right = self._parse_expression(parts[1], context)
            if left is not None and right is not None:
                return z3.Implies(left, right)
        
        # OR 运算符
        if ' or ' in expr:
            parts = expr.split(' or ')
            exprs = [self._parse_expression(p.strip(), context) for p in parts]
            if all(e is not None for e in exprs):
                return z3.Or(*exprs)
        
        # AND 运算符
        if ' and ' in expr:
            parts = expr.split(' and ')
            exprs = [self._parse_expression(p.strip(), context) for p in parts]
            if all(e is not None for e in exprs):
                return z3.And(*exprs)
        
        # NOT 运算符
        if expr.startswith('not '):
            sub_expr = self._parse_expression(expr[4:], context)
            if sub_expr is not None:
                return z3.Not(sub_expr)
        
        # 处理比较运算符
        for op in ['>=', '<=', '==', '!=', '>', '<']:
            if op in expr:
                parts = expr.split(op)
                if len(parts) == 2:
                    left = self._get_value(parts[0].strip(), context)
                    right = self._get_value(parts[1].strip(), context)
                    if left is not None and right is not None:
                        return self._apply_operator(left, op, right)
        
        # 处理集合操作
        if ' in ' in expr:
            parts = expr.split(' in ')
            if len(parts) == 2:
                elem = self._get_value(parts[0].strip(), context)
                set_name = parts[1].strip()
                if set_name in self.set_vars and elem is not None:
                    return self.set_vars[set_name]['set'][elem]
        
        # 处理函数调用
        if '(' in expr and ')' in expr:
            return self._parse_function_call(expr, context)
        
        # 如果无法解析，返回 None
        return None
    
    def _parse_function_call(self, expr: str, context: Dict[str, Any] = None) -> Optional[Any]:
        """解析函数调用"""
        match = re.match(r'(\w+)\((.*)\)', expr)
        if match:
            func_name = match.group(1)
            args = match.group(2)
            
            if func_name == 'size' or func_name == 'length':
                var_name = args.strip()
                if var_name in self.array_vars:
                    return self.array_vars[var_name]['size']
                elif var_name in self.set_vars:
                    return self.set_vars[var_name]['size']
            
            elif func_name == 'count':
                # count(set, condition) - 计算满足条件的元素数量
                # 简化实现
                pass
            
            elif func_name == 'sum':
                # sum(array) - 数组求和
                # 需要更复杂的实现
                pass
        
        return None
    
    def _get_value(self, expr_str: str, context: Dict[str, Any] = None):
        """获取表达式的值"""
        expr_str = expr_str.strip()
        
        # 常量
        if expr_str.isdigit() or (expr_str.startswith('-') and expr_str[1:].isdigit()):
            return int(expr_str)
        if expr_str.replace('.', '').replace('-', '').isdigit():
            return float(expr_str)
        if expr_str == 'true':
            return z3.BoolVal(True)
        if expr_str == 'false':
            return z3.BoolVal(False)
        
        # 字符串常量
        if expr_str.startswith('"') and expr_str.endswith('"'):
            return expr_str[1:-1]
        
        # 变量
        if expr_str in self.variables:
            return self.variables[expr_str]
        
        # 数组/集合大小
        if expr_str.endswith('_size'):
            base_name = expr_str[:-5]
            if base_name in self.array_vars:
                return self.array_vars[base_name]['size']
            if base_name in self.set_vars:
                return self.set_vars[base_name]['size']
        
        # 从上下文获取
        if context and expr_str in context:
            return context[expr_str]
        
        return None
    
    def _apply_operator(self, left, op: str, right):
        """应用运算符"""
        if op == '>=':
            return left >= right
        elif op == '<=':
            return left <= right
        elif op == '==':
            return left == right
        elif op == '!=':
            return left != right
        elif op == '>':
            return left > right
        elif op == '<':
            return left < right
        return None


class SmartTestDeduplicator:
    """智能测试去重器"""
    
    def __init__(self):
        self.test_signatures = {}
        self.coverage_map = {}  # 跟踪覆盖情况
        
    def deduplicate(self, tests: List[UnifiedTest]) -> List[UnifiedTest]:
        """智能去重"""
        # 第一步：基于签名去重
        unique_by_signature = self._deduplicate_by_signature(tests)
        
        # 第二步：基于覆盖去重
        optimized = self._optimize_by_coverage(unique_by_signature)
        
        # 第三步：确保关键测试不被删除
        final_tests = self._ensure_critical_tests(optimized)
        
        return final_tests
    
    def _deduplicate_by_signature(self, tests: List[UnifiedTest]) -> List[UnifiedTest]:
        """基于测试签名去重"""
        unique_tests = []
        
        for test in tests:
            sig = self._create_signature(test)
            
            if sig not in self.test_signatures:
                self.test_signatures[sig] = test
                unique_tests.append(test)
                
                # 记录覆盖情况
                for point in test.coverage_points:
                    if point not in self.coverage_map:
                        self.coverage_map[point] = []
                    self.coverage_map[point].append(test.id)
            else:
                # 合并信息到已存在的测试
                existing = self.test_signatures[sig]
                self._merge_test_info(existing, test)
        
        return unique_tests
    
    def _optimize_by_coverage(self, tests: List[UnifiedTest]) -> List[UnifiedTest]:
        """基于覆盖优化测试集"""
        # 计算每个测试的价值（覆盖的独特点数）
        test_values = {}
        
        for test in tests:
            unique_coverage = 0
            for point in test.coverage_points:
                if len(self.coverage_map.get(point, [])) == 1:
                    unique_coverage += 1
            
            test_values[test.id] = {
                'test': test,
                'unique_coverage': unique_coverage,
                'total_coverage': len(test.coverage_points),
                'priority': test.priority
            }
        
        # 贪心选择测试
        selected_tests = []
        covered_points = set()
        
        # 按价值排序
        sorted_tests = sorted(
            test_values.values(),
            key=lambda x: (x['unique_coverage'], x['priority'], x['total_coverage']),
            reverse=True
        )
        
        for test_info in sorted_tests:
            test = test_info['test']
            new_coverage = set(test.coverage_points) - covered_points
            
            # 如果能增加新的覆盖点，或者是高优先级测试，则保留
            if new_coverage or test.priority >= 8:
                selected_tests.append(test)
                covered_points.update(test.coverage_points)
        
        return selected_tests
    
    def _ensure_critical_tests(self, tests: List[UnifiedTest]) -> List[UnifiedTest]:
        """确保关键测试不被删除"""
        critical_types = {
            TestType.FUNCTIONAL,  # 基本功能测试
            TestType.CONSTRAINT_VIOLATION,  # 约束违反测试
            TestType.STATE_TRANSITION  # 状态转换测试
        }
        
        # 确保每种关键类型至少有一个测试
        type_tests = {}
        for test in tests:
            if test.type not in type_tests:
                type_tests[test.type] = []
            type_tests[test.type].append(test)
        
        # 如果某个关键类型没有测试，从原始集合中找回
        final_tests = tests.copy()
        
        for critical_type in critical_types:
            if critical_type not in type_tests or not type_tests[critical_type]:
                # 从签名集合中找回一个该类型的测试
                for sig, test in self.test_signatures.items():
                    if test.type == critical_type and test not in final_tests:
                        final_tests.append(test)
                        break
        
        return final_tests
    
    def _create_signature(self, test: UnifiedTest) -> str:
        """创建测试签名"""
        # 使用更智能的签名生成
        sig_parts = [
            test.type.value,
            self._normalize_test_data(test.test_data),
            test.expected_result
        ]
        
        # 对于某些类型的测试，包含更多信息
        if test.type in [TestType.RULE_ACTIVATION, TestType.RULE_DEACTIVATION]:
            sig_parts.extend(test.rules_tested)
        
        if test.type == TestType.STATE_TRANSITION:
            sig_parts.extend(test.coverage_points)
        
        # 生成哈希
        sig_str = json.dumps(sig_parts, sort_keys=True)
        return hashlib.md5(sig_str.encode()).hexdigest()
    
    def _normalize_test_data(self, data: Dict[str, Any]) -> str:
        """标准化测试数据用于签名"""
        normalized = {}
        
        for key, value in data.items():
            if isinstance(value, list):
                # 对列表排序
                normalized[key] = sorted(value) if value else []
            elif isinstance(value, dict):
                # 递归标准化
                normalized[key] = self._normalize_test_data(value)
            else:
                normalized[key] = value
        
        return json.dumps(normalized, sort_keys=True)
    
    def _merge_test_info(self, existing: UnifiedTest, new: UnifiedTest):
        """合并测试信息"""
        # 合并覆盖点
        existing.coverage_points = list(set(existing.coverage_points + new.coverage_points))
        
        # 合并约束和规则
        existing.constraints_tested = list(set(existing.constraints_tested + new.constraints_tested))
        existing.rules_tested = list(set(existing.rules_tested + new.rules_tested))
        
        # 合并标签
        existing.tags = list(set(existing.tags + new.tags))
        
        # 更新优先级
        existing.priority = max(existing.priority, new.priority)
        
        # 如果新测试有更好的描述，使用新的
        if len(new.description) > len(existing.description):
            existing.description = new.description
        
        if len(new.rationale) > len(existing.rationale):
            existing.rationale = new.rationale


class UnifiedDSLTestGeneratorV2:
    """统一的 DSL 测试生成器 V2"""
    
    def __init__(self):
        self.z3_engine = EnhancedZ3Engine()
        self.deduplicator = SmartTestDeduplicator()
        self.test_counter = 0
        self.dsl_model = None
        self.entity_map = {}
        self.attribute_map = {}
        
    def generate_tests(self, dsl_file: str, config: Dict[str, Any] = None) -> Dict[str, Any]:
        """生成测试主入口"""
        # 默认配置
        default_config = {
            'max_tests_per_type': 20,
            'enable_combinatorial': True,
            'combinatorial_strength': 2,
            'enable_scenarios': True,
            'optimize_tests': True,
            'value_strategy': 'realistic'  # minimal, maximal, realistic
        }
        
        self.config = {**default_config, **(config or {})}
        
        # 解析 DSL
        with open(dsl_file, 'r', encoding='utf-8') as f:
            self.dsl_model = yaml.safe_load(f)
        
        # 构建内部映射
        self._build_internal_mappings()
        
        # 创建 Z3 变量
        self.z3_engine.create_variables_from_entities(self.dsl_model.get('entities', []))
        
        # 添加约束
        for constraint in self.dsl_model.get('constraints', []):
            self.z3_engine.add_constraint(constraint)
        
        # 添加规则
        for rule in self.dsl_model.get('rules', []):
            self.z3_engine.add_rule(rule)
        
        # 生成测试
        all_tests = self._generate_all_test_types()
        
        # 去重和优化
        if self.config['optimize_tests']:
            optimized_tests = self.deduplicator.deduplicate(all_tests)
        else:
            optimized_tests = all_tests
        
        # 排序
        optimized_tests.sort(key=lambda t: (t.priority, t.type.value), reverse=True)
        
        # 格式化输出
        return self._format_output(optimized_tests)
    
    def _build_internal_mappings(self):
        """构建内部映射"""
        for entity in self.dsl_model.get('entities', []):
            entity_name = entity['name']
            self.entity_map[entity_name.lower()] = entity
            
            for attr in entity.get('attributes', []):
                attr_key = f"{entity_name.lower()}_{attr['name']}"
                self.attribute_map[attr_key] = {
                    'entity': entity,
                    'attribute': attr
                }
    
    def _generate_all_test_types(self) -> List[UnifiedTest]:
        """生成所有类型的测试"""
        all_tests = []
        
        # 1. 功能测试
        all_tests.extend(self._generate_functional_tests())
        
        # 2. 边界测试
        all_tests.extend(self._generate_boundary_tests())
        
        # 3. 规则测试
        all_tests.extend(self._generate_rule_tests())
        
        # 4. 约束测试
        all_tests.extend(self._generate_constraint_tests())
        
        # 5. 负面测试
        all_tests.extend(self._generate_negative_tests())
        
        # 6. 场景测试
        if self.config['enable_scenarios']:
            all_tests.extend(self._generate_scenario_tests())
        
        # 7. 状态机测试
        if 'state_machines' in self.dsl_model:
            all_tests.extend(self._generate_state_machine_tests())
        
        # 8. 组合测试
        if self.config['enable_combinatorial']:
            all_tests.extend(self._generate_combinatorial_tests())
        
        return all_tests
    
    def _generate_functional_tests(self) -> List[UnifiedTest]:
        """生成功能测试"""
        tests = []
        
        for entity_name, entity in self.entity_map.items():
            # 测试1：最小有效数据（只包含必填字段）
            test_data = self._generate_minimal_valid_data(entity)
            if test_data:
                test = UnifiedTest(
                    id=self._next_test_id(),
                    name=f"Create {entity['name']} with minimal data",
                    type=TestType.FUNCTIONAL,
                    description=f"Test creating {entity['name']} with only required fields",
                    rationale="Verify entity can be created with minimal required data",
                    test_data=test_data,
                    expected_result="pass",
                    coverage_points=[f"entity:{entity['name']}:minimal"],
                    priority=9,
                    tags=["smoke", "required_fields"]
                )
                tests.append(test)
            
            # 测试2：完整有效数据（包含所有字段）
            test_data = self._generate_complete_valid_data(entity)
            if test_data and test_data != tests[-1].test_data if tests else True:
                test = UnifiedTest(
                    id=self._next_test_id(),
                    name=f"Create {entity['name']} with complete data",
                    type=TestType.FUNCTIONAL,
                    description=f"Test creating {entity['name']} with all fields populated",
                    rationale="Verify entity handles all fields correctly",
                    test_data=test_data,
                    expected_result="pass",
                    coverage_points=[f"entity:{entity['name']}:complete"],
                    priority=8,
                    tags=["comprehensive"]
                )
                tests.append(test)
            
            # 测试3：使用默认值的数据
            test_data = self._generate_data_with_defaults(entity)
            if test_data:
                test = UnifiedTest(
                    id=self._next_test_id(),
                    name=f"Create {entity['name']} with default values",
                    type=TestType.FUNCTIONAL,
                    description=f"Test creating {entity['name']} relying on default values",
                    rationale="Verify default value handling",
                    test_data=test_data,
                    expected_result="pass",
                    coverage_points=[f"entity:{entity['name']}:defaults"],
                    priority=7,
                    tags=["defaults"]
                )
                tests.append(test)
        
        return tests[:self.config['max_tests_per_type']]
    
    def _generate_boundary_tests(self) -> List[UnifiedTest]:
        """生成边界测试"""
        tests = []
        
        for attr_key, attr_info in self.attribute_map.items():
            entity = attr_info['entity']
            attr = attr_info['attribute']
            attr_meta = self.z3_engine.metadata.get(attr_key)
            
            if not attr_meta:
                continue
            
            # 数值边界测试
            if attr_meta.is_numeric:
                # 最小值测试
                if attr_meta.min is not None:
                    test_data = self._generate_boundary_value_test(
                        entity, attr_key, attr_meta.min, "minimum"
                    )
                    if test_data:
                        test = UnifiedTest(
                            id=self._next_test_id(),
                            name=f"Boundary: {attr_key} at minimum ({attr_meta.min})",
                            type=TestType.BOUNDARY,
                            description=f"Test {attr_key} at its minimum boundary",
                            rationale="Verify system handles minimum values correctly",
                            test_data=test_data,
                            expected_result="pass",
                            coverage_points=[f"boundary:{attr_key}:min"],
                            priority=8,
                            tags=["boundary", "minimum"]
                        )
                        tests.append(test)
                
                # 最大值测试
                if attr_meta.max is not None:
                    test_data = self._generate_boundary_value_test(
                        entity, attr_key, attr_meta.max, "maximum"
                    )
                    if test_data:
                        test = UnifiedTest(
                            id=self._next_test_id(),
                            name=f"Boundary: {attr_key} at maximum ({attr_meta.max})",
                            type=TestType.BOUNDARY,
                            description=f"Test {attr_key} at its maximum boundary",
                            rationale="Verify system handles maximum values correctly",
                            test_data=test_data,
                            expected_result="pass",
                            coverage_points=[f"boundary:{attr_key}:max"],
                            priority=8,
                            tags=["boundary", "maximum"]
                        )
                        tests.append(test)
                
                # 刚好超出边界的测试
                if attr_meta.min is not None:
                    test_data = self._generate_boundary_value_test(
                        entity, attr_key, attr_meta.min - 1, "below_minimum"
                    )
                    if test_data:
                        test = UnifiedTest(
                            id=self._next_test_id(),
                            name=f"Boundary: {attr_key} below minimum ({attr_meta.min - 1})",
                            type=TestType.NEGATIVE,
                            description=f"Test {attr_key} below its minimum boundary",
                            rationale="Verify system rejects out-of-range values",
                            test_data=test_data,
                            expected_result="fail",
                            coverage_points=[f"boundary:{attr_key}:below_min"],
                            priority=7,
                            tags=["boundary", "negative"]
                        )
                        tests.append(test)
            
            # 集合边界测试
            elif attr_meta.is_collection:
                # 空集合
                test_data = self._generate_collection_boundary_test(entity, attr_key, 0)
                if test_data:
                    test = UnifiedTest(
                        id=self._next_test_id(),
                        name=f"Boundary: {attr_key} empty collection",
                        type=TestType.BOUNDARY,
                        description=f"Test {attr_key} with empty collection",
                        rationale="Verify system handles empty collections",
                        test_data=test_data,
                        expected_result="pass",
                        coverage_points=[f"boundary:{attr_key}:empty"],
                        priority=8,
                        tags=["boundary", "empty"]
                    )
                    tests.append(test)
                
                # 单元素集合
                test_data = self._generate_collection_boundary_test(entity, attr_key, 1)
                if test_data:
                    test = UnifiedTest(
                        id=self._next_test_id(),
                        name=f"Boundary: {attr_key} single element",
                        type=TestType.BOUNDARY,
                        description=f"Test {attr_key} with single element",
                        rationale="Verify system handles single-element collections",
                        test_data=test_data,
                        expected_result="pass",
                        coverage_points=[f"boundary:{attr_key}:single"],
                        priority=7,
                        tags=["boundary", "single"]
                    )
                    tests.append(test)
        
        return tests[:self.config['max_tests_per_type']]
    
    def _generate_rule_tests(self) -> List[UnifiedTest]:
        """生成规则测试"""
        tests = []
        
        for i, rule in enumerate(self.dsl_model.get('rules', [])):
            rule_name = rule.get('name', f"Rule_{i+1}")
            
            # 激活规则的测试
            activation_data = self._generate_rule_activation_data(rule)
            if activation_data:
                test = UnifiedTest(
                    id=self._next_test_id(),
                    name=f"Activate rule: {rule_name}",
                    type=TestType.RULE_ACTIVATION,
                    description=f"Test that activates '{rule_name}'",
                    rationale=f"Verify rule '{rule_name}' is enforced when conditions are met",
                    test_data=activation_data,
                    expected_result="pass",
                    coverage_points=[f"rule:{rule_name}:activated"],
                    rules_tested=[rule_name],
                    priority=8,
                    tags=["rule", "activation"]
                )
                tests.append(test)
            
            # 不激活规则的测试
            deactivation_data = self._generate_rule_deactivation_data(rule)
            if deactivation_data:
                test = UnifiedTest(
                    id=self._next_test_id(),
                    name=f"Deactivate rule: {rule_name}",
                    type=TestType.RULE_DEACTIVATION,
                    description=f"Test that does not activate '{rule_name}'",
                    rationale=f"Verify system behavior when rule '{rule_name}' is not applicable",
                    test_data=deactivation_data,
                    expected_result="pass",
                    coverage_points=[f"rule:{rule_name}:deactivated"],
                    rules_tested=[rule_name],
                    priority=7,
                    tags=["rule", "deactivation"]
                )
                tests.append(test)
        
        return tests[:self.config['max_tests_per_type']]
    
    def _generate_constraint_tests(self) -> List[UnifiedTest]:
        """生成约束测试"""
        tests = []
        
        for i, constraint in enumerate(self.dsl_model.get('constraints', [])):
            # 约束满足测试（通常已包含在功能测试中）
            
            # 约束违反测试
            violation_data = self._generate_constraint_violation_data(constraint, i)
            if violation_data:
                test = UnifiedTest(
                    id=self._next_test_id(),
                    name=f"Violate constraint: {constraint[:50]}",
                    type=TestType.CONSTRAINT_VIOLATION,
                    description=f"Test data that violates: {constraint}",
                    rationale="Verify system properly rejects constraint-violating data",
                    test_data=violation_data,
                    expected_result="fail",
                    coverage_points=[f"constraint:violation:{i}"],
                    constraints_tested=[constraint],
                    priority=8,
                    tags=["constraint", "negative"]
                )
                tests.append(test)
        
        return tests[:self.config['max_tests_per_type']]
    
    def _generate_negative_tests(self) -> List[UnifiedTest]:
        """生成负面测试"""
        tests = []
        
        for entity_name, entity in self.entity_map.items():
            # 缺少必填字段
            for attr in entity.get('attributes', []):
                if not attr.get('optional', False):
                    attr_key = f"{entity_name}_{attr['name']}"
                    test_data = self._generate_missing_field_data(entity, attr_key)
                    
                    if test_data:
                        test = UnifiedTest(
                            id=self._next_test_id(),
                            name=f"Missing required field: {attr_key}",
                            type=TestType.NEGATIVE,
                            description=f"Test with missing required field {attr_key}",
                            rationale="Verify system enforces required fields",
                            test_data=test_data,
                            expected_result="fail",
                            coverage_points=[f"negative:{attr_key}:missing"],
                            priority=7,
                            tags=["negative", "missing_field"]
                        )
                        tests.append(test)
            
            # 无效数据类型
            for attr in entity.get('attributes', []):
                attr_key = f"{entity_name}_{attr['name']}"
                test_data = self._generate_invalid_type_data(entity, attr_key)
                
                if test_data:
                    test = UnifiedTest(
                        id=self._next_test_id(),
                        name=f"Invalid type for: {attr_key}",
                        type=TestType.NEGATIVE,
                        description=f"Test with invalid data type for {attr_key}",
                        rationale="Verify system validates data types",
                        test_data=test_data,
                        expected_result="fail",
                        coverage_points=[f"negative:{attr_key}:invalid_type"],
                        priority=6,
                        tags=["negative", "type_validation"]
                    )
                    tests.append(test)
        
        return tests[:self.config['max_tests_per_type']]
    
    def _generate_scenario_tests(self) -> List[UnifiedTest]:
        """生成场景测试"""
        tests = []
        domain = self.dsl_model.get('domain', '').lower()
        
        # 基于领域的场景生成器
        scenario_generators = {
            'shopping': self._generate_shopping_scenarios,
            'cart': self._generate_shopping_scenarios,
            'order': self._generate_order_scenarios,
            'user': self._generate_user_scenarios,
            'account': self._generate_user_scenarios,
            'permission': self._generate_permission_scenarios,
            'student': self._generate_student_scenarios,
            'grade': self._generate_student_scenarios
        }
        
        # 查找匹配的场景生成器
        for keyword, generator in scenario_generators.items():
            if keyword in domain:
                tests.extend(generator())
                break
        
        # 通用场景
        tests.extend(self._generate_generic_scenarios())
        
        return tests[:self.config['max_tests_per_type']]
    
    def _generate_state_machine_tests(self) -> List[UnifiedTest]:
        """生成状态机测试"""
        tests = []
        
        for sm in self.dsl_model.get('state_machines', []):
            sm_name = sm.get('name', 'StateMachine')
            
            # 测试每个有效转换
            for transition in sm.get('transitions', []):
                test_data = self._generate_state_transition_data(sm, transition)
                
                if test_data:
                    test = UnifiedTest(
                        id=self._next_test_id(),
                        name=f"{sm_name}: {transition['name']}",
                        type=TestType.STATE_TRANSITION,
                        description=f"Test transition from {transition['from']} to {transition['to']}",
                        rationale=transition.get('description', 'Verify state transition works correctly'),
                        test_data=test_data,
                        expected_result="pass",
                        coverage_points=[
                            f"state:{sm_name}:{transition['from']}->{transition['to']}",
                            f"transition:{transition['name']}"
                        ],
                        priority=8,
                        tags=["state_machine", "transition"]
                    )
                    tests.append(test)
            
            # 测试禁止的转换
            for forbidden in sm.get('forbidden_transitions', []):
                test_data = self._generate_forbidden_transition_data(sm, forbidden)
                
                if test_data:
                    test = UnifiedTest(
                        id=self._next_test_id(),
                        name=f"{sm_name}: Forbidden {forbidden['from']} to {forbidden['to']}",
                        type=TestType.NEGATIVE,
                        description=f"Test forbidden transition from {forbidden['from']} to {forbidden['to']}",
                        rationale=forbidden.get('description', 'Verify forbidden transitions are blocked'),
                        test_data=test_data,
                        expected_result="fail",
                        coverage_points=[
                            f"state:{sm_name}:forbidden:{forbidden['from']}->{forbidden['to']}"
                        ],
                        priority=7,
                        tags=["state_machine", "forbidden"]
                    )
                    tests.append(test)
        
        return tests[:self.config['max_tests_per_type']]
    
    def _generate_combinatorial_tests(self) -> List[UnifiedTest]:
        """生成组合测试"""
        tests = []
        
        # 获取组合测试配置
        strength = self.config.get('combinatorial_strength', 2)
        
        # 为每个实体生成组合测试
        for entity_name, entity in self.entity_map.items():
            # 选择要组合的属性
            combinable_attrs = self._select_combinable_attributes(entity)
            
            if len(combinable_attrs) >= strength:
                # 生成组合
                combinations = self._generate_combinations(combinable_attrs, strength)
                
                for combo in combinations[:5]:  # 限制数量
                    test_data = self._generate_combination_test_data(entity, combo)
                    
                    if test_data:
                        combo_desc = ", ".join([f"{attr['name']}={value}" 
                                              for attr, value in combo])
                        
                        test = UnifiedTest(
                            id=self._next_test_id(),
                            name=f"Combination: {combo_desc[:50]}",
                            type=TestType.COMBINATORIAL,
                            description=f"Test combination of {len(combo)} attributes",
                            rationale=f"Verify system handles {strength}-way interactions correctly",
                            test_data=test_data,
                            expected_result="pass",
                            coverage_points=[f"combo:{strength}way:{entity_name}"],
                            priority=6,
                            tags=["combinatorial", f"{strength}way"]
                        )
                        tests.append(test)
        
        return tests[:self.config['max_tests_per_type']]
    
    # 辅助方法
    def _next_test_id(self) -> str:
        """生成下一个测试ID"""
        self.test_counter += 1
        return f"TEST_{self.test_counter:04d}"
    
    def _generate_minimal_valid_data(self, entity: Dict[str, Any]) -> Dict[str, Any]:
        """生成最小有效数据"""
        # 使用 Z3 求解器生成满足约束的最小数据
        self.z3_engine.solver.push()
        
        # 只包含必填字段
        entity_name = entity['name'].lower()
        for attr in entity.get('attributes', []):
            if attr.get('optional', False):
                attr_key = f"{entity_name}_{attr['name']}"
                if attr_key in self.z3_engine.optional_vars:
                    # 设置可选字段不存在
                    self.z3_engine.solver.add(
                        z3.Not(self.z3_engine.optional_vars[attr_key])
                    )
        
        # 使用最小化策略求解
        values = self.z3_engine.solve_with_strategy('realistic')
        self.z3_engine.solver.pop()
        
        if values:
            return self._post_process_values(values)
        
        # 回退方案
        return self._generate_fallback_minimal_data(entity)
    
    def _generate_complete_valid_data(self, entity: Dict[str, Any]) -> Dict[str, Any]:
        """生成完整有效数据"""
        self.z3_engine.solver.push()
        
        # 包含所有字段（包括可选字段）
        entity_name = entity['name'].lower()
        for attr in entity.get('attributes', []):
            if attr.get('optional', False):
                attr_key = f"{entity_name}_{attr['name']}"
                if attr_key in self.z3_engine.optional_vars:
                    # 设置可选字段存在
                    self.z3_engine.solver.add(
                        self.z3_engine.optional_vars[attr_key]
                    )
        
        values = self.z3_engine.solve_with_strategy('realistic')
        self.z3_engine.solver.pop()
        
        if values:
            return self._post_process_values(values)
        
        return self._generate_fallback_complete_data(entity)
    
    def _generate_data_with_defaults(self, entity: Dict[str, Any]) -> Dict[str, Any]:
        """生成使用默认值的数据"""
        data = {}
        entity_name = entity['name'].lower()
        
        for attr in entity.get('attributes', []):
            attr_key = f"{entity_name}_{attr['name']}"
            
            # 必填字段使用正常值
            if not attr.get('optional', False):
                if attr_key in self.z3_engine.metadata:
                    meta = self.z3_engine.metadata[attr_key]
                    data[attr_key] = self._get_realistic_value(attr_key, meta)
            # 有默认值的可选字段不包含（使用默认值）
            elif 'default' not in attr:
                # 没有默认值的可选字段包含一个值
                if attr_key in self.z3_engine.metadata:
                    meta = self.z3_engine.metadata[attr_key]
                    data[attr_key] = self._get_realistic_value(attr_key, meta)
        
        return data
    
    def _get_realistic_value(self, attr_key: str, meta: AttributeMetadata) -> Any:
        """获取现实的属性值"""
        # 基于属性名和类型生成合理的值
        attr_name = attr_key.lower()
        
        # 金额相关
        if any(keyword in attr_name for keyword in ['amount', 'price', 'cost', 'balance', 'total']):
            if meta.type == 'integer':
                return 100
            elif meta.type == 'real':
                return 99.99
        
        # 数量相关
        elif any(keyword in attr_name for keyword in ['count', 'quantity', 'number']):
            return 5
        
        # ID 相关
        elif any(keyword in attr_name for keyword in ['_id', 'identifier']):
            return 1001
        
        # 状态相关
        elif 'status' in attr_name:
            if meta.min is not None:
                return meta.min  # 通常是初始状态
            return 1
        
        # 布尔值
        elif meta.type == 'boolean':
            # 根据属性名智能选择
            if any(keyword in attr_name for keyword in ['is_active', 'enabled', 'is_verified']):
                return True
            return False
        
        # 字符串枚举
        elif meta.type == 'string' and meta.enum:
            return meta.enum[0]
        
        # 字符串
        elif meta.type == 'string':
            if 'name' in attr_name:
                return "Test User"
            elif 'email' in attr_name:
                return "test@example.com"
            elif 'phone' in attr_name:
                return "+1234567890"
            return f"test_{attr_name}"
        
        # 时间戳
        elif any(keyword in attr_name for keyword in ['_at', 'timestamp', 'date', 'time']):
            return 1640000000  # 2021-12-20
        
        # 数组/集合
        elif meta.is_collection:
            if 'roles' in attr_name:
                return ["user"]
            elif 'permissions' in attr_name:
                return ["read"]
            return []
        
        # 默认值
        if meta.type == 'integer':
            return meta.min if meta.min is not None else 1
        elif meta.type == 'real':
            return float(meta.min) if meta.min is not None else 1.0
        
        return None
    
    def _post_process_values(self, values: Dict[str, Any]) -> Dict[str, Any]:
        """后处理 Z3 生成的值"""
        processed = {}
        
        for key, value in values.items():
            if key.endswith('_size') or key.endswith('_exists'):
                continue  # 跳过辅助变量
            
            if key in self.z3_engine.metadata:
                meta = self.z3_engine.metadata[key]
                
                # 处理字符串枚举
                if meta.type == 'string' and meta.enum and isinstance(value, int):
                    if 0 <= value < len(meta.enum):
                        processed[key] = meta.enum[value]
                    else:
                        processed[key] = meta.enum[0]
                else:
                    processed[key] = value
            else:
                processed[key] = value
        
        return processed
    
    def _generate_fallback_minimal_data(self, entity: Dict[str, Any]) -> Dict[str, Any]:
        """生成回退的最小数据"""
        data = {}
        entity_name = entity['name'].lower()
        
        for attr in entity.get('attributes', []):
            if not attr.get('optional', False):
                attr_key = f"{entity_name}_{attr['name']}"
                meta = self.z3_engine.metadata.get(attr_key)
                if meta:
                    data[attr_key] = self._get_realistic_value(attr_key, meta)
        
        return data
    
    def _generate_fallback_complete_data(self, entity: Dict[str, Any]) -> Dict[str, Any]:
        """生成回退的完整数据"""
        data = {}
        entity_name = entity['name'].lower()
        
        for attr in entity.get('attributes', []):
            attr_key = f"{entity_name}_{attr['name']}"
            meta = self.z3_engine.metadata.get(attr_key)
            if meta:
                data[attr_key] = self._get_realistic_value(attr_key, meta)
        
        return data
    
    def _generate_boundary_value_test(self, entity: Dict[str, Any], attr_key: str, 
                                    value: Union[int, float], boundary_type: str) -> Dict[str, Any]:
        """生成边界值测试数据"""
        self.z3_engine.solver.push()
        
        # 设置特定属性为边界值
        if attr_key in self.z3_engine.variables:
            var = self.z3_engine.variables[attr_key]
            self.z3_engine.solver.add(var == value)
        
        # 求解
        values = self.z3_engine.solve_with_strategy('realistic')
        self.z3_engine.solver.pop()
        
        if values:
            return self._post_process_values(values)
        
        # 回退：手动构造
        data = self._generate_fallback_minimal_data(entity)
        if attr_key in data:
            data[attr_key] = value
        
        return data
    
    def _generate_collection_boundary_test(self, entity: Dict[str, Any], 
                                         attr_key: str, size: int) -> Dict[str, Any]:
        """生成集合边界测试"""
        self.z3_engine.solver.push()
        
        # 设置集合大小
        if attr_key in self.z3_engine.array_vars:
            size_var = self.z3_engine.array_vars[attr_key]['size']
            self.z3_engine.solver.add(size_var == size)
        elif attr_key in self.z3_engine.set_vars:
            size_var = self.z3_engine.set_vars[attr_key]['size']
            self.z3_engine.solver.add(size_var == size)
        
        values = self.z3_engine.solve_with_strategy('realistic')
        self.z3_engine.solver.pop()
        
        if values:
            return self._post_process_values(values)
        
        # 回退
        data = self._generate_fallback_minimal_data(entity)
        if attr_key in data:
            if size == 0:
                data[attr_key] = []
            elif size == 1:
                meta = self.z3_engine.metadata.get(attr_key)
                if meta and meta.element_type == 'integer':
                    data[attr_key] = [1]
                else:
                    data[attr_key] = ["element1"]
        
        return data
    
    def _generate_rule_activation_data(self, rule: Dict[str, Any]) -> Dict[str, Any]:
        """生成激活规则的数据"""
        self.z3_engine.solver.push()
        
        # 添加规则条件为真
        condition_expr = rule.get('condition') or rule.get('if')
        if condition_expr:
            condition = self.z3_engine._parse_constraint(condition_expr)
            if condition is not None:
                self.z3_engine.solver.add(condition)
        
        # 如果有 implies，也要满足
        implies_expr = rule.get('implies') or rule.get('then')
        if implies_expr:
            implies = self.z3_engine._parse_constraint(implies_expr)
            if implies is not None:
                self.z3_engine.solver.add(implies)
        
        values = self.z3_engine.solve_with_strategy('realistic')
        self.z3_engine.solver.pop()
        
        if values:
            return self._post_process_values(values)
        
        return None
    
    def _generate_rule_deactivation_data(self, rule: Dict[str, Any]) -> Dict[str, Any]:
        """生成不激活规则的数据"""
        self.z3_engine.solver.push()
        
        # 添加规则条件为假
        condition_expr = rule.get('condition') or rule.get('if')
        if condition_expr:
            condition = self.z3_engine._parse_constraint(condition_expr)
            if condition is not None:
                self.z3_engine.solver.add(z3.Not(condition))
        
        values = self.z3_engine.solve_with_strategy('realistic')
        self.z3_engine.solver.pop()
        
        if values:
            return self._post_process_values(values)
        
        return None
    
    def _generate_constraint_violation_data(self, constraint: str, index: int) -> Dict[str, Any]:
        """生成违反约束的数据"""
        # 创建新的求解器，不包含这个约束
        temp_engine = EnhancedZ3Engine()
        temp_engine.variables = self.z3_engine.variables.copy()
        temp_engine.array_vars = self.z3_engine.array_vars.copy()
        temp_engine.set_vars = self.z3_engine.set_vars.copy()
        temp_engine.metadata = self.z3_engine.metadata.copy()
        
        # 添加其他约束
        for i, other_constraint in enumerate(self.dsl_model.get('constraints', [])):
            if i != index:
                temp_engine.add_constraint(other_constraint)
        
        # 添加约束的否定
        negated = temp_engine._parse_constraint(constraint)
        if negated is not None:
            temp_engine.solver.add(z3.Not(negated))
        
        # 求解
        values = temp_engine.solve_with_strategy('realistic')
        
        if values:
            return self._post_process_values(values)
        
        return None
    
    def _generate_missing_field_data(self, entity: Dict[str, Any], missing_field: str) -> Dict[str, Any]:
        """生成缺少字段的数据"""
        data = self._generate_fallback_minimal_data(entity)
        
        # 删除指定字段
        if missing_field in data:
            del data[missing_field]
        
        return data
    
    def _generate_invalid_type_data(self, entity: Dict[str, Any], field: str) -> Dict[str, Any]:
        """生成无效类型的数据"""
        data = self._generate_fallback_minimal_data(entity)
        
        if field in data and field in self.z3_engine.metadata:
            meta = self.z3_engine.metadata[field]
            
            # 生成错误类型的值
            if meta.type == 'integer':
                data[field] = "not_a_number"
            elif meta.type == 'real':
                data[field] = "not_a_float"
            elif meta.type == 'boolean':
                data[field] = "not_a_bool"
            elif meta.type == 'string':
                data[field] = 12345  # 数字而不是字符串
            elif meta.is_collection:
                data[field] = "not_a_list"
        
        return data
    
    def _generate_shopping_scenarios(self) -> List[UnifiedTest]:
        """生成购物相关场景"""
        tests = []
        
        # 场景1：空购物车结算
        empty_cart_data = self._create_scenario_data('empty_cart')
        if empty_cart_data:
            test = UnifiedTest(
                id=self._next_test_id(),
                name="Scenario: Empty cart checkout",
                type=TestType.SCENARIO,
                description="Attempt to checkout with empty shopping cart",
                rationale="Verify system handles empty cart scenario appropriately",
                test_data=empty_cart_data,
                expected_result="fail",
                coverage_points=["scenario:empty_cart_checkout"],
                priority=7,
                tags=["scenario", "shopping", "edge_case"]
            )
            tests.append(test)
        
        # 场景2：大额订单
        large_order_data = self._create_scenario_data('large_order')
        if large_order_data:
            test = UnifiedTest(
                id=self._next_test_id(),
                name="Scenario: Large order processing",
                type=TestType.SCENARIO,
                description="Process order with many items and high value",
                rationale="Verify system handles large orders correctly",
                test_data=large_order_data,
                expected_result="pass",
                coverage_points=["scenario:large_order"],
                priority=6,
                tags=["scenario", "shopping", "stress"]
            )
            tests.append(test)
        
        return tests
    
    def _generate_order_scenarios(self) -> List[UnifiedTest]:
        """生成订单相关场景"""
        tests = []
        
        # 场景：订单生命周期
        new_order_data = self._create_scenario_data('new_order')
        if new_order_data:
            test = UnifiedTest(
                id=self._next_test_id(),
                name="Scenario: New order creation",
                type=TestType.SCENARIO,
                description="Create a new order in pending payment state",
                rationale="Verify order creation and initial state",
                test_data=new_order_data,
                expected_result="pass",
                coverage_points=["scenario:order_creation"],
                priority=7,
                tags=["scenario", "order", "lifecycle"]
            )
            tests.append(test)
        
        return tests
    
    def _generate_user_scenarios(self) -> List[UnifiedTest]:
        """生成用户相关场景"""
        tests = []
        
        # 场景：新用户注册
        new_user_data = self._create_scenario_data('new_user')
        if new_user_data:
            test = UnifiedTest(
                id=self._next_test_id(),
                name="Scenario: New user registration",
                type=TestType.SCENARIO,
                description="Register a new user account",
                rationale="Verify user registration process",
                test_data=new_user_data,
                expected_result="pass",
                coverage_points=["scenario:user_registration"],
                priority=7,
                tags=["scenario", "user", "registration"]
            )
            tests.append(test)
        
        # 场景：账户锁定
        locked_account_data = self._create_scenario_data('locked_account')
        if locked_account_data:
            test = UnifiedTest(
                id=self._next_test_id(),
                name="Scenario: Account lockout after failed logins",
                type=TestType.SCENARIO,
                description="Test account lockout mechanism",
                rationale="Verify security feature works correctly",
                test_data=locked_account_data,
                expected_result="pass",
                coverage_points=["scenario:account_lockout"],
                priority=8,
                tags=["scenario", "user", "security"]
            )
            tests.append(test)
        
        return tests
    
    def _generate_permission_scenarios(self) -> List[UnifiedTest]:
        """生成权限相关场景"""
        tests = []
        
        # 场景：管理员权限
        admin_data = self._create_scenario_data('admin_user')
        if admin_data:
            test = UnifiedTest(
                id=self._next_test_id(),
                name="Scenario: Admin user full access",
                type=TestType.SCENARIO,
                description="Test admin user with all permissions",
                rationale="Verify admin users have appropriate access",
                test_data=admin_data,
                expected_result="pass",
                coverage_points=["scenario:admin_access"],
                priority=8,
                tags=["scenario", "permission", "admin"]
            )
            tests.append(test)
        
        return tests
    
    def _generate_student_scenarios(self) -> List[UnifiedTest]:
        """生成学生相关场景"""
        tests = []
        
        # 场景：优秀学生
        honor_student_data = self._create_scenario_data('honor_student')
        if honor_student_data:
            test = UnifiedTest(
                id=self._next_test_id(),
                name="Scenario: Honor student with high grades",
                type=TestType.SCENARIO,
                description="Test honor student with excellent performance",
                rationale="Verify system handles top performers correctly",
                test_data=honor_student_data,
                expected_result="pass",
                coverage_points=["scenario:honor_student"],
                priority=6,
                tags=["scenario", "student", "academic"]
            )
            tests.append(test)
        
        return tests
    
    def _generate_generic_scenarios(self) -> List[UnifiedTest]:
        """生成通用场景"""
        tests = []
        
        # 场景：系统初始化
        init_data = self._create_scenario_data('system_init')
        if init_data:
            test = UnifiedTest(
                id=self._next_test_id(),
                name="Scenario: System initialization",
                type=TestType.SCENARIO,
                description="Test system with initial/default data",
                rationale="Verify system initialization state",
                test_data=init_data,
                expected_result="pass",
                coverage_points=["scenario:initialization"],
                priority=5,
                tags=["scenario", "generic", "init"]
            )
            tests.append(test)
        
        return tests
    
    def _create_scenario_data(self, scenario_type: str) -> Dict[str, Any]:
        """创建特定场景的数据"""
        # 基于场景类型和领域生成合适的数据
        # 这里简化实现，实际应该根据DSL模型智能生成
        
        if scenario_type == 'empty_cart':
            # 查找购物车相关实体
            for entity_name, entity in self.entity_map.items():
                if 'cart' in entity_name:
                    data = self._generate_fallback_minimal_data(entity)
                    # 设置购物车为空
                    for key in data:
                        if 'items' in key and isinstance(data[key], list):
                            data[key] = []
                        elif 'total' in key or 'amount' in key:
                            data[key] = 0.0
                    return data
        
        elif scenario_type == 'new_order':
            for entity_name, entity in self.entity_map.items():
                if 'order' in entity_name:
                    data = self._generate_fallback_minimal_data(entity)
                    # 设置订单状态为初始状态
                    for key in data:
                        if 'status' in key:
                            meta = self.z3_engine.metadata.get(key)
                            if meta and meta.min is not None:
                                data[key] = meta.min
                    return data
        
        elif scenario_type == 'admin_user':
            for entity_name, entity in self.entity_map.items():
                if 'user' in entity_name:
                    data = self._generate_fallback_complete_data(entity)
                    # 设置管理员角色
                    for key in data:
                        if 'role' in key:
                            if isinstance(data[key], list):
                                data[key] = ["admin"]
                            else:
                                data[key] = "admin"
                        elif 'permission' in key and isinstance(data[key], list):
                            data[key] = ["all", "admin", "write", "read", "delete"]
                    return data
        
        # 默认返回最小数据
        if self.entity_map:
            first_entity = list(self.entity_map.values())[0]
            return self._generate_fallback_minimal_data(first_entity)
        
        return {}
    
    def _generate_state_transition_data(self, state_machine: Dict[str, Any], 
                                      transition: Dict[str, Any]) -> Dict[str, Any]:
        """生成状态转换测试数据"""
        # 找到对应的实体
        entity_name = state_machine.get('entity', '').lower()
        if entity_name not in self.entity_map:
            return None
        
        entity = self.entity_map[entity_name]
        
        # 生成基础数据
        self.z3_engine.solver.push()
        
        # 设置初始状态
        state_attr = state_machine.get('state_attribute', 'status')
        state_var_name = f"{entity_name}_{state_attr}"
        if state_var_name in self.z3_engine.variables:
            var = self.z3_engine.variables[state_var_name]
            # 假设状态是从1开始的整数
            from_state = self._state_name_to_value(transition['from'], state_machine)
            self.z3_engine.solver.add(var == from_state)
        
        # 添加转换条件
        if 'condition' in transition and transition['condition'] != 'true':
            condition = self.z3_engine._parse_constraint(transition['condition'])
            if condition is not None:
                self.z3_engine.solver.add(condition)
        
        values = self.z3_engine.solve_with_strategy('realistic')
        self.z3_engine.solver.pop()
        
        if values:
            return self._post_process_values(values)
        
        # 回退
        data = self._generate_fallback_minimal_data(entity)
        if state_var_name in data:
            data[state_var_name] = from_state
        
        return data
    
    def _generate_forbidden_transition_data(self, state_machine: Dict[str, Any], 
                                          forbidden: Dict[str, Any]) -> Dict[str, Any]:
        """生成禁止转换的测试数据"""
        # 类似于状态转换，但设置为禁止的起始状态
        entity_name = state_machine.get('entity', '').lower()
        if entity_name not in self.entity_map:
            return None
        
        entity = self.entity_map[entity_name]
        data = self._generate_fallback_minimal_data(entity)
        
        # 设置为禁止转换的起始状态
        state_attr = state_machine.get('state_attribute', 'status')
        state_var_name = f"{entity_name}_{state_attr}"
        if state_var_name in data:
            from_state = self._state_name_to_value(forbidden['from'], state_machine)
            data[state_var_name] = from_state
        
        return data
    
    def _state_name_to_value(self, state_name: str, state_machine: Dict[str, Any]) -> int:
        """将状态名转换为数值"""
        states = state_machine.get('states', [])
        for i, state in enumerate(states, 1):
            if state.get('name') == state_name:
                return i
        return 1  # 默认返回1
    
    def _select_combinable_attributes(self, entity: Dict[str, Any]) -> List[Tuple[Dict, List]]:
        """选择可组合的属性"""
        combinable = []
        entity_name = entity['name'].lower()
        
        for attr in entity.get('attributes', []):
            attr_key = f"{entity_name}_{attr['name']}"
            meta = self.z3_engine.metadata.get(attr_key)
            
            if meta and not attr.get('optional', False):
                # 获取属性的可能值
                if meta.enum:
                    values = meta.enum
                elif meta.type == 'boolean':
                    values = [True, False]
                elif meta.is_numeric and meta.min is not None and meta.max is not None:
                    # 选择几个代表值
                    if meta.type == 'integer':
                        values = [meta.min, (meta.min + meta.max) // 2, meta.max]
                    else:
                        values = [meta.min, (meta.min + meta.max) / 2, meta.max]
                else:
                    continue  # 跳过难以组合的属性
                
                combinable.append((attr, values))
        
        return combinable
    
    def _generate_combinations(self, attributes: List[Tuple[Dict, List]], 
                             strength: int) -> List[List[Tuple[Dict, Any]]]:
        """生成属性组合"""
        # 简化实现：生成所有可能的 n-way 组合
        import itertools
        
        # 选择要组合的属性
        if len(attributes) > strength:
            # 选择最重要的属性
            selected_attrs = attributes[:strength]
        else:
            selected_attrs = attributes
        
        # 生成值的组合
        combinations = []
        value_lists = [values for _, values in selected_attrs]
        attr_list = [attr for attr, _ in selected_attrs]
        
        for value_combo in itertools.product(*value_lists):
            combo = list(zip(attr_list, value_combo))
            combinations.append(combo)
        
        return combinations
    
    def _generate_combination_test_data(self, entity: Dict[str, Any], 
                                      combination: List[Tuple[Dict, Any]]) -> Dict[str, Any]:
        """生成组合测试数据"""
        # 基础数据
        data = self._generate_fallback_minimal_data(entity)
        entity_name = entity['name'].lower()
        
        # 应用组合值
        for attr, value in combination:
            attr_key = f"{entity_name}_{attr['name']}"
            data[attr_key] = value
        
        # 使用 Z3 确保数据满足约束
        self.z3_engine.solver.push()
        
        # 固定组合的值
        for attr, value in combination:
            attr_key = f"{entity_name}_{attr['name']}"
            if attr_key in self.z3_engine.variables:
                var = self.z3_engine.variables[attr_key]
                self.z3_engine.solver.add(var == value)
        
        values = self.z3_engine.solve_with_strategy('realistic')
        self.z3_engine.solver.pop()
        
        if values:
            # 合并固定值和求解值
            result = self._post_process_values(values)
            for attr, value in combination:
                attr_key = f"{entity_name}_{attr['name']}"
                result[attr_key] = value
            return result
        
        return data
    
    def _format_output(self, tests: List[UnifiedTest]) -> Dict[str, Any]:
        """格式化输出"""
        # 统计信息
        type_distribution = {}
        tag_distribution = {}
        
        for test in tests:
            # 类型统计
            type_name = test.type.value
            type_distribution[type_name] = type_distribution.get(type_name, 0) + 1
            
            # 标签统计
            for tag in test.tags:
                tag_distribution[tag] = tag_distribution.get(tag, 0) + 1
        
        # 按类型分组
        test_suites = {}
        for test in tests:
            type_name = test.type.value
            if type_name not in test_suites:
                test_suites[type_name] = []
            test_suites[type_name].append(test.to_dict())
        
        # 生成可执行代码
        executable_code = self._generate_executable_code(tests)
        
        return {
            "meta": {
                "generator": "Unified DSL Test Generator v2.0",
                "domain": self.dsl_model.get('domain', 'Unknown'),
                "timestamp": datetime.now().isoformat(),
                "dsl_file": Path(self.dsl_model.get('domain', 'Unknown')).stem + '.yaml',
                "config": self.config
            },
            "summary": {
                "total_tests": len(tests),
                "coverage_rate": self._calculate_coverage_rate(tests),
                "test_distribution": type_distribution,
                "tag_distribution": tag_distribution,
                "priority_distribution": {
                    "high": len([t for t in tests if t.priority >= 8]),
                    "medium": len([t for t in tests if 5 <= t.priority < 8]),
                    "low": len([t for t in tests if t.priority < 5])
                }
            },
            "test_suites": test_suites,
            "executable_tests": executable_code
        }
    
    def _calculate_coverage_rate(self, tests: List[UnifiedTest]) -> str:
        """计算覆盖率"""
        # 统计覆盖的元素
        covered_entities = set()
        covered_rules = set()
        covered_constraints = set()
        covered_states = set()
        
        for test in tests:
            for point in test.coverage_points:
                if point.startswith('entity:'):
                    covered_entities.add(point.split(':')[1])
                elif point.startswith('rule:'):
                    covered_rules.add(point.split(':')[1])
                elif point.startswith('constraint:'):
                    covered_constraints.add(point)
                elif point.startswith('state:'):
                    covered_states.add(point)
        
        # 计算覆盖率
        total_entities = len(self.dsl_model.get('entities', []))
        total_rules = len(self.dsl_model.get('rules', []))
        total_constraints = len(self.dsl_model.get('constraints', []))
        
        entity_coverage = len(covered_entities) / total_entities if total_entities > 0 else 1.0
        rule_coverage = len(covered_rules) / total_rules if total_rules > 0 else 1.0
        constraint_coverage = len(covered_constraints) / total_constraints if total_constraints > 0 else 1.0
        
        # 加权平均
        overall_coverage = (entity_coverage * 0.4 + rule_coverage * 0.3 + constraint_coverage * 0.3)
        
        return f"{overall_coverage * 100:.1f}%"
    
    def _generate_executable_code(self, tests: List[UnifiedTest]) -> str:
        """生成可执行的测试代码"""
        domain_name = self.dsl_model.get('domain', 'System').replace(' ', '')
        domain_name = ''.join(c for c in domain_name if c.isalnum())
        
        code = f'''#!/usr/bin/env python3
"""
自动生成的测试代码
领域: {self.dsl_model.get('domain', 'Unknown')}
生成时间: {datetime.now().isoformat()}
测试框架: pytest
"""

import pytest
import json
from typing import Dict, Any, List
from dataclasses import dataclass


@dataclass
class APIResponse:
    """API 响应对象"""
    status: str
    message: str
    data: Dict[str, Any] = None
    errors: List[str] = None


class {domain_name}API:
    """
    {self.dsl_model.get('domain', 'System')} API 客户端
    
    这是一个模拟的 API 客户端，实际使用时应该替换为真实的 API 调用
    """
    
    @staticmethod
    def create(data: Dict[str, Any]) -> APIResponse:
        """创建实体"""
        # TODO: 实现实际的 API 调用
        # 这里是模拟实现
        
        # 基本验证
        if not data:
            return APIResponse("fail", "Empty data", errors=["No data provided"])
        
        # 模拟验证逻辑
        errors = {domain_name}API._validate(data)
        if errors:
            return APIResponse("fail", "Validation failed", errors=errors)
        
        return APIResponse("pass", "Created successfully", data=data)
    
    @staticmethod
    def update(id: Any, data: Dict[str, Any]) -> APIResponse:
        """更新实体"""
        # TODO: 实现实际的 API 调用
        errors = {domain_name}API._validate(data)
        if errors:
            return APIResponse("fail", "Validation failed", errors=errors)
        
        return APIResponse("pass", "Updated successfully", data=data)
    
    @staticmethod
    def validate(data: Dict[str, Any]) -> APIResponse:
        """验证数据"""
        errors = {domain_name}API._validate(data)
        if errors:
            return APIResponse("fail", "Validation failed", errors=errors)
        
        return APIResponse("pass", "Valid data")
    
    @staticmethod
    def _validate(data: Dict[str, Any]) -> List[str]:
        """内部验证方法"""
        errors = []
        
        # TODO: 实现基于 DSL 的验证逻辑
        # 示例验证
        for key, value in data.items():
            if value is None and not key.endswith('_optional'):
                errors.append(f"{{key}} is required")
            
            # 类型验证
            if '_id' in key and not isinstance(value, (int, str)):
                errors.append(f"{{key}} must be an integer or string")
            
            if '_price' in key or '_amount' in key:
                if not isinstance(value, (int, float)) or value < 0:
                    errors.append(f"{{key}} must be a positive number")
        
        return errors


# 测试基类
class Test{domain_name}Base:
    """测试基类，提供共享的设置和工具方法"""
    
    @pytest.fixture(autouse=True)
    def setup(self):
        """测试前的设置"""
        # TODO: 添加测试设置代码
        pass
    
    def assert_success(self, response: APIResponse, message: str = None):
        """断言响应成功"""
        assert response.status == "pass", f"Expected success but got: {{response.message}}"
        if message:
            assert message in response.message
    
    def assert_failure(self, response: APIResponse, message: str = None):
        """断言响应失败"""
        assert response.status == "fail", f"Expected failure but got: {{response.message}}"
        if message:
            assert message in response.message or any(message in e for e in (response.errors or []))


'''
        
        # 为每个测试类型创建测试类
        test_classes = {}
        
        for test in tests[:50]:  # 限制生成的测试数量
            test_type = test.type.value.title().replace('_', '')
            class_name = f"Test{test_type}"
            
            if class_name not in test_classes:
                test_classes[class_name] = []
            
            test_classes[class_name].append(test)
        
        # 生成测试类
        for class_name, class_tests in test_classes.items():
            code += f'''

class {class_name}(Test{domain_name}Base):
    """{class_tests[0].type.value.replace('_', ' ').title()} 测试"""
'''
            
            # 生成测试方法
            for test in class_tests[:10]:  # 每个类最多10个测试
                method_name = self._generate_test_method_name(test)
                
                code += f'''
    def test_{method_name}(self):
        """
        {test.description}
        
        理由: {test.rationale}
        类型: {test.type.value}
        优先级: {test.priority}
        预期结果: {test.expected_result}
        标签: {', '.join(test.tags)}
        """
        # 测试数据
        test_data = {json.dumps(test.test_data, indent=12, ensure_ascii=False)}
        
        # 执行测试
        response = {domain_name}API.create(test_data)
        
        # 验证结果
'''
                
                if test.expected_result == "pass":
                    code += '''        self.assert_success(response)
'''
                else:
                    code += '''        self.assert_failure(response)
'''
                
                # 添加覆盖点注释
                if test.coverage_points:
                    code += f'''        
        # 覆盖点: {', '.join(test.coverage_points)}
'''
                
                # 添加测试的约束和规则
                if test.constraints_tested:
                    code += f'''        # 测试约束: {', '.join(test.constraints_tested)}
'''
                
                if test.rules_tested:
                    code += f'''        # 测试规则: {', '.join(test.rules_tested)}
'''
        
        # 添加测试运行入口
        code += '''


if __name__ == "__main__":
    # 运行测试
    pytest.main([__file__, "-v", "--tb=short"])
'''
        
        return code
    
    def _generate_test_method_name(self, test: UnifiedTest) -> str:
        """生成测试方法名"""
        # 清理测试名称，使其成为有效的 Python 方法名
        name = test.name.lower()
        name = re.sub(r'[^a-z0-9_]', '_', name)
        name = re.sub(r'_+', '_', name)
        name = name.strip('_')
        
        # 确保不超过合理长度
        if len(name) > 50:
            name = name[:47] + f"_{test.id[-3:]}"
        
        # 确保唯一性
        name = f"{name}_{test.id[-4:]}"
        
        return name


def main():
    """主函数"""
    parser = argparse.ArgumentParser(
        description="统一的 DSL 测试生成器 V2 - 支持高级特性和更好的 Z3 集成",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  %(prog)s examples/shopping_cart.yaml
  %(prog)s examples/order_system.yaml -o tests.json --config config.yaml
  %(prog)s examples/user_system.yaml --format python --max-tests 50
        """
    )
    
    parser.add_argument("dsl_file", help="DSL 文件路径 (YAML 格式)")
    parser.add_argument("-o", "--output", help="输出文件路径")
    parser.add_argument("--format", choices=["json", "python", "both"], 
                       default="both", help="输出格式 (默认: both)")
    parser.add_argument("--config", help="配置文件路径 (YAML 格式)")
    parser.add_argument("--max-tests", type=int, default=20,
                       help="每种类型的最大测试数 (默认: 20)")
    parser.add_argument("--no-optimize", action="store_true",
                       help="禁用测试优化和去重")
    parser.add_argument("--strategy", choices=["minimal", "maximal", "realistic"],
                       default="realistic", help="值生成策略 (默认: realistic)")
    parser.add_argument("-v", "--verbose", action="store_true", help="详细输出")
    
    args = parser.parse_args()
    
    # 加载配置
    config = {}
    if args.config:
        with open(args.config, 'r', encoding='utf-8') as f:
            config = yaml.safe_load(f)
    
    # 应用命令行参数
    config['max_tests_per_type'] = args.max_tests
    config['optimize_tests'] = not args.no_optimize
    config['value_strategy'] = args.strategy
    
    # 创建生成器
    generator = UnifiedDSLTestGeneratorV2()
    
    if args.verbose:
        print(f"正在处理 DSL 文件: {args.dsl_file}")
        print(f"配置: {json.dumps(config, indent=2)}")
    
    # 生成测试
    try:
        result = generator.generate_tests(args.dsl_file, config)
        
        # 输出结果
        if args.format in ["json", "both"]:
            json_output = json.dumps(result, ensure_ascii=False, indent=2)
            
            if args.output:
                json_file = args.output if args.output.endswith('.json') else f"{args.output}.json"
                with open(json_file, 'w', encoding='utf-8') as f:
                    f.write(json_output)
                print(f"✓ JSON 测试用例已保存到: {json_file}")
            else:
                print(json_output)
        
        if args.format in ["python", "both"]:
            python_code = result.get("executable_tests", "")
            
            if args.output:
                py_file = args.output if args.output.endswith('.py') else f"{args.output}_test.py"
                with open(py_file, 'w', encoding='utf-8') as f:
                    f.write(python_code)
                print(f"✓ Python 测试代码已保存到: {py_file}")
            elif args.format == "python":
                print(python_code)
        
        # 打印摘要
        if args.verbose or (args.output and args.format == "both"):
            print("\n" + "="*60)
            print("测试生成完成!")
            print(f"总测试数: {result['summary']['total_tests']}")
            print(f"覆盖率: {result['summary']['coverage_rate']}")
            print(f"\n测试类型分布:")
            for test_type, count in result['summary']['test_distribution'].items():
                print(f"  - {test_type}: {count}")
            
            if result['summary'].get('tag_distribution'):
                print(f"\n标签分布:")
                for tag, count in sorted(result['summary']['tag_distribution'].items(), 
                                        key=lambda x: x[1], reverse=True)[:10]:
                    print(f"  - {tag}: {count}")
            print("="*60)
            
    except Exception as e:
        print(f"错误: {str(e)}", file=sys.stderr)
        if args.verbose:
            import traceback
            traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    import sys
    main()