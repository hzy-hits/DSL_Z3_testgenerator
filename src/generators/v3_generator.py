#!/usr/bin/env python3
"""
统一的 DSL 测试生成器 V3 - 进阶优化版
增强功能：
1. 配置驱动的测试生成策略
2. 更复杂的约束类型支持（时间约束、正则表达式、自定义函数）
3. 测试数据模板系统
4. 性能优化和缓存机制
5. 测试生成策略插件系统
"""

import argparse
import json
import yaml
import z3
from typing import List, Dict, Any, Set, Tuple, Optional, Union, Callable
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
import re
from datetime import datetime, timedelta
import hashlib
from abc import ABC, abstractmethod
import random
# from functools import lru_cache
import time


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
    PERFORMANCE = "performance"
    SECURITY = "security"
    TEMPLATE_BASED = "template_based"


@dataclass
class AttributeMetadata:
    """增强的属性元数据"""
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
    format: Optional[str] = None  # 如：email, url, date, time
    custom_validator: Optional[str] = None  # 自定义验证函数名
    dependencies: Optional[List[str]] = None  # 依赖的其他属性
    
    @property
    def is_numeric(self) -> bool:
        return self.type in ['integer', 'real']
    
    @property
    def is_collection(self) -> bool:
        return self.type.startswith('array[') or self.type.startswith('set[')
    
    @property
    def is_temporal(self) -> bool:
        return self.format in ['date', 'time', 'datetime', 'timestamp']
    
    @property
    def element_type(self) -> Optional[str]:
        if self.type.startswith('array['):
            return self.type[6:-1]
        elif self.type.startswith('set['):
            return self.type[4:-1]
        return None


@dataclass
class TestTemplate:
    """测试模板"""
    id: str
    name: str
    description: str
    test_type: TestType
    data_pattern: Dict[str, Any]
    expected_behavior: str
    tags: List[str] = field(default_factory=list)
    priority_modifier: int = 0
    applicable_entities: List[str] = field(default_factory=list)
    conditions: Dict[str, Any] = field(default_factory=dict)


@dataclass
class TestGenerationConfig:
    """测试生成配置"""
    max_tests_per_type: int = 20
    enable_combinatorial: bool = True
    combinatorial_strength: int = 2
    enable_scenarios: bool = True
    optimize_tests: bool = True
    value_strategy: str = "realistic"  # realistic, boundary, random
    enable_templates: bool = True
    template_coverage: float = 0.8
    performance_mode: bool = False
    cache_size: int = 1000
    parallel_generation: bool = False
    custom_strategies: List[str] = field(default_factory=list)
    constraint_solver_timeout: int = 5000  # 毫秒
    
    @classmethod
    def from_dict(cls, config_dict: Dict[str, Any]) -> 'TestGenerationConfig':
        return cls(**{k: v for k, v in config_dict.items() if k in cls.__annotations__})


class TestGenerationStrategy(ABC):
    """测试生成策略接口"""
    
    @abstractmethod
    def generate(self, context: Dict[str, Any]) -> List[Dict[str, Any]]:
        """生成测试数据"""
        pass
    
    @abstractmethod
    def applies_to(self, entity: Dict[str, Any]) -> bool:
        """检查策略是否适用于给定实体"""
        pass


class SmartValueGenerator:
    """智能值生成器"""
    
    def __init__(self, config: TestGenerationConfig):
        self.config = config
        self._cache = {}
        self._patterns = {
            'email': lambda: f"test_{random.randint(1000, 9999)}@example.com",
            'url': lambda: f"https://example.com/{random.choice(['api', 'web', 'app'])}/{random.randint(1, 100)}",
            'phone': lambda: f"+1{random.randint(1000000000, 9999999999)}",
            'uuid': lambda: f"{hashlib.md5(str(random.random()).encode()).hexdigest()[:8]}-"
                          f"{hashlib.md5(str(random.random()).encode()).hexdigest()[:4]}-"
                          f"{hashlib.md5(str(random.random()).encode()).hexdigest()[:4]}-"
                          f"{hashlib.md5(str(random.random()).encode()).hexdigest()[:12]}",
            'ipv4': lambda: f"{random.randint(1, 255)}.{random.randint(0, 255)}."
                           f"{random.randint(0, 255)}.{random.randint(1, 255)}",
        }
    
    def generate_value(self, attr: AttributeMetadata, context: Dict[str, Any] = None) -> Any:
        """生成属性值"""
        cache_key = f"{attr.name}_{attr.type}_{attr.format}"
        
        # 检查缓存
        if self.config.performance_mode and cache_key in self._cache:
            return self._cache[cache_key]
        
        value = self._generate_uncached_value(attr, context)
        
        # 存入缓存
        if self.config.performance_mode:
            self._cache[cache_key] = value
        
        return value
    
    def _generate_uncached_value(self, attr: AttributeMetadata, context: Dict[str, Any]) -> Any:
        """生成未缓存的值"""
        # 处理特殊格式
        if attr.format and attr.format in self._patterns:
            return self._patterns[attr.format]()
        
        # 处理时间类型
        if attr.is_temporal:
            return self._generate_temporal_value(attr)
        
        # 处理枚举
        if attr.enum:
            return random.choice(attr.enum)
        
        # 处理数值类型
        if attr.is_numeric:
            return self._generate_numeric_value(attr)
        
        # 处理字符串
        if attr.type == 'string':
            return self._generate_string_value(attr)
        
        # 处理布尔值
        if attr.type == 'boolean':
            return random.choice([True, False])
        
        # 处理集合
        if attr.is_collection:
            return self._generate_collection_value(attr)
        
        # 默认值
        return attr.default if attr.default is not None else None
    
    def _generate_temporal_value(self, attr: AttributeMetadata) -> Union[int, str]:
        """生成时间值"""
        now = datetime.now()
        
        if attr.format == 'timestamp':
            # 生成过去30天内的时间戳
            past_time = now - timedelta(days=random.randint(0, 30))
            return int(past_time.timestamp())
        elif attr.format == 'date':
            return now.strftime('%Y-%m-%d')
        elif attr.format == 'time':
            return now.strftime('%H:%M:%S')
        else:
            return now.isoformat()
    
    def _generate_numeric_value(self, attr: AttributeMetadata) -> Union[int, float]:
        """生成数值"""
        if self.config.value_strategy == 'boundary':
            # 边界值策略
            if attr.min is not None and attr.max is not None:
                return random.choice([attr.min, attr.max, (attr.min + attr.max) // 2])
            elif attr.min is not None:
                return attr.min
            elif attr.max is not None:
                return attr.max
        
        # 实际值策略
        min_val = attr.min if attr.min is not None else 0
        max_val = attr.max if attr.max is not None else 1000
        
        # 特殊处理金额相关字段
        if any(keyword in attr.name.lower() for keyword in ['amount', 'price', 'cost', 'fee']):
            min_val = max(min_val, 10)
            max_val = max(max_val, 10000)  # 确保 max 值足够大
        
        # 特殊处理时间戳字段
        if 'timestamp' in attr.name.lower() or 'time' in attr.name.lower():
            if attr.min is not None and attr.min > 1000000000:  # Unix timestamp
                min_val = attr.min
                max_val = max(attr.max if attr.max is not None else int(datetime.now().timestamp()), min_val + 86400)
        
        # 确保 min <= max
        if min_val > max_val:
            min_val, max_val = max_val, min_val
        
        if attr.type == 'integer':
            return random.randint(int(min_val), int(max_val))
        else:
            return round(random.uniform(float(min_val), float(max_val)), 2)
    
    def _generate_string_value(self, attr: AttributeMetadata) -> str:
        """生成字符串值"""
        if attr.pattern:
            # TODO: 实现基于正则表达式的字符串生成
            pass
        
        # 基于属性名生成合理的字符串
        base_names = {
            'name': ['Alice', 'Bob', 'Charlie', 'David', 'Emma'],
            'title': ['Manager', 'Developer', 'Designer', 'Analyst', 'Engineer'],
            'description': ['Test description', 'Sample text', 'Example content'],
            'code': [f'CODE{random.randint(1000, 9999)}', f'ID{random.randint(100, 999)}'],
            'status': ['active', 'pending', 'completed', 'cancelled'],
        }
        
        for key, values in base_names.items():
            if key in attr.name.lower():
                return random.choice(values)
        
        # 默认字符串
        return f"{attr.name}_value_{random.randint(1, 100)}"
    
    def _generate_collection_value(self, attr: AttributeMetadata) -> List[Any]:
        """生成集合值"""
        size = random.randint(0, 5)
        element_type = attr.element_type
        
        if element_type == 'integer':
            return [random.randint(1, 100) for _ in range(size)]
        elif element_type == 'string':
            return [f"item_{i}" for i in range(size)]
        else:
            return []


class AdvancedConstraintSolver:
    """高级约束求解器"""
    
    def __init__(self, timeout: int = 5000):
        self.timeout = timeout
        self.custom_functions = {}
        self._constraint_cache = {}
    
    def register_custom_function(self, name: str, func: Callable):
        """注册自定义函数"""
        self.custom_functions[name] = func
    
    def solve_constraints(self, constraints: List[str], variables: Dict[str, AttributeMetadata]) -> Optional[Dict[str, Any]]:
        """求解约束"""
        # 检查缓存
        cache_key = hashlib.md5(str(sorted(constraints)).encode()).hexdigest()
        if cache_key in self._constraint_cache:
            return self._constraint_cache[cache_key]
        
        solver = z3.Solver()
        solver.set("timeout", self.timeout)
        
        # 创建 Z3 变量
        z3_vars = self._create_z3_variables(variables)
        
        # 添加基本约束
        self._add_basic_constraints(solver, z3_vars, variables)
        
        # 解析并添加自定义约束
        for constraint in constraints:
            try:
                z3_constraint = self._parse_constraint(constraint, z3_vars, variables)
                if z3_constraint is not None:
                    solver.add(z3_constraint)
            except Exception as e:
                print(f"Warning: Failed to parse constraint '{constraint}': {e}")
        
        # 求解
        if solver.check() == z3.sat:
            model = solver.model()
            result = self._extract_solution(model, z3_vars, variables)
            self._constraint_cache[cache_key] = result
            return result
        
        return None
    
    def _create_z3_variables(self, variables: Dict[str, AttributeMetadata]) -> Dict[str, Any]:
        """创建 Z3 变量"""
        z3_vars = {}
        
        for var_name, attr in variables.items():
            if attr.is_numeric:
                if attr.type == 'integer':
                    z3_vars[var_name] = z3.Int(var_name)
                else:
                    z3_vars[var_name] = z3.Real(var_name)
            elif attr.type == 'boolean':
                z3_vars[var_name] = z3.Bool(var_name)
            elif attr.type == 'string' and attr.enum:
                # 为枚举创建整数变量
                z3_vars[var_name] = z3.Int(var_name)
            # 其他类型暂不支持 Z3 求解
        
        return z3_vars
    
    def _add_basic_constraints(self, solver: z3.Solver, z3_vars: Dict[str, Any], 
                              variables: Dict[str, AttributeMetadata]):
        """添加基本约束"""
        for var_name, attr in variables.items():
            if var_name not in z3_vars:
                continue
                
            var = z3_vars[var_name]
            
            # 范围约束
            if attr.min is not None:
                solver.add(var >= attr.min)
            if attr.max is not None:
                solver.add(var <= attr.max)
            
            # 枚举约束
            if attr.enum and isinstance(var, z3.ArithRef):
                solver.add(z3.And(var >= 0, var < len(attr.enum)))
            
            # 特殊业务约束
            if any(keyword in var_name for keyword in ['amount', 'price', 'cost']):
                solver.add(var > 0)
    
    def _parse_constraint(self, constraint: str, z3_vars: Dict[str, Any], 
                         variables: Dict[str, AttributeMetadata]) -> Optional[Any]:
        """解析约束表达式"""
        # 处理自定义函数
        for func_name, func in self.custom_functions.items():
            if func_name in constraint:
                # TODO: 实现自定义函数的 Z3 表达式转换
                pass
        
        # 处理时间约束
        if any(keyword in constraint for keyword in ['before', 'after', 'between']):
            return self._parse_temporal_constraint(constraint, z3_vars, variables)
        
        # 处理常规比较和逻辑表达式
        return self._parse_basic_constraint(constraint, z3_vars, variables)
    
    def _parse_temporal_constraint(self, constraint: str, z3_vars: Dict[str, Any], 
                                  variables: Dict[str, AttributeMetadata]) -> Optional[Any]:
        """解析时间约束"""
        # TODO: 实现时间约束解析
        return None
    
    def _parse_basic_constraint(self, constraint: str, z3_vars: Dict[str, Any], 
                               variables: Dict[str, AttributeMetadata]) -> Optional[Any]:
        """解析基本约束"""
        try:
            # 替换变量名
            expr = constraint
            for var_name in z3_vars:
                if var_name in expr:
                    expr = expr.replace(var_name, f"z3_vars['{var_name}']")
            
            # 安全评估
            namespace = {
                'z3_vars': z3_vars,
                'z3': z3,
                'And': z3.And,
                'Or': z3.Or,
                'Not': z3.Not,
                'Implies': z3.Implies,
            }
            
            return eval(expr, namespace)
        except:
            return None
    
    def _extract_solution(self, model: z3.Model, z3_vars: Dict[str, Any], 
                         variables: Dict[str, AttributeMetadata]) -> Dict[str, Any]:
        """提取求解结果"""
        result = {}
        
        for var_name, var in z3_vars.items():
            attr = variables[var_name]
            value = model.eval(var)
            
            if isinstance(value, z3.IntNumRef):
                result[var_name] = value.as_long()
            elif isinstance(value, z3.RatNumRef):
                result[var_name] = float(value.as_decimal(2))
            elif isinstance(value, z3.BoolRef):
                result[var_name] = z3.is_true(value)
            
            # 处理枚举
            if attr.enum and var_name in result:
                index = result[var_name]
                if 0 <= index < len(attr.enum):
                    result[var_name] = attr.enum[index]
        
        return result


class TemplateEngine:
    """测试模板引擎"""
    
    def __init__(self):
        self.templates: List[TestTemplate] = []
        self._load_builtin_templates()
    
    def _load_builtin_templates(self):
        """加载内置模板"""
        # 安全测试模板
        self.templates.append(TestTemplate(
            id="SEC_001",
            name="SQL Injection Test",
            description="Test with SQL injection patterns",
            test_type=TestType.SECURITY,
            data_pattern={
                "*_name": "'; DROP TABLE users; --",
                "*_id": "1 OR 1=1",
                "*_query": "SELECT * FROM users WHERE id = '1' OR '1'='1'"
            },
            expected_behavior="fail",
            tags=["security", "sql_injection"],
            priority_modifier=2,
            applicable_entities=["*"]
        ))
        
        # 性能测试模板
        self.templates.append(TestTemplate(
            id="PERF_001",
            name="Large Data Volume Test",
            description="Test with large data volumes",
            test_type=TestType.PERFORMANCE,
            data_pattern={
                "*_list": "generate_large_array(1000)",
                "*_count": 10000,
                "*_size": 1048576  # 1MB
            },
            expected_behavior="pass",
            tags=["performance", "volume"],
            priority_modifier=1,
            applicable_entities=["*"]
        ))
        
        # 边界值模板
        self.templates.append(TestTemplate(
            id="BOUND_001",
            name="Unicode Boundary Test",
            description="Test with unicode characters",
            test_type=TestType.BOUNDARY,
            data_pattern={
                "*_name": "测试用户🚀",
                "*_description": "Special chars: @#$%^&*()",
                "*_text": "Multi-line\ntext\twith\ttabs"
            },
            expected_behavior="pass",
            tags=["boundary", "unicode"],
            priority_modifier=0,
            applicable_entities=["*"]
        ))
    
    def apply_template(self, template: TestTemplate, entity: Dict[str, Any], 
                      base_data: Dict[str, Any]) -> Dict[str, Any]:
        """应用模板到测试数据"""
        result = base_data.copy()
        
        for pattern_key, pattern_value in template.data_pattern.items():
            if pattern_key.startswith('*'):
                # 通配符匹配
                suffix = pattern_key[1:]
                for key in base_data:
                    if key.endswith(suffix):
                        result[key] = self._process_pattern_value(pattern_value)
            else:
                # 精确匹配
                if pattern_key in result:
                    result[pattern_key] = self._process_pattern_value(pattern_value)
        
        return result
    
    def _process_pattern_value(self, value: Any) -> Any:
        """处理模板值"""
        if isinstance(value, str) and value.startswith('generate_'):
            # 处理生成函数
            if value == 'generate_large_array(1000)':
                return list(range(1000))
            # 可以添加更多生成函数
        
        return value
    
    def find_applicable_templates(self, entity: Dict[str, Any], 
                                 test_type: TestType = None) -> List[TestTemplate]:
        """查找适用的模板"""
        applicable = []
        
        for template in self.templates:
            # 检查测试类型
            if test_type and template.test_type != test_type:
                continue
            
            # 检查实体适用性
            if '*' in template.applicable_entities:
                applicable.append(template)
            elif entity['name'] in template.applicable_entities:
                applicable.append(template)
        
        return applicable


class UnifiedDSLTestGeneratorV3:
    """统一的 DSL 测试生成器 V3"""
    
    def __init__(self, dsl_file: str, config: TestGenerationConfig = None):
        self.dsl_file = dsl_file
        self.config = config or TestGenerationConfig()
        
        # 加载 DSL
        with open(dsl_file, 'r', encoding='utf-8') as f:
            self.dsl_model = yaml.safe_load(f)
        
        # 初始化组件
        self.value_generator = SmartValueGenerator(self.config)
        self.constraint_solver = AdvancedConstraintSolver(self.config.constraint_solver_timeout)
        self.template_engine = TemplateEngine()
        
        # 内部映射
        self.entity_map = {}
        self.attribute_map = {}
        self.test_counter = 0
        
        # 性能统计
        self.generation_stats = {
            'start_time': time.time(),
            'solver_calls': 0,
            'cache_hits': 0,
            'tests_generated': 0
        }
        
        # 构建映射
        self._build_internal_mappings()
    
    def generate_tests(self) -> Dict[str, Any]:
        """生成测试"""
        print(f"[V3] Starting test generation for: {self.dsl_model.get('domain', 'Unknown')}")
        
        # 生成所有测试
        all_tests = self._generate_all_test_types()
        
        # 应用模板
        if self.config.enable_templates:
            all_tests.extend(self._generate_template_based_tests())
        
        # 优化和去重
        optimized_tests = self._optimize_test_suite(all_tests)
        
        # 统计信息
        self.generation_stats['end_time'] = time.time()
        self.generation_stats['tests_generated'] = len(optimized_tests)
        self.generation_stats['duration'] = self.generation_stats['end_time'] - self.generation_stats['start_time']
        
        print(f"[V3] Generated {len(optimized_tests)} tests in {self.generation_stats['duration']:.2f}s")
        print(f"[V3] Solver calls: {self.generation_stats['solver_calls']}, Cache hits: {self.generation_stats['cache_hits']}")
        
        # 格式化输出
        return self._format_output(optimized_tests)
    
    def _build_internal_mappings(self):
        """构建内部映射"""
        for entity in self.dsl_model.get('entities', []):
            entity_name = entity['name']
            self.entity_map[entity_name.lower()] = entity
            
            for attr in entity.get('attributes', []):
                # 创建增强的属性元数据
                attr_meta = AttributeMetadata(
                    name=attr['name'],
                    type=attr['type'],
                    min=attr.get('min'),
                    max=attr.get('max'),
                    enum=attr.get('enum'),
                    pattern=attr.get('pattern'),
                    optional=attr.get('optional', False),
                    default=attr.get('default'),
                    unique=attr.get('unique', False),
                    nullable=attr.get('nullable', False),
                    description=attr.get('description'),
                    format=attr.get('format'),
                    custom_validator=attr.get('validator'),
                    dependencies=attr.get('dependencies', [])
                )
                
                attr_key = f"{entity_name.lower()}_{attr['name']}"
                self.attribute_map[attr_key] = {
                    'entity': entity,
                    'attribute': attr_meta
                }
    
    def _generate_all_test_types(self) -> List[Dict[str, Any]]:
        """生成所有类型的测试"""
        all_tests = []
        
        # 基础测试类型
        test_generators = [
            (self._generate_functional_tests, "Functional"),
            (self._generate_boundary_tests, "Boundary"),
            (self._generate_negative_tests, "Negative"),
            (self._generate_rule_tests, "Rule"),
            (self._generate_constraint_tests, "Constraint"),
        ]
        
        # 高级测试类型
        if self.config.enable_scenarios:
            test_generators.append((self._generate_scenario_tests, "Scenario"))
        
        if 'state_machines' in self.dsl_model:
            test_generators.append((self._generate_state_machine_tests, "State Machine"))
        
        if self.config.enable_combinatorial:
            test_generators.append((self._generate_combinatorial_tests, "Combinatorial"))
        
        # 执行生成
        for generator, name in test_generators:
            print(f"  Generating {name} tests...")
            tests = generator()
            all_tests.extend(tests)
            print(f"    Generated {len(tests)} {name} tests")
        
        return all_tests
    
    def _generate_functional_tests(self) -> List[Dict[str, Any]]:
        """生成功能测试"""
        tests = []
        
        for entity_name, entity in self.entity_map.items():
            # 使用约束求解器生成有效数据
            variables = {}
            for attr in entity.get('attributes', []):
                attr_key = f"{entity_name}_{attr['name']}"
                if attr_key in self.attribute_map:
                    variables[attr_key] = self.attribute_map[attr_key]['attribute']
            
            # 求解约束
            self.generation_stats['solver_calls'] += 1
            solution = self.constraint_solver.solve_constraints(
                self.dsl_model.get('constraints', []),
                variables
            )
            
            if solution:
                test_data = solution
            else:
                # 使用智能生成器
                test_data = {}
                for var_name, attr in variables.items():
                    test_data[var_name] = self.value_generator.generate_value(attr)
            
            tests.append({
                "id": self._next_test_id(),
                "name": f"Create {entity['name']} with valid data",
                "type": TestType.FUNCTIONAL.value,
                "description": f"Functional test for {entity['name']}",
                "test_data": test_data,
                "expected_result": "pass",
                "priority": 8,
                "tags": ["functional", entity_name]
            })
            
            if len(tests) >= self.config.max_tests_per_type:
                break
        
        return tests
    
    def _generate_boundary_tests(self) -> List[Dict[str, Any]]:
        """生成边界测试"""
        tests = []
        
        for attr_key, attr_info in self.attribute_map.items():
            attr = attr_info['attribute']
            
            if not attr.is_numeric:
                continue
            
            # 生成边界值
            boundary_values = []
            if attr.min is not None:
                boundary_values.extend([attr.min - 1, attr.min, attr.min + 1])
            if attr.max is not None:
                boundary_values.extend([attr.max - 1, attr.max, attr.max + 1])
            
            for value in boundary_values:
                test_data = {attr_key: value}
                expected = "pass" if (attr.min is None or value >= attr.min) and \
                                   (attr.max is None or value <= attr.max) else "fail"
                
                tests.append({
                    "id": self._next_test_id(),
                    "name": f"Boundary test for {attr_key} = {value}",
                    "type": TestType.BOUNDARY.value,
                    "description": f"Testing boundary value {value}",
                    "test_data": test_data,
                    "expected_result": expected,
                    "priority": 7,
                    "tags": ["boundary", attr_key]
                })
                
                if len(tests) >= self.config.max_tests_per_type:
                    break
        
        return tests
    
    def _generate_negative_tests(self) -> List[Dict[str, Any]]:
        """生成负面测试"""
        tests = []
        
        # 类型错误测试
        for attr_key, attr_info in self.attribute_map.items():
            attr = attr_info['attribute']
            
            # 生成错误类型的数据
            wrong_values = {
                'integer': "not_a_number",
                'real': "not_a_float",
                'boolean': "not_a_bool",
                'string': 12345 if attr.type == 'string' else None
            }
            
            if attr.type in wrong_values:
                test_data = {attr_key: wrong_values[attr.type]}
                
                tests.append({
                    "id": self._next_test_id(),
                    "name": f"Type validation for {attr_key}",
                    "type": TestType.NEGATIVE.value,
                    "description": f"Testing wrong type for {attr_key}",
                    "test_data": test_data,
                    "expected_result": "fail",
                    "priority": 6,
                    "tags": ["negative", "type_validation", attr_key]
                })
        
        return tests[:self.config.max_tests_per_type]
    
    def _generate_rule_tests(self) -> List[Dict[str, Any]]:
        """生成规则测试"""
        tests = []
        
        for rule in self.dsl_model.get('rules', []):
            # 规则激活测试
            # TODO: 实现更复杂的规则条件解析
            tests.append({
                "id": self._next_test_id(),
                "name": f"Rule activation: {rule.get('name', 'Unknown')}",
                "type": TestType.RULE_ACTIVATION.value,
                "description": f"Test rule activation conditions",
                "test_data": {},  # 需要根据规则条件生成
                "expected_result": "pass",
                "priority": 7,
                "tags": ["rule", "activation"]
            })
            
            if len(tests) >= self.config.max_tests_per_type:
                break
        
        return tests
    
    def _generate_constraint_tests(self) -> List[Dict[str, Any]]:
        """生成约束测试"""
        tests = []
        
        for constraint in self.dsl_model.get('constraints', []):
            # 约束满足测试
            tests.append({
                "id": self._next_test_id(),
                "name": f"Constraint satisfaction: {constraint}",
                "type": TestType.CONSTRAINT_SATISFACTION.value,
                "description": "Test constraint is satisfied",
                "test_data": {},  # 需要生成满足约束的数据
                "expected_result": "pass",
                "priority": 8,
                "tags": ["constraint", "satisfaction"]
            })
            
            # 约束违反测试
            tests.append({
                "id": self._next_test_id(),
                "name": f"Constraint violation: {constraint}",
                "type": TestType.CONSTRAINT_VIOLATION.value,
                "description": "Test constraint is violated",
                "test_data": {},  # 需要生成违反约束的数据
                "expected_result": "fail",
                "priority": 7,
                "tags": ["constraint", "violation"]
            })
            
            if len(tests) >= self.config.max_tests_per_type:
                break
        
        return tests
    
    def _generate_scenario_tests(self) -> List[Dict[str, Any]]:
        """生成场景测试"""
        tests = []
        
        for scenario in self.dsl_model.get('scenarios', []):
            test_data = {}
            
            # 根据场景步骤生成数据
            for step in scenario.get('steps', []):
                # TODO: 实现场景步骤解析
                pass
            
            tests.append({
                "id": self._next_test_id(),
                "name": f"Scenario: {scenario.get('name', 'Unknown')}",
                "type": TestType.SCENARIO.value,
                "description": scenario.get('description', ''),
                "test_data": test_data,
                "expected_result": "pass",
                "priority": 6,
                "tags": ["scenario"] + scenario.get('tags', [])
            })
        
        return tests
    
    def _generate_state_machine_tests(self) -> List[Dict[str, Any]]:
        """生成状态机测试"""
        tests = []
        
        for sm in self.dsl_model.get('state_machines', []):
            for transition in sm.get('transitions', []):
                test_data = {
                    "current_state": transition['from'],
                    "event": transition.get('event', ''),
                    "expected_state": transition['to']
                }
                
                tests.append({
                    "id": self._next_test_id(),
                    "name": f"State transition: {transition['from']} -> {transition['to']}",
                    "type": TestType.STATE_TRANSITION.value,
                    "description": f"Test state machine transition",
                    "test_data": test_data,
                    "expected_result": "pass",
                    "priority": 7,
                    "tags": ["state_machine", "transition"]
                })
        
        return tests[:self.config.max_tests_per_type]
    
    def _generate_combinatorial_tests(self) -> List[Dict[str, Any]]:
        """生成组合测试"""
        tests = []
        
        # TODO: 实现 N-way 组合测试生成
        # 这里需要实现 pairwise 或 n-way 算法
        
        return tests
    
    def _generate_template_based_tests(self) -> List[Dict[str, Any]]:
        """生成基于模板的测试"""
        tests = []
        
        for entity_name, entity in self.entity_map.items():
            # 查找适用的模板
            templates = self.template_engine.find_applicable_templates(entity)
            
            for template in templates:
                # 生成基础数据
                base_data = {}
                for attr in entity.get('attributes', []):
                    attr_key = f"{entity_name}_{attr['name']}"
                    if attr_key in self.attribute_map:
                        base_data[attr_key] = self.value_generator.generate_value(
                            self.attribute_map[attr_key]['attribute']
                        )
                
                # 应用模板
                test_data = self.template_engine.apply_template(template, entity, base_data)
                
                tests.append({
                    "id": self._next_test_id(),
                    "name": f"{template.name} for {entity['name']}",
                    "type": template.test_type.value,
                    "description": template.description,
                    "test_data": test_data,
                    "expected_result": template.expected_behavior,
                    "priority": 5 + template.priority_modifier,
                    "tags": template.tags + [entity_name, "template"]
                })
                
                if len(tests) >= 5:  # 限制模板测试数量
                    break
        
        return tests
    
    def _optimize_test_suite(self, tests: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """优化测试套件"""
        if not self.config.optimize_tests:
            return tests
        
        # 简单的去重（基于测试数据的哈希）
        seen_hashes = set()
        optimized = []
        
        for test in tests:
            # 计算测试数据的哈希
            data_str = json.dumps(test['test_data'], sort_keys=True)
            data_hash = hashlib.md5(data_str.encode()).hexdigest()
            
            if data_hash not in seen_hashes:
                seen_hashes.add(data_hash)
                optimized.append(test)
            else:
                self.generation_stats['cache_hits'] += 1
        
        # 按优先级排序
        optimized.sort(key=lambda t: t.get('priority', 5), reverse=True)
        
        return optimized
    
    def _next_test_id(self) -> str:
        """生成下一个测试ID"""
        self.test_counter += 1
        return f"TEST_{self.test_counter:04d}"
    
    def _format_output(self, tests: List[Dict[str, Any]]) -> Dict[str, Any]:
        """格式化输出"""
        # 按类型分组
        test_suites = {}
        for test in tests:
            test_type = test['type']
            if test_type not in test_suites:
                test_suites[test_type] = []
            test_suites[test_type].append(test)
        
        # 统计信息
        tag_counts = {}
        priority_counts = {}
        
        for test in tests:
            for tag in test.get('tags', []):
                tag_counts[tag] = tag_counts.get(tag, 0) + 1
            
            priority = test.get('priority', 5)
            priority_level = 'high' if priority >= 8 else 'medium' if priority >= 5 else 'low'
            priority_counts[priority_level] = priority_counts.get(priority_level, 0) + 1
        
        return {
            "meta": {
                "generator": "Unified DSL Test Generator v3.0",
                "domain": self.dsl_model.get('domain', 'Unknown'),
                "timestamp": datetime.now().isoformat(),
                "dsl_file": self.dsl_file,
                "config": {
                    "max_tests_per_type": self.config.max_tests_per_type,
                    "enable_combinatorial": self.config.enable_combinatorial,
                    "enable_templates": self.config.enable_templates,
                    "value_strategy": self.config.value_strategy,
                    "performance_mode": self.config.performance_mode
                },
                "generation_stats": self.generation_stats
            },
            "summary": {
                "total_tests": len(tests),
                "test_distribution": {test_type: len(tests) for test_type, tests in test_suites.items()},
                "tag_distribution": tag_counts,
                "priority_distribution": priority_counts
            },
            "test_suites": test_suites
        }


def main():
    parser = argparse.ArgumentParser(description="Unified DSL Test Generator V3")
    parser.add_argument("dsl_file", help="Path to DSL YAML file")
    parser.add_argument("-o", "--output", default="tests_v3.json", help="Output file")
    parser.add_argument("-c", "--config", help="Configuration file (JSON)")
    parser.add_argument("--max-tests", type=int, default=20, help="Max tests per type")
    parser.add_argument("--strategy", choices=['realistic', 'boundary', 'random'], 
                       default='realistic', help="Value generation strategy")
    parser.add_argument("--performance", action="store_true", help="Enable performance mode")
    parser.add_argument("--no-templates", action="store_true", help="Disable template tests")
    
    args = parser.parse_args()
    
    # 加载配置
    config_dict = {}
    if args.config:
        with open(args.config, 'r') as f:
            config_dict = json.load(f)
    
    # 命令行参数覆盖配置
    config_dict['max_tests_per_type'] = args.max_tests
    config_dict['value_strategy'] = args.strategy
    config_dict['performance_mode'] = args.performance
    config_dict['enable_templates'] = not args.no_templates
    
    config = TestGenerationConfig.from_dict(config_dict)
    
    # 生成测试
    generator = UnifiedDSLTestGeneratorV3(args.dsl_file, config)
    result = generator.generate_tests()
    
    # 保存结果
    with open(args.output, 'w', encoding='utf-8') as f:
        json.dump(result, f, ensure_ascii=False, indent=2)
    
    print(f"\nTests saved to: {args.output}")


if __name__ == "__main__":
    main()