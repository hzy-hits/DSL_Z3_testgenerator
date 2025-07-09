# DSL测试生成系统 V2.0 架构设计

## 设计原则

1. **正确性优先**：宁可不生成，也不生成错误的测试
2. **关注点分离**：每层只负责一个职责
3. **可验证性**：每个阶段的输出都可独立验证
4. **最小化原则**：生成最少的必要测试
5. **可扩展性**：易于添加新的测试策略和领域

## 分层架构

```
┌────────────────────────────────────────────────────┐
│                  API Layer                         │
│         (统一的对外接口，CLI/Web/SDK)               │
└──────────────────────┬─────────────────────────────┘
                       │
┌──────────────────────▼─────────────────────────────┐
│               DSL Layer                            │
│      (解析、验证、规范化DSL定义)                    │
│  ┌─────────────┬──────────────┬────────────────┐  │
│  │   Parser    │  Validator   │  Normalizer    │  │
│  └─────────────┴──────────────┴────────────────┘  │
└──────────────────────┬─────────────────────────────┘
                       │ DSLModel
┌──────────────────────▼─────────────────────────────┐
│           Test Strategy Layer                      │
│         (决定测试策略和覆盖目标)                    │
│  ┌─────────────┬──────────────┬────────────────┐  │
│  │  Coverage   │   Priority    │   Minimizer    │  │
│  │  Analyzer   │   Calculator  │                │  │
│  └─────────────┴──────────────┴────────────────┘  │
└──────────────────────┬─────────────────────────────┘
                       │ TestPlan
┌──────────────────────▼─────────────────────────────┐
│          Constraint System Layer                   │
│      (构建和求解约束系统，保证正确性)               │
│  ┌─────────────┬──────────────┬────────────────┐  │
│  │ Constraint  │   Z3 Solver  │   Solution     │  │
│  │  Builder    │   Adapter    │   Verifier     │  │
│  └─────────────┴──────────────┴────────────────┘  │
└──────────────────────┬─────────────────────────────┘
                       │ TestData
┌──────────────────────▼─────────────────────────────┐
│            Output Layer                            │
│         (格式化和输出测试用例)                      │
│  ┌─────────────┬──────────────┬────────────────┐  │
│  │  Formatter  │  Exporter    │   Reporter     │  │
│  └─────────────┴──────────────┴────────────────┘  │
└────────────────────────────────────────────────────┘
```

## 核心组件设计

### 1. DSL Layer

```python
from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import List, Dict, Any, Optional

@dataclass
class Entity:
    """实体定义"""
    name: str
    attributes: List['Attribute']
    
@dataclass
class Attribute:
    """属性定义"""
    name: str
    type: str
    constraints: List['Constraint']
    
    @property
    def full_name(self) -> str:
        """获取包含实体名的完整属性名"""
        return f"{self.entity.name.lower()}_{self.name}"

@dataclass
class Constraint:
    """约束定义"""
    expression: str
    type: str  # 'range', 'enum', 'relation', 'implication'
    
@dataclass
class Rule:
    """业务规则"""
    name: str
    condition: str
    consequence: str
    priority: int = 0

@dataclass
class DSLModel:
    """规范化的DSL模型"""
    domain: str
    entities: List[Entity]
    constraints: List[Constraint]
    rules: List[Rule]
    test_hints: List['TestHint']  # 用户提供的测试提示
```

### 2. Test Strategy Layer

```python
@dataclass
class TestObjective:
    """测试目标"""
    type: str  # 'constraint', 'rule', 'boundary', 'equivalence'
    target: str  # 要测试的约束或规则
    priority: int
    reason: str  # 为什么需要这个测试

@dataclass
class TestPlan:
    """测试计划"""
    objectives: List[TestObjective]
    coverage_goals: Dict[str, float]  # 覆盖目标
    max_tests: Optional[int]  # 最大测试数量
    
class TestStrategyEngine:
    """测试策略引擎"""
    
    def create_test_plan(self, model: DSLModel) -> TestPlan:
        """基于DSL模型创建测试计划"""
        objectives = []
        
        # 1. 分析约束覆盖
        for constraint in model.constraints:
            # 边界测试
            if self._is_boundary_testable(constraint):
                objectives.append(TestObjective(
                    type='boundary',
                    target=constraint.expression,
                    priority=self._calculate_priority(constraint),
                    reason=f"Test boundary values for {constraint.expression}"
                ))
            
        # 2. 分析规则覆盖
        for rule in model.rules:
            # 规则激活测试
            objectives.append(TestObjective(
                type='rule_active',
                target=rule.name,
                priority=rule.priority,
                reason=f"Test rule activation: {rule.name}"
            ))
            # 规则非激活测试
            objectives.append(TestObjective(
                type='rule_inactive',
                target=rule.name,
                priority=rule.priority,
                reason=f"Test rule non-activation: {rule.name}"
            ))
        
        # 3. 最小化测试集
        minimized = self._minimize_objectives(objectives)
        
        return TestPlan(
            objectives=minimized,
            coverage_goals={'constraint': 1.0, 'rule': 1.0},
            max_tests=len(minimized)
        )
```

### 3. Constraint System Layer

```python
class ConstraintSystem:
    """约束系统 - 核心正确性保证"""
    
    def __init__(self, model: DSLModel):
        self.model = model
        self.solver = Z3Solver()
        self._build_base_constraints()
    
    def _build_base_constraints(self):
        """构建基础约束系统"""
        # 1. 创建变量
        for entity in self.model.entities:
            for attr in entity.attributes:
                self.solver.add_variable(attr.full_name, attr.type)
        
        # 2. 添加所有约束
        for constraint in self.model.constraints:
            z3_expr = self._translate_constraint(constraint)
            self.solver.add_constraint(z3_expr)
        
        # 3. 添加所有规则作为软约束
        for rule in self.model.rules:
            z3_rule = self._translate_rule(rule)
            self.solver.add_soft_constraint(z3_rule, weight=rule.priority)
    
    def generate_test_data(self, objective: TestObjective) -> Optional[TestData]:
        """为特定测试目标生成数据"""
        self.solver.push()
        
        try:
            # 根据测试目标添加额外约束
            if objective.type == 'boundary':
                self._add_boundary_constraints(objective)
            elif objective.type == 'rule_active':
                self._add_rule_activation_constraints(objective)
            elif objective.type == 'rule_inactive':
                self._add_rule_deactivation_constraints(objective)
            
            # 求解
            if self.solver.check():
                model = self.solver.get_model()
                data = self._extract_values(model)
                
                # 验证生成的数据
                if self._verify_solution(data, objective):
                    return TestData(
                        values=data,
                        objective=objective,
                        satisfied_constraints=self._get_satisfied_constraints(data),
                        activated_rules=self._get_activated_rules(data)
                    )
            
            return None
            
        finally:
            self.solver.pop()
    
    def _verify_solution(self, data: Dict[str, Any], objective: TestObjective) -> bool:
        """验证解是否满足所有约束和测试目标"""
        # 1. 验证所有硬约束
        for constraint in self.model.constraints:
            if not self._evaluate_constraint(constraint, data):
                return False
        
        # 2. 验证测试目标
        if objective.type == 'rule_active':
            rule = self._find_rule(objective.target)
            if not self._is_rule_activated(rule, data):
                return False
            if not self._evaluate_expression(rule.consequence, data):
                return False
        
        return True
```

### 4. 最小化策略

```python
class TestMinimizer:
    """测试最小化器"""
    
    def minimize(self, objectives: List[TestObjective], model: DSLModel) -> List[TestObjective]:
        """最小化测试集，去除冗余"""
        # 1. 构建覆盖矩阵
        coverage_matrix = self._build_coverage_matrix(objectives, model)
        
        # 2. 使用贪心算法选择最少的测试
        selected = []
        uncovered = set(range(len(model.constraints) + len(model.rules)))
        
        while uncovered:
            # 选择覆盖最多未覆盖项的测试
            best_obj = None
            best_coverage = set()
            
            for obj in objectives:
                if obj in selected:
                    continue
                
                coverage = coverage_matrix[obj] & uncovered
                if len(coverage) > len(best_coverage):
                    best_obj = obj
                    best_coverage = coverage
            
            if best_obj:
                selected.append(best_obj)
                uncovered -= best_coverage
            else:
                break
        
        return selected
```

## 关键改进

### 1. 正确性保证
- **生成时验证**：在Z3求解时就保证所有约束
- **双重验证**：求解后再次验证确保正确
- **失败即停止**：无法生成正确数据时不强行生成

### 2. 测试最小化
- **覆盖分析**：分析每个测试覆盖的约束和规则
- **冗余消除**：去除覆盖相同内容的测试
- **优先级排序**：重要测试优先生成

### 3. 可解释性
- **测试目标明确**：每个测试都有明确的目标
- **覆盖报告**：显示每个测试覆盖了什么
- **生成原因**：解释为什么需要这个测试

### 4. 扩展性
- **插件式架构**：易于添加新的测试策略
- **领域无关**：核心引擎不包含业务逻辑
- **配置驱动**：通过配置改变行为

## 实现路线图

### Phase 1: 核心框架（1周）
1. 实现基础数据结构
2. 实现DSL解析器
3. 实现基础约束系统

### Phase 2: 测试策略（1周）
1. 实现覆盖分析
2. 实现测试最小化
3. 实现优先级计算

### Phase 3: 完整系统（2周）
1. 集成所有组件
2. 实现输出格式化
3. 添加CLI界面

### Phase 4: 优化和扩展（持续）
1. 性能优化
2. 添加更多测试策略
3. 支持更多输出格式

## 成功指标

1. **正确性**：100%生成的测试满足所有约束
2. **最小性**：测试数量减少60%以上
3. **覆盖率**：达到指定的覆盖目标
4. **性能**：中等规模DSL在10秒内完成
5. **可用性**：清晰的错误信息和测试报告