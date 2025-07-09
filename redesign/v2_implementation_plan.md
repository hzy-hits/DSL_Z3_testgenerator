# V2.0 实现计划

## 原型验证结果

原型成功展示了新架构的核心优势：

1. **正确性保证** ✅
   - 所有生成的测试数据都满足约束
   - 规则测试正确激活/不激活
   - 生成前后双重验证

2. **测试最小化** ✅
   - 只生成了5个必要测试（相比之前的50+）
   - 每个测试都有明确目的
   - 没有冗余

3. **清晰的架构** ✅
   - 关注点分离明确
   - 无业务硬编码
   - 易于扩展

## 完整实现路线图

### Phase 1: 基础框架（第1周）

#### 1.1 完善数据模型
```python
# 添加更多属性类型支持
class AttributeType(Enum):
    INTEGER = "integer"
    REAL = "real"
    BOOLEAN = "boolean"
    STRING = "string"
    DATE = "date"
    ENUM = "enum"
    ARRAY = "array"
    SET = "set"

# 支持更复杂的约束类型
class ConstraintType(Enum):
    RANGE = "range"
    PATTERN = "pattern"
    RELATION = "relation"
    IMPLICATION = "implication"
    COLLECTION = "collection"
```

#### 1.2 增强DSL解析器
```python
class DSLParser:
    """Parse YAML DSL files into normalized model"""
    
    def parse_file(self, path: str) -> DSLModel:
        # 1. Load YAML
        # 2. Validate structure
        # 3. Normalize to internal model
        # 4. Validate references
        pass
    
    def validate_model(self, model: DSLModel) -> List[str]:
        """Validate model consistency"""
        errors = []
        # Check all references exist
        # Check no circular dependencies
        # Check constraint syntax
        return errors
```

#### 1.3 改进表达式解析
```python
class ExpressionParser:
    """Robust expression parser with error handling"""
    
    def parse(self, expr: str) -> AST:
        # Use proper lexer/parser (e.g., PLY or pyparsing)
        # Support full expression syntax
        # Provide helpful error messages
        pass
```

### Phase 2: 测试策略引擎（第2周）

#### 2.1 覆盖分析器
```python
class CoverageAnalyzer:
    """Analyze what each test covers"""
    
    def analyze_coverage(self, test: TestCase, model: DSLModel) -> CoverageReport:
        report = CoverageReport()
        
        # 1. Constraint coverage
        for constraint in model.constraints:
            if self._test_covers_constraint(test, constraint):
                report.add_constraint_coverage(constraint)
        
        # 2. Rule coverage
        for rule in model.rules:
            if self._test_activates_rule(test, rule):
                report.add_rule_activation(rule)
        
        # 3. Boundary coverage
        for attr in model.get_all_attributes():
            if self._test_covers_boundary(test, attr):
                report.add_boundary_coverage(attr)
        
        return report
```

#### 2.2 测试优先级计算
```python
class PriorityCalculator:
    """Calculate test priority based on multiple factors"""
    
    def calculate(self, objective: TestObjective, model: DSLModel) -> int:
        priority = objective.base_priority
        
        # Adjust based on:
        # - Rule importance
        # - Constraint criticality
        # - User hints
        # - Historical failures
        
        return priority
```

#### 2.3 智能最小化
```python
class SmartMinimizer:
    """Minimize test set while maintaining coverage"""
    
    def minimize(self, tests: List[TestCase], coverage_goals: Dict[str, float]) -> List[TestCase]:
        # 1. Build coverage matrix
        # 2. Use set cover algorithm
        # 3. Respect priority constraints
        # 4. Ensure coverage goals are met
        pass
```

### Phase 3: 约束求解优化（第3周）

#### 3.1 增量求解
```python
class IncrementalSolver:
    """Reuse solver state for efficiency"""
    
    def __init__(self, model: DSLModel):
        self.base_solver = z3.Solver()
        self._setup_base_constraints(model)
    
    def solve_incremental(self, objectives: List[TestObjective]) -> List[Solution]:
        # Reuse common constraints
        # Use push/pop efficiently
        # Cache intermediate results
        pass
```

#### 3.2 冲突处理
```python
class ConflictResolver:
    """Handle conflicting constraints and rules"""
    
    def resolve_conflicts(self, model: DSLModel) -> List[ConflictResolution]:
        # 1. Detect conflicts
        # 2. Prioritize based on rule weights
        # 3. Suggest resolutions
        # 4. Log decisions
        pass
```

#### 3.3 软约束支持
```python
class SoftConstraintSolver:
    """Support soft constraints with weights"""
    
    def add_soft_constraint(self, expr: z3.BoolRef, weight: int):
        # Use Z3's optimization features
        # Maximize satisfied soft constraints
        # Respect hard constraints always
        pass
```

### Phase 4: 输出和报告（第4周）

#### 4.1 多格式输出
```python
class OutputFormatter:
    """Format tests for different targets"""
    
    def format_json(self, tests: List[TestCase]) -> str:
        # Standard JSON format
        pass
    
    def format_junit(self, tests: List[TestCase]) -> str:
        # JUnit XML format
        pass
    
    def format_csv(self, tests: List[TestCase]) -> str:
        # CSV for spreadsheets
        pass
    
    def format_code(self, tests: List[TestCase], language: str) -> str:
        # Generate actual test code
        pass
```

#### 4.2 覆盖报告
```python
class CoverageReporter:
    """Generate detailed coverage reports"""
    
    def generate_report(self, tests: List[TestCase], model: DSLModel) -> Report:
        # 1. Overall coverage statistics
        # 2. Detailed coverage matrix
        # 3. Uncovered items
        # 4. Redundancy analysis
        # 5. Recommendations
        pass
```

#### 4.3 可视化
```python
class TestVisualizer:
    """Visualize test coverage and relationships"""
    
    def create_coverage_heatmap(self, tests: List[TestCase], model: DSLModel) -> Image:
        # Visual coverage matrix
        pass
    
    def create_dependency_graph(self, model: DSLModel) -> Graph:
        # Show constraint and rule relationships
        pass
```

### Phase 5: CLI和API（第5周）

#### 5.1 命令行界面
```python
# dsl2test.py --input model.yaml --output tests.json --format json --minimize --coverage-goal 0.95
```

#### 5.2 Python API
```python
from dsl_test_gen import TestGenerator, DSLModel

model = DSLModel.from_file("model.yaml")
generator = TestGenerator(
    minimize=True,
    coverage_goal=0.95,
    max_tests=50
)
tests = generator.generate(model)
```

#### 5.3 REST API
```python
# POST /api/generate
# Body: { "dsl": "...", "options": {...} }
# Response: { "tests": [...], "coverage": {...} }
```

## 质量保证

### 测试策略
1. **单元测试**：每个组件100%覆盖
2. **集成测试**：端到端场景
3. **性能测试**：大规模DSL
4. **正确性测试**：验证生成的测试总是满足约束

### 文档
1. **API文档**：完整的接口说明
2. **用户指南**：如何编写DSL和使用工具
3. **架构文档**：设计决策和扩展指南
4. **示例库**：各种领域的DSL示例

## 成功指标

1. **正确性**：100%生成的测试满足所有约束
2. **最小性**：比V1.0减少60%以上的测试
3. **性能**：中等DSL（50个属性）在5秒内完成
4. **可用性**：清晰的错误信息，易于调试
5. **可扩展**：添加新功能不需要修改核心

## 时间线

- **Week 1**: 基础框架完成
- **Week 2**: 测试策略引擎完成
- **Week 3**: 约束求解优化完成
- **Week 4**: 输出和报告完成
- **Week 5**: CLI/API和文档完成
- **Week 6**: 测试、优化和发布

## 风险和缓解

1. **Z3性能问题**
   - 缓解：增量求解，缓存，并行化

2. **复杂表达式解析**
   - 缓解：使用成熟的解析库，提供清晰错误信息

3. **最小化NP完全问题**
   - 缓解：使用启发式算法，可配置的超时

4. **向后兼容性**
   - 缓解：提供迁移工具，保留V1 API子集