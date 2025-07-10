"""
Executable Test Generator
Produces concrete, runnable test cases with actual data values
"""

import json
from typing import Dict, List, Any, Optional, Tuple
from dataclasses import dataclass, asdict
from datetime import datetime

from src.models.dsl_models import Model, Entity, Rule, Constraint, DSLType
from src.core.concrete_value_generator import ConcreteValueGenerator, ConcreteValue
from src.core.combination_engine import CombinationEngine, TestCombination


@dataclass
class ExecutableTestCase:
    """A fully executable test case with concrete data"""
    test_id: str
    name: str
    description: str
    rationale: str  # Why this test was generated
    test_type: str  # functional, boundary, combinatorial, rule, constraint
    
    # Concrete input data
    concrete_input: Dict[str, Any]
    
    # Expected outcomes
    expected_result: str  # success, validation_error, rule_triggered, etc.
    expected_values: Dict[str, Any]  # Expected output values
    
    # Metadata
    coverage_points: List[str]  # What this test covers
    constraints_tested: List[str]  # Which constraints are tested
    rules_triggered: List[str]  # Which rules should fire
    
    # Optional executable code
    executable_code: Optional[str] = None
    
    def to_json(self) -> str:
        """Convert to JSON string"""
        return json.dumps(asdict(self), indent=2, default=str)


class ExecutableTestGenerator:
    """Generates executable test cases from DSL models"""
    
    def __init__(self):
        self.value_generator = ConcreteValueGenerator()
        self.test_counter = 0
        
    def generate_executable_tests(self, model: Model, file_name: str) -> List[ExecutableTestCase]:
        """Generate all executable test cases for a model"""
        tests = []
        
        # Reset counter for each file
        self.test_counter = 0
        
        # Generate tests for each entity
        for entity in model.entities:
            # 1. Basic CRUD tests
            tests.extend(self._generate_crud_tests(entity, model, file_name))
            
            # 2. Boundary value tests
            tests.extend(self._generate_boundary_tests(entity, model, file_name))
            
            # 3. Rule-based tests
            tests.extend(self._generate_rule_tests(entity, model, file_name))
            
            # 4. Constraint tests
            tests.extend(self._generate_constraint_tests(entity, model, file_name))
            
            # 5. Combination tests (if specified)
            if model.test_requirements and model.test_requirements.type == "combinatorial":
                tests.extend(self._generate_combination_tests(entity, model, file_name))
            
            # 6. Scenario-based tests
            tests.extend(self._generate_scenario_tests(entity, model, file_name))
        
        # 7. Integration tests (cross-entity)
        if len(model.entities) > 1:
            tests.extend(self._generate_integration_tests(model, file_name))
        
        return tests
    
    def _generate_crud_tests(self, entity: Entity, model: Model, file_name: str) -> List[ExecutableTestCase]:
        """Generate basic Create, Read, Update, Delete tests"""
        tests = []
        
        # CREATE - Valid entity with all required fields
        self.test_counter += 1
        values = self.value_generator.generate_entity_values(
            entity, model.rules, model.constraints, "create_valid"
        )
        
        concrete_input = self._build_concrete_input(entity, values)
        
        test = ExecutableTestCase(
            test_id=f"{file_name}_{self.test_counter:04d}",
            name=f"Create valid {entity.name}",
            description=f"Test creating a {entity.name} with all required fields",
            rationale="Verify basic entity creation with valid data",
            test_type="functional",
            concrete_input=concrete_input,
            expected_result="success",
            expected_values={"id": "generated", "status": "created"},
            coverage_points=[f"entity:{entity.name}", "operation:create", "valid_data"],
            constraints_tested=[],
            rules_triggered=[],
            executable_code=self._generate_test_code("create", entity.name, concrete_input)
        )
        tests.append(test)
        
        # CREATE - Missing required field
        for attr in entity.get_required_attributes():
            self.test_counter += 1
            incomplete_values = dict(values)
            del incomplete_values[attr.name]
            
            incomplete_input = self._build_concrete_input(entity, incomplete_values)
            
            test = ExecutableTestCase(
                test_id=f"{file_name}_{self.test_counter:04d}",
                name=f"Create {entity.name} missing {attr.name}",
                description=f"Test validation when required field {attr.name} is missing",
                rationale=f"Verify required field validation for {attr.name}",
                test_type="negative",
                concrete_input=incomplete_input,
                expected_result="validation_error",
                expected_values={"error": f"Missing required field: {attr.name}"},
                coverage_points=[f"entity:{entity.name}", "validation:required", f"field:{attr.name}"],
                constraints_tested=[],
                rules_triggered=[],
                executable_code=self._generate_test_code("create", entity.name, incomplete_input)
            )
            tests.append(test)
        
        # UPDATE - Modify existing entity
        self.test_counter += 1
        update_values = self.value_generator.generate_entity_values(
            entity, model.rules, model.constraints, "update"
        )
        
        update_input = {
            "id": 123,
            "updates": self._build_concrete_input(entity, update_values)
        }
        
        test = ExecutableTestCase(
            test_id=f"{file_name}_{self.test_counter:04d}",
            name=f"Update existing {entity.name}",
            description=f"Test updating an existing {entity.name}",
            rationale="Verify entity update functionality",
            test_type="functional",
            concrete_input=update_input,
            expected_result="success",
            expected_values={"status": "updated"},
            coverage_points=[f"entity:{entity.name}", "operation:update"],
            constraints_tested=[],
            rules_triggered=[],
            executable_code=self._generate_test_code("update", entity.name, update_input)
        )
        tests.append(test)
        
        return tests
    
    def _generate_boundary_tests(self, entity: Entity, model: Model, file_name: str) -> List[ExecutableTestCase]:
        """Generate boundary value tests"""
        tests = []
        combination_engine = CombinationEngine(model)
        
        # Get boundary combinations
        boundary_combos = combination_engine.generate_boundary_combinations(entity)
        
        for combo in boundary_combos:
            self.test_counter += 1
            
            # Generate full entity values with boundary constraints
            values = self.value_generator.generate_combination_values(
                entity, combo.values, model.rules, model.constraints
            )
            
            concrete_input = self._build_concrete_input(entity, values)
            
            test = ExecutableTestCase(
                test_id=f"{file_name}_{self.test_counter:04d}",
                name=f"Boundary test: {combo.rationale[:50]}",
                description=f"Boundary value test for {entity.name}",
                rationale=combo.rationale,
                test_type="boundary",
                concrete_input=concrete_input,
                expected_result="success",
                expected_values={},
                coverage_points=[f"entity:{entity.name}", "boundary_test"] + 
                               [f"boundary:{k}={v}" for k, v in combo.values.items()],
                constraints_tested=self._extract_relevant_constraints(combo.values, model.constraints),
                rules_triggered=[],
                executable_code=self._generate_test_code("create", entity.name, concrete_input)
            )
            tests.append(test)
        
        return tests
    
    def _generate_rule_tests(self, entity: Entity, model: Model, file_name: str) -> List[ExecutableTestCase]:
        """Generate tests for business rules"""
        tests = []
        
        for rule in model.rules:
            # Test rule activation
            self.test_counter += 1
            
            # Generate values that satisfy the rule condition
            values = self.value_generator.generate_entity_values(
                entity, model.rules, model.constraints, f"rule_{rule.name}"
            )
            
            # Ensure rule condition is met
            concrete_input = self._build_concrete_input_for_rule(entity, values, rule, True)
            
            test = ExecutableTestCase(
                test_id=f"{file_name}_{self.test_counter:04d}",
                name=f"Rule '{rule.name}' activation",
                description=f"Test that rule '{rule.name}' fires when condition is met",
                rationale=f"Verify business rule: {rule.condition}",
                test_type="rule",
                concrete_input=concrete_input,
                expected_result="rule_triggered",
                expected_values=self._get_expected_rule_outcome(rule),
                coverage_points=[f"entity:{entity.name}", f"rule:{rule.name}", "rule_activation"],
                constraints_tested=[],
                rules_triggered=[rule.name],
                executable_code=self._generate_test_code("process", entity.name, concrete_input)
            )
            tests.append(test)
            
            # Test rule non-activation
            self.test_counter += 1
            
            # Generate values that violate the rule condition
            neg_concrete_input = self._build_concrete_input_for_rule(entity, values, rule, False)
            
            test = ExecutableTestCase(
                test_id=f"{file_name}_{self.test_counter:04d}",
                name=f"Rule '{rule.name}' non-activation",
                description=f"Test that rule '{rule.name}' does not fire when condition is not met",
                rationale=f"Verify rule does not fire incorrectly",
                test_type="rule",
                concrete_input=neg_concrete_input,
                expected_result="rule_not_triggered",
                expected_values={},
                coverage_points=[f"entity:{entity.name}", f"rule:{rule.name}", "rule_non_activation"],
                constraints_tested=[],
                rules_triggered=[],
                executable_code=self._generate_test_code("process", entity.name, neg_concrete_input)
            )
            tests.append(test)
        
        return tests
    
    def _generate_constraint_tests(self, entity: Entity, model: Model, file_name: str) -> List[ExecutableTestCase]:
        """Generate tests for constraints"""
        tests = []
        
        for constraint in model.constraints:
            # Test constraint satisfaction
            self.test_counter += 1
            
            values = self.value_generator.generate_entity_values(
                entity, model.rules, model.constraints, "constraint_satisfy"
            )
            
            concrete_input = self._build_concrete_input(entity, values)
            
            test = ExecutableTestCase(
                test_id=f"{file_name}_{self.test_counter:04d}",
                name=f"Constraint satisfaction: {constraint.expression[:40]}",
                description=f"Test that data satisfies constraint",
                rationale=f"Verify constraint: {constraint.expression}",
                test_type="constraint",
                concrete_input=concrete_input,
                expected_result="success",
                expected_values={},
                coverage_points=[f"entity:{entity.name}", f"constraint:{constraint.get_type()}"],
                constraints_tested=[constraint.expression],
                rules_triggered=[],
                executable_code=self._generate_test_code("validate", entity.name, concrete_input)
            )
            tests.append(test)
            
            # Test constraint violation (if possible)
            if self._can_violate_constraint(constraint):
                self.test_counter += 1
                
                violation_input = self._build_constraint_violation(entity, constraint)
                
                test = ExecutableTestCase(
                    test_id=f"{file_name}_{self.test_counter:04d}",
                    name=f"Constraint violation: {constraint.expression[:40]}",
                    description=f"Test that constraint violation is detected",
                    rationale=f"Verify constraint enforcement",
                    test_type="negative",
                    concrete_input=violation_input,
                    expected_result="validation_error",
                    expected_values={"error": f"Constraint violation: {constraint.expression}"},
                    coverage_points=[f"entity:{entity.name}", f"constraint:{constraint.get_type()}", "violation"],
                    constraints_tested=[constraint.expression],
                    rules_triggered=[],
                    executable_code=self._generate_test_code("validate", entity.name, violation_input)
                )
                tests.append(test)
        
        return tests
    
    def _generate_combination_tests(self, entity: Entity, model: Model, file_name: str) -> List[ExecutableTestCase]:
        """Generate combinatorial tests based on test requirements"""
        tests = []
        combination_engine = CombinationEngine(model)
        
        # Generate combinations based on coverage level
        coverage_level = model.test_requirements.coverage_level if model.test_requirements else "pairwise"
        combinations = combination_engine.generate_combinations(entity, "combinatorial", coverage_level)
        
        for combo in combinations:
            self.test_counter += 1
            
            # Generate full entity values with combination constraints
            values = self.value_generator.generate_combination_values(
                entity, combo.values, model.rules, model.constraints
            )
            
            concrete_input = self._build_concrete_input(entity, values)
            
            # Determine expected result based on combination
            expected_result, expected_values = self._analyze_combination_outcome(
                combo.values, model.rules, model.constraints
            )
            
            test = ExecutableTestCase(
                test_id=f"{file_name}_{self.test_counter:04d}",
                name=f"Combination test: {', '.join(f'{k}={v}' for k, v in combo.values.items())}",
                description=f"{combo.coverage_type} combination test for {entity.name}",
                rationale=combo.rationale,
                test_type="combinatorial",
                concrete_input=concrete_input,
                expected_result=expected_result,
                expected_values=expected_values,
                coverage_points=[f"entity:{entity.name}", f"combination:{combo.coverage_type}"] + 
                               [f"param:{k}={v}" for k, v in combo.values.items()],
                constraints_tested=self._extract_relevant_constraints(combo.values, model.constraints),
                rules_triggered=self._extract_triggered_rules(combo.values, model.rules),
                executable_code=self._generate_test_code("process", entity.name, concrete_input)
            )
            tests.append(test)
        
        return tests
    
    def _generate_scenario_tests(self, entity: Entity, model: Model, file_name: str) -> List[ExecutableTestCase]:
        """Generate scenario-based tests"""
        tests = []
        
        # Determine domain-specific scenarios
        domain = model.domain.lower()
        scenarios = []
        
        if "cart" in domain or "shopping" in domain:
            scenarios = [
                ("empty_cart", "Empty shopping cart"),
                ("single_item", "Cart with single item"),
                ("bulk_purchase", "Cart with bulk discount threshold"),
                ("premium_member_discount", "Premium member with discounts")
            ]
        elif "user" in domain or "account" in domain:
            scenarios = [
                ("new_user", "Newly registered user"),
                ("active_user", "Active user with permissions"),
                ("suspended_user", "Suspended user account"),
                ("admin_user", "Administrator with full permissions")
            ]
        elif "order" in domain:
            scenarios = [
                ("pending_order", "Order in pending state"),
                ("processing_order", "Order being processed"),
                ("completed_order", "Successfully completed order"),
                ("cancelled_order", "Cancelled order")
            ]
        else:
            # Generic scenarios
            scenarios = [
                ("typical_case", "Typical usage scenario"),
                ("edge_case", "Edge case scenario"),
                ("error_case", "Error handling scenario")
            ]
        
        for scenario_key, scenario_desc in scenarios[:3]:  # Limit to 3 scenarios
            self.test_counter += 1
            
            values = self.value_generator.generate_entity_values(
                entity, model.rules, model.constraints, scenario_key
            )
            
            concrete_input = self._build_concrete_input(entity, values)
            
            test = ExecutableTestCase(
                test_id=f"{file_name}_{self.test_counter:04d}",
                name=f"Scenario: {scenario_desc}",
                description=f"Test {scenario_desc} for {entity.name}",
                rationale=f"Verify system behavior in {scenario_desc} scenario",
                test_type="scenario",
                concrete_input=concrete_input,
                expected_result="success",
                expected_values=self._get_scenario_expected_values(scenario_key),
                coverage_points=[f"entity:{entity.name}", f"scenario:{scenario_key}"],
                constraints_tested=[],
                rules_triggered=self._get_scenario_rules(scenario_key, model.rules),
                executable_code=self._generate_test_code("scenario", entity.name, concrete_input)
            )
            tests.append(test)
        
        return tests
    
    def _generate_integration_tests(self, model: Model, file_name: str) -> List[ExecutableTestCase]:
        """Generate cross-entity integration tests"""
        tests = []
        
        if len(model.entities) >= 2:
            self.test_counter += 1
            
            # Generate values for multiple entities
            integration_data = {}
            for entity in model.entities[:2]:  # Test first two entities
                values = self.value_generator.generate_entity_values(
                    entity, model.rules, model.constraints, "integration"
                )
                entity_data = self._build_concrete_input(entity, values)
                integration_data[entity.name.lower()] = entity_data
            
            test = ExecutableTestCase(
                test_id=f"{file_name}_{self.test_counter:04d}",
                name="Cross-entity data consistency",
                description="Test data consistency across multiple entities",
                rationale="Verify relationships and data integrity between entities",
                test_type="integration",
                concrete_input=integration_data,
                expected_result="success",
                expected_values={"consistency": "maintained"},
                coverage_points=["integration:cross_entity"] + 
                               [f"entity:{e.name}" for e in model.entities[:2]],
                constraints_tested=[],
                rules_triggered=[],
                executable_code=self._generate_integration_test_code(model.entities[:2], integration_data)
            )
            tests.append(test)
        
        return tests
    
    def _build_concrete_input(self, entity: Entity, values: Dict[str, ConcreteValue]) -> Dict[str, Any]:
        """Build concrete input data from generated values"""
        concrete_data = {}
        
        for attr_name, concrete_value in values.items():
            if concrete_value.value is not None:  # Skip None values (optional fields)
                concrete_data[attr_name] = concrete_value.value
        
        return concrete_data
    
    def _build_concrete_input_for_rule(self, entity: Entity, values: Dict[str, ConcreteValue], 
                                      rule: Rule, satisfy: bool) -> Dict[str, Any]:
        """Build input that satisfies or violates a rule"""
        concrete_data = self._build_concrete_input(entity, values)
        
        # Analyze rule condition
        condition = rule.condition.lower()
        
        if satisfy:
            # Ensure condition is met
            if "admin" in condition and "roles" in concrete_data:
                concrete_data["roles"] = ["admin", "super_user"]
            elif "active" in condition and "is_active" in concrete_data:
                concrete_data["is_active"] = True
            elif "size" in condition and ">=" in condition:
                # Extract size requirement
                for key in concrete_data:
                    if "items" in key and isinstance(concrete_data[key], list):
                        # Ensure we have enough items
                        if len(concrete_data[key]) < 10:
                            # Add more items
                            for i in range(10 - len(concrete_data[key])):
                                concrete_data[key].append({
                                    "id": 200 + i,
                                    "price": 29.99,
                                    "quantity": 1
                                })
        else:
            # Ensure condition is NOT met
            if "admin" in condition and "roles" in concrete_data:
                concrete_data["roles"] = ["user"]
            elif "active" in condition and "is_active" in concrete_data:
                concrete_data["is_active"] = False
            elif "size" in condition and ">=" in condition:
                # Ensure we have fewer items
                for key in concrete_data:
                    if "items" in key and isinstance(concrete_data[key], list):
                        concrete_data[key] = concrete_data[key][:2]  # Keep only 2 items
        
        return concrete_data
    
    def _get_expected_rule_outcome(self, rule: Rule) -> Dict[str, Any]:
        """Determine expected outcome when rule fires"""
        outcome = {}
        
        if rule.action:
            # Parse action to determine outcome
            action = rule.action.lower()
            if "discount" in action:
                outcome["discount_applied"] = True
                outcome["discount_type"] = "rule_based"
            elif "permission" in action:
                outcome["permission_granted"] = True
            elif "status" in action:
                outcome["status_changed"] = True
        
        if rule.implies:
            outcome["implication_applied"] = True
            
        return outcome
    
    def _can_violate_constraint(self, constraint: Constraint) -> bool:
        """Check if we can generate a violation for this constraint"""
        expr = constraint.expression
        
        # Can violate size constraints
        if "size" in expr and any(op in expr for op in [">=", "<=", ">", "<"]):
            return True
        
        # Can violate simple comparisons
        if any(op in expr for op in [">=", "<=", ">", "<", "=="]):
            return True
        
        # Cannot easily violate implications
        if "->" in expr:
            return False
        
        return False
    
    def _build_constraint_violation(self, entity: Entity, constraint: Constraint) -> Dict[str, Any]:
        """Build input that violates a constraint"""
        violation_data = {}
        expr = constraint.expression.lower()
        
        # Violate size constraints
        if "size >= " in expr:
            # Extract the field and minimum size
            for attr in entity.attributes:
                if attr.name in expr:
                    violation_data[attr.name] = []  # Empty collection
                    break
        
        # Add other required fields with valid values
        for attr in entity.get_required_attributes():
            if attr.name not in violation_data:
                if attr.type == DSLType.INTEGER:
                    violation_data[attr.name] = 1
                elif attr.type == DSLType.BOOLEAN:
                    violation_data[attr.name] = False
                elif attr.type == DSLType.STRING:
                    violation_data[attr.name] = "test"
        
        return violation_data
    
    def _extract_relevant_constraints(self, values: Dict[str, Any], 
                                    constraints: List[Constraint]) -> List[str]:
        """Extract constraints relevant to the given values"""
        relevant = []
        
        for constraint in constraints:
            expr = constraint.expression.lower()
            # Check if any of the value keys appear in the constraint
            for key in values:
                if key.lower() in expr:
                    relevant.append(constraint.expression)
                    break
        
        return relevant
    
    def _extract_triggered_rules(self, values: Dict[str, Any], rules: List[Rule]) -> List[str]:
        """Determine which rules would be triggered by the values"""
        triggered = []
        
        for rule in rules:
            condition = rule.condition.lower()
            
            # Simple check - can be enhanced
            will_trigger = True
            
            if "is_premium_member" in values and "premium" in condition:
                if not values["is_premium_member"]:
                    will_trigger = False
            
            if "is_active" in values and "active" in condition:
                if not values["is_active"]:
                    will_trigger = False
            
            if will_trigger and any(key in condition for key in values):
                triggered.append(rule.name)
        
        return triggered
    
    def _analyze_combination_outcome(self, combo_values: Dict[str, Any], 
                                   rules: List[Rule], 
                                   constraints: List[Constraint]) -> Tuple[str, Dict[str, Any]]:
        """Analyze expected outcome for a parameter combination"""
        # Check for invalid combinations
        if "is_premium_member" in combo_values and "discount_codes_size" in combo_values:
            if not combo_values.get("is_premium_member", False) and combo_values.get("discount_codes_size", 0) > 0:
                # Non-premium member with VIP codes
                return "validation_error", {"error": "VIP codes require premium membership"}
        
        # Check which rules would trigger
        triggered_rules = self._extract_triggered_rules(combo_values, rules)
        
        if triggered_rules:
            return "rule_triggered", {"triggered_rules": triggered_rules}
        else:
            return "success", {}
    
    def _get_scenario_expected_values(self, scenario: str) -> Dict[str, Any]:
        """Get expected values for a scenario"""
        expected = {}
        
        if scenario == "empty_cart":
            expected["total"] = 0
            expected["item_count"] = 0
        elif scenario == "bulk_purchase":
            expected["discount_applied"] = True
            expected["discount_type"] = "bulk"
        elif scenario == "admin_user":
            expected["permission_level"] = "full"
            expected["can_modify_system"] = True
        elif scenario == "suspended_user":
            expected["access_allowed"] = False
            expected["reason"] = "account_suspended"
        
        return expected
    
    def _get_scenario_rules(self, scenario: str, rules: List[Rule]) -> List[str]:
        """Get rules that should trigger in a scenario"""
        triggered = []
        
        for rule in rules:
            condition = rule.condition.lower()
            
            if scenario == "bulk_purchase" and "size" in condition and ">=" in condition:
                triggered.append(rule.name)
            elif scenario == "admin_user" and "admin" in condition:
                triggered.append(rule.name)
            elif scenario == "suspended_user" and "active" in condition and "false" in condition:
                triggered.append(rule.name)
        
        return triggered
    
    def _generate_test_code(self, operation: str, entity_name: str, data: Dict[str, Any]) -> str:
        """Generate executable test code (example for Python)"""
        code = f"""
def test_{operation}_{entity_name.lower()}():
    # Arrange
    data = {json.dumps(data, indent=8)}
    
    # Act
    result = api.{operation}_{entity_name.lower()}(data)
    
    # Assert
    assert result.status == "success"
    # Add more assertions based on expected values
"""
        return code.strip()
    
    def _generate_integration_test_code(self, entities: List[Entity], data: Dict[str, Any]) -> str:
        """Generate integration test code"""
        entity_names = [e.name for e in entities]
        code = f"""
def test_integration_{('_'.join(entity_names)).lower()}():
    # Test cross-entity data consistency
    data = {json.dumps(data, indent=8)}
    
    # Create entities
    for entity_name, entity_data in data.items():
        api.create(entity_name, entity_data)
    
    # Verify relationships
    # Add relationship verification logic
"""
        return code.strip()