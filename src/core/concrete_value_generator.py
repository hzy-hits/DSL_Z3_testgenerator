"""
Concrete Value Generator using Z3 SMT Solver
Generates specific, executable test data values
"""

import z3
import random
from typing import Dict, List, Any, Optional, Tuple
from dataclasses import dataclass
from src.models.dsl_models import DSLType, Attribute, Entity, Rule, Constraint, Model


@dataclass
class ConcreteValue:
    """A concrete value with its generation rationale"""
    value: Any
    rationale: str
    constraints_satisfied: List[str]


class ConcreteValueGenerator:
    """Generates concrete test data values using Z3"""
    
    def __init__(self):
        self.solver = z3.Solver()
        self.variables = {}
        self.id_counter = 100  # Starting ID for generated entities
        
    def generate_entity_values(self, entity: Entity, rules: List[Rule], 
                             constraints: List[Constraint], 
                             scenario: str = "default") -> Dict[str, ConcreteValue]:
        """Generate concrete values for all entity attributes"""
        values = {}
        entity_name = entity.name.lower()
        
        # Create Z3 variables for each attribute
        self._create_z3_variables(entity)
        
        # Apply constraints
        self._apply_constraints(entity, constraints)
        
        # Apply scenario-specific constraints
        self._apply_scenario_constraints(entity, rules, scenario)
        
        # Solve and extract values
        if self.solver.check() == z3.sat:
            model = self.solver.model()
            
            for attr in entity.attributes:
                var_name = f"{entity_name}_{attr.name}"
                concrete_value = self._extract_concrete_value(attr, var_name, model, scenario)
                values[attr.name] = concrete_value
        else:
            # If no solution, generate default valid values
            for attr in entity.attributes:
                values[attr.name] = self._generate_default_value(attr, scenario)
        
        self.solver.reset()  # Reset for next entity
        return values
    
    def _create_z3_variables(self, entity: Entity):
        """Create Z3 variables for entity attributes"""
        entity_name = entity.name.lower()
        
        for attr in entity.attributes:
            var_name = f"{entity_name}_{attr.name}"
            
            if attr.type == DSLType.INTEGER:
                self.variables[var_name] = z3.Int(var_name)
                
                # Apply min/max constraints
                if attr.min_value is not None:
                    self.solver.add(self.variables[var_name] >= attr.min_value)
                if attr.max_value is not None:
                    self.solver.add(self.variables[var_name] <= attr.max_value)
                    
            elif attr.type == DSLType.BOOLEAN:
                self.variables[var_name] = z3.Bool(var_name)
                
            elif attr.type == DSLType.STRING:
                # For strings, we'll handle them separately
                pass
                
            elif attr.type in [DSLType.ARRAY, DSLType.SET]:
                # For collections, create size variable
                size_var = f"{var_name}_size"
                self.variables[size_var] = z3.Int(size_var)
                self.solver.add(self.variables[size_var] >= 0)
                
                if attr.collection_info:
                    if attr.collection_info.min_size is not None:
                        self.solver.add(self.variables[size_var] >= attr.collection_info.min_size)
                    if attr.collection_info.max_size is not None:
                        self.solver.add(self.variables[size_var] <= attr.collection_info.max_size)
    
    def _apply_constraints(self, entity: Entity, constraints: List[Constraint]):
        """Apply DSL constraints to Z3 solver"""
        entity_name = entity.name.lower()
        
        for constraint in constraints:
            try:
                # Parse constraint expression
                expr = constraint.expression.lower()
                
                # Handle size constraints
                if "size" in expr and ">=" in expr:
                    parts = expr.split(">=")
                    if len(parts) == 2:
                        attr_ref = parts[0].strip()
                        min_size = int(parts[1].strip())
                        
                        # Find matching attribute
                        for attr in entity.attributes:
                            if attr.name in attr_ref:
                                size_var = f"{entity_name}_{attr.name}_size"
                                if size_var in self.variables:
                                    self.solver.add(self.variables[size_var] >= min_size)
                                    
            except Exception as e:
                # Skip constraints that can't be parsed
                pass
    
    def _apply_scenario_constraints(self, entity: Entity, rules: List[Rule], scenario: str):
        """Apply scenario-specific constraints based on rules"""
        entity_name = entity.name.lower()
        
        # Map scenarios to specific constraint patterns
        if scenario == "admin_user":
            # Ensure user has admin privileges
            if "is_admin" in self.variables:
                self.solver.add(self.variables["is_admin"] == True)
            if f"{entity_name}_roles_size" in self.variables:
                self.solver.add(self.variables[f"{entity_name}_roles_size"] >= 1)
                
        elif scenario == "bulk_discount":
            # Ensure cart has enough items
            if f"{entity_name}_items_size" in self.variables:
                self.solver.add(self.variables[f"{entity_name}_items_size"] >= 10)
                
        elif scenario == "inactive_user":
            # Ensure user is inactive
            if f"{entity_name}_is_active" in self.variables:
                self.solver.add(self.variables[f"{entity_name}_is_active"] == False)
    
    def _extract_concrete_value(self, attr: Attribute, var_name: str, 
                               model: z3.ModelRef, scenario: str) -> ConcreteValue:
        """Extract concrete value from Z3 model"""
        
        if attr.type == DSLType.INTEGER:
            if var_name in self.variables:
                z3_value = model.eval(self.variables[var_name])
                value = z3_value.as_long() if hasattr(z3_value, 'as_long') else int(str(z3_value))
                rationale = f"Generated integer value {value} for {attr.name}"
                
                constraints = []
                if attr.min_value is not None and value == attr.min_value:
                    constraints.append(f"min_value={attr.min_value}")
                    rationale += f" (at minimum boundary)"
                elif attr.max_value is not None and value == attr.max_value:
                    constraints.append(f"max_value={attr.max_value}")
                    rationale += f" (at maximum boundary)"
                    
                return ConcreteValue(value, rationale, constraints)
            else:
                return self._generate_default_value(attr, scenario)
                
        elif attr.type == DSLType.BOOLEAN:
            if var_name in self.variables:
                z3_value = model.eval(self.variables[var_name])
                # Convert Z3 boolean to Python boolean
                value = z3.is_true(z3_value)
                rationale = f"Set {attr.name} to {value} for scenario '{scenario}'"
                return ConcreteValue(value, rationale, [])
            else:
                return self._generate_default_value(attr, scenario)
                
        elif attr.type == DSLType.STRING:
            # Generate contextual string values
            value = self._generate_string_value(attr, scenario)
            rationale = f"Generated string value for {attr.name} in {scenario} scenario"
            return ConcreteValue(value, rationale, [])
            
        elif attr.type in [DSLType.ARRAY, DSLType.SET]:
            # Generate collection with concrete elements
            size_var = f"{var_name}_size"
            if size_var in self.variables:
                z3_size = model.eval(self.variables[size_var])
                size = z3_size.as_long() if hasattr(z3_size, 'as_long') else int(str(z3_size))
            else:
                size = 3  # Default size
                
            elements = self._generate_collection_elements(attr, size, scenario)
            rationale = f"Generated {attr.type.value} with {size} elements for {scenario}"
            constraints = [f"size={size}"]
            
            if attr.collection_info:
                if attr.collection_info.min_size and size == attr.collection_info.min_size:
                    constraints.append(f"at_min_size={attr.collection_info.min_size}")
                    
            return ConcreteValue(elements, rationale, constraints)
        
        return self._generate_default_value(attr, scenario)
    
    def _generate_string_value(self, attr: Attribute, scenario: str) -> str:
        """Generate contextual string values"""
        name = attr.name.lower()
        
        # Context-aware string generation
        if "email" in name:
            return f"test_{scenario}@example.com"
        elif "name" in name:
            return f"Test_{scenario.title()}_Name"
        elif "code" in name and "discount" in name:
            if scenario == "premium_discount":
                return "VIP_ONLY_20"
            else:
                return f"DISCOUNT_{scenario.upper()[:10]}"
        elif "id" in name:
            return f"{scenario}_{self.id_counter}"
        else:
            return f"{scenario}_{name}_value"
    
    def _generate_collection_elements(self, attr: Attribute, size: int, scenario: str) -> List[Any]:
        """Generate concrete collection elements"""
        elements = []
        
        if attr.collection_info and attr.collection_info.element_type == DSLType.INTEGER:
            # Generate product IDs for cart items
            if "item" in attr.name.lower() or "product" in attr.name.lower():
                for i in range(size):
                    item = {
                        "id": self.id_counter + i,
                        "price": round(19.99 + (i * 10), 2),
                        "quantity": 1,
                        "name": f"Product_{self.id_counter + i}"
                    }
                    elements.append(item)
                self.id_counter += size
            else:
                # Generate simple integer array
                elements = list(range(self.id_counter, self.id_counter + size))
                self.id_counter += size
                
        elif attr.collection_info and attr.collection_info.element_type == DSLType.STRING:
            # Generate string elements
            if "role" in attr.name.lower():
                if scenario == "admin_user":
                    elements = ["admin", "super_user", "moderator"][:size]
                else:
                    elements = ["user", "viewer", "guest"][:size]
            elif "permission" in attr.name.lower():
                base_perms = ["read", "write", "delete", "create", "update", "admin"]
                elements = base_perms[:size]
            elif "code" in attr.name.lower():
                elements = [f"CODE_{i:03d}" for i in range(size)]
            else:
                elements = [f"{attr.name}_{i}" for i in range(size)]
        else:
            # Generic elements
            elements = [f"element_{i}" for i in range(size)]
            
        return elements
    
    def _generate_default_value(self, attr: Attribute, scenario: str) -> ConcreteValue:
        """Generate default valid value for attribute"""
        if attr.optional and scenario != "all_fields":
            # Skip optional fields in most scenarios
            return ConcreteValue(None, f"Optional field {attr.name} omitted", ["optional=true"])
            
        if attr.type == DSLType.INTEGER:
            if attr.default_value is not None:
                value = attr.default_value
            elif attr.min_value is not None:
                value = attr.min_value + 1
            else:
                value = 100
            return ConcreteValue(value, f"Default integer value for {attr.name}", [])
            
        elif attr.type == DSLType.BOOLEAN:
            value = attr.default_value if attr.default_value is not None else True
            return ConcreteValue(value, f"Default boolean value for {attr.name}", [])
            
        elif attr.type == DSLType.STRING:
            value = self._generate_string_value(attr, scenario)
            return ConcreteValue(value, f"Default string value for {attr.name}", [])
            
        elif attr.type in [DSLType.ARRAY, DSLType.SET]:
            size = 3  # Default size
            elements = self._generate_collection_elements(attr, size, scenario)
            return ConcreteValue(elements, f"Default {attr.type.value} for {attr.name}", [])
            
        return ConcreteValue(None, f"No value generated for {attr.name}", [])
    
    def generate_combination_values(self, entity: Entity, combination: Dict[str, Any],
                                  rules: List[Rule], constraints: List[Constraint]) -> Dict[str, ConcreteValue]:
        """Generate values for a specific parameter combination"""
        values = {}
        entity_name = entity.name.lower()
        
        # First, apply the combination values as constraints
        self._create_z3_variables(entity)
        
        for attr_name, combo_value in combination.items():
            var_name = f"{entity_name}_{attr_name}"
            if var_name in self.variables:
                if isinstance(combo_value, bool):
                    self.solver.add(self.variables[var_name] == combo_value)
                elif isinstance(combo_value, int):
                    self.solver.add(self.variables[var_name] == combo_value)
        
        # Apply other constraints
        self._apply_constraints(entity, constraints)
        
        # Generate values
        if self.solver.check() == z3.sat:
            model = self.solver.model()
            
            for attr in entity.attributes:
                if attr.name in combination:
                    # Use the combination value
                    value = combination[attr.name]
                    rationale = f"Fixed by combination: {attr.name}={value}"
                    values[attr.name] = ConcreteValue(value, rationale, ["combination_fixed"])
                else:
                    # Generate value that satisfies constraints
                    var_name = f"{entity_name}_{attr.name}"
                    values[attr.name] = self._extract_concrete_value(attr, var_name, model, "combination")
        
        self.solver.reset()
        return values