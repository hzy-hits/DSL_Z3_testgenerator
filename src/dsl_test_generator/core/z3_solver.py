"""Enhanced Z3 solver with collection support."""

from typing import Any, Dict, List, Optional, Union, Set as PySet
import z3

from ..types import DSLModel, DSLType, Attribute, ArrayType, SetType
from ..config import DSLEngineConfig, default_config


class Z3Solver:
    """Z3 SMT solver wrapper with collection support."""
    
    def __init__(self, config: Optional[DSLEngineConfig] = None):
        self.config = config or default_config
        self.solver = z3.Solver()
        if self.config.solver.timeout:
            self.solver.set(timeout=self.config.solver.timeout)
        if self.config.solver.random_seed is not None:
            z3.set_param('smt.random_seed', self.config.solver.random_seed)
        
        self.variables: Dict[str, Any] = {}
        self.array_vars: Dict[str, z3.ArrayRef] = {}
        self.set_vars: Dict[str, z3.ArrayRef] = {}
    
    def create_variables(self, model: DSLModel):
        """Create Z3 variables including arrays and sets."""
        for entity in model.entities:
            for attr in entity.attributes:
                var_name = f"{entity.name.lower()}_{attr.name}"
                
                if attr.type == DSLType.INTEGER:
                    self.variables[var_name] = z3.Int(var_name)
                elif attr.type == DSLType.REAL:
                    self.variables[var_name] = z3.Real(var_name)
                elif attr.type == DSLType.BOOLEAN:
                    self.variables[var_name] = z3.Bool(var_name)
                elif attr.type == DSLType.STRING:
                    # Z3 strings are more complex, using int encoding for now
                    self.variables[var_name] = z3.Int(var_name)
                elif attr.type == DSLType.ARRAY:
                    self._create_array_variable(var_name, attr)
                elif attr.type == DSLType.SET:
                    self._create_set_variable(var_name, attr)
    
    def _create_array_variable(self, var_name: str, attr: Attribute):
        """Create Z3 array variable."""
        if not attr.collection_info:
            return
        
        array_info = attr.collection_info
        element_type = array_info.element_type
        
        # Create array with size variable
        size_var = z3.Int(f"{var_name}_size")
        self.variables[f"{var_name}_size"] = size_var
        
        # Add size constraints
        if array_info.min_size is not None:
            self.solver.add(size_var >= array_info.min_size)
        else:
            self.solver.add(size_var >= 0)
        
        if array_info.max_size is not None:
            self.solver.add(size_var <= array_info.max_size)
        
        # Create array based on element type
        if element_type == DSLType.INTEGER:
            array = z3.Array(var_name, z3.IntSort(), z3.IntSort())
        elif element_type == DSLType.REAL:
            array = z3.Array(var_name, z3.IntSort(), z3.RealSort())
        elif element_type == DSLType.BOOLEAN:
            array = z3.Array(var_name, z3.IntSort(), z3.BoolSort())
        else:
            # Default to integer array
            array = z3.Array(var_name, z3.IntSort(), z3.IntSort())
        
        self.array_vars[var_name] = array
    
    def _create_set_variable(self, var_name: str, attr: Attribute):
        """Create Z3 set variable (represented as array of booleans)."""
        if not attr.collection_info:
            return
        
        set_info = attr.collection_info
        element_type = set_info.element_type
        
        # Create size variable
        size_var = z3.Int(f"{var_name}_size")
        self.variables[f"{var_name}_size"] = size_var
        
        # Add size constraints
        if set_info.min_size is not None:
            self.solver.add(size_var >= set_info.min_size)
        else:
            self.solver.add(size_var >= 0)
        
        if set_info.max_size is not None:
            self.solver.add(size_var <= set_info.max_size)
        
        # Sets are represented as characteristic functions
        if element_type == DSLType.INTEGER:
            set_array = z3.Array(var_name, z3.IntSort(), z3.BoolSort())
        else:
            # For simplicity, use integer domain for now
            set_array = z3.Array(var_name, z3.IntSort(), z3.BoolSort())
        
        self.set_vars[var_name] = set_array
    
    def add_constraint(self, constraint_expr: Any):
        """Add constraint to solver."""
        self.solver.add(constraint_expr)
    
    def check(self) -> bool:
        """Check if constraints are satisfiable."""
        return self.solver.check() == z3.sat
    
    def get_model(self) -> Optional[z3.ModelRef]:
        """Get Z3 model if satisfiable."""
        if self.check():
            return self.solver.model()
        return None
    
    def push(self):
        """Push solver state."""
        self.solver.push()
    
    def pop(self):
        """Pop solver state."""
        self.solver.pop()
    
    def reset(self):
        """Reset solver."""
        self.solver.reset()
        self.variables.clear()
        self.array_vars.clear()
        self.set_vars.clear()
    
    def extract_values(self, model: z3.ModelRef) -> Dict[str, Any]:
        """Extract values from Z3 model including collections."""
        values = {}
        
        # Extract scalar values
        for var_name, var in self.variables.items():
            try:
                if z3.is_int(var):
                    values[var_name] = model[var].as_long()
                elif z3.is_real(var):
                    values[var_name] = float(model[var].as_decimal(self.config.test_generation.decimal_precision))
                elif z3.is_bool(var):
                    values[var_name] = bool(model[var])
                else:
                    values[var_name] = str(model[var])
            except:
                values[var_name] = None
        
        # Extract array values
        for var_name, array in self.array_vars.items():
            size_var_name = f"{var_name}_size"
            if size_var_name in values:
                size = values[size_var_name]
                array_values = []
                
                for i in range(size):
                    try:
                        elem = model.eval(array[i])
                        if z3.is_int_value(elem):
                            array_values.append(elem.as_long())
                        elif z3.is_rational_value(elem):
                            array_values.append(float(elem.as_decimal(self.config.test_generation.decimal_precision)))
                        elif z3.is_bool(elem):
                            array_values.append(bool(elem))
                        else:
                            array_values.append(str(elem))
                    except:
                        array_values.append(None)
                
                values[var_name] = array_values
        
        # Extract set values
        for var_name, set_array in self.set_vars.items():
            set_values = set()
            # For demonstration, check first 100 integers
            for i in range(self.config.test_generation.set_domain_check_limit):
                try:
                    if model.eval(set_array[i]):
                        set_values.add(i)
                except:
                    pass
            
            values[var_name] = list(set_values)
        
        return values