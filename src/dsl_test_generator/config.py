"""Configuration module for DSL Test Generator.

This module provides centralized configuration to avoid hardcoded values
and allow customization for different domains and use cases.
"""

from dataclasses import dataclass, field
from typing import Dict, List, Optional


@dataclass
class TestGenerationConfig:
    """Configuration for test generation behavior."""
    
    # Test types that can be generated
    test_types: List[str] = field(default_factory=lambda: [
        "boundary", "equivalence", "negative", "collection", "combinatorial"
    ])
    
    # Default collection test scenarios
    collection_test_scenarios: List[str] = field(default_factory=lambda: [
        "empty", "single", "multiple", "boundary"
    ])
    
    # Numeric precision settings
    decimal_precision: int = 6
    negative_test_integer_extension: int = 1
    negative_test_real_extension: float = 1.0
    
    # Collection size limits for constraint checking
    set_domain_check_limit: int = 100
    array_membership_check_limit: int = 10
    string_hash_modulo: int = 1000000
    default_min_collection_size: int = 0
    
    # Naming conventions
    variable_name_pattern: str = "{entity}_{attribute}"
    variable_name_case: str = "lower"  # "lower", "upper", "camel"
    
    # String representation strategy
    string_representation: str = "integer"  # "integer" or "z3string"
    
    # Test generation limits
    max_attempts_per_test: int = 10
    max_test_cases_per_type: int = 100
    
    # Business logic validation
    validate_business_logic: bool = True
    cross_entity_validation: bool = True


@dataclass
class SolverConfig:
    """Configuration for Z3 solver behavior."""
    
    # Solver timeout in milliseconds
    timeout: Optional[int] = 5000
    
    # Random seed for reproducible results
    random_seed: Optional[int] = None
    
    # Solver optimization settings
    enable_optimization: bool = True
    use_simplification: bool = True


@dataclass
class OperatorConfig:
    """Configuration for logical operator mappings."""
    
    logical_operators: Dict[str, str] = field(default_factory=lambda: {
        'and': 'And',
        'or': 'Or',
        'not': 'Not',
        '->': 'Implies',
        'implies': 'Implies',
        '&&': 'And',
        '||': 'Or',
        '!': 'Not',
    })
    
    comparison_operators: Dict[str, str] = field(default_factory=lambda: {
        '==': 'eq',
        '!=': 'ne',
        '<': 'lt',
        '<=': 'le',
        '>': 'gt',
        '>=': 'ge',
    })


@dataclass
class DSLEngineConfig:
    """Main configuration class for DSL Engine."""
    
    test_generation: TestGenerationConfig = field(default_factory=TestGenerationConfig)
    solver: SolverConfig = field(default_factory=SolverConfig)
    operators: OperatorConfig = field(default_factory=OperatorConfig)
    
    @classmethod
    def from_dict(cls, config_dict: Dict) -> 'DSLEngineConfig':
        """Create configuration from dictionary."""
        config = cls()
        
        if 'test_generation' in config_dict:
            test_gen_dict = config_dict['test_generation']
            config.test_generation = TestGenerationConfig(**test_gen_dict)
        
        if 'solver' in config_dict:
            solver_dict = config_dict['solver']
            config.solver = SolverConfig(**solver_dict)
        
        if 'operators' in config_dict:
            operators_dict = config_dict['operators']
            config.operators = OperatorConfig(**operators_dict)
        
        return config
    
    def to_dict(self) -> Dict:
        """Convert configuration to dictionary."""
        return {
            'test_generation': {
                'test_types': self.test_generation.test_types,
                'collection_test_scenarios': self.test_generation.collection_test_scenarios,
                'decimal_precision': self.test_generation.decimal_precision,
                'negative_test_integer_extension': self.test_generation.negative_test_integer_extension,
                'negative_test_real_extension': self.test_generation.negative_test_real_extension,
                'set_domain_check_limit': self.test_generation.set_domain_check_limit,
                'array_membership_check_limit': self.test_generation.array_membership_check_limit,
                'string_hash_modulo': self.test_generation.string_hash_modulo,
                'default_min_collection_size': self.test_generation.default_min_collection_size,
                'variable_name_pattern': self.test_generation.variable_name_pattern,
                'variable_name_case': self.test_generation.variable_name_case,
                'string_representation': self.test_generation.string_representation,
                'max_attempts_per_test': self.test_generation.max_attempts_per_test,
                'max_test_cases_per_type': self.test_generation.max_test_cases_per_type,
                'validate_business_logic': self.test_generation.validate_business_logic,
                'cross_entity_validation': self.test_generation.cross_entity_validation,
            },
            'solver': {
                'timeout': self.solver.timeout,
                'random_seed': self.solver.random_seed,
                'enable_optimization': self.solver.enable_optimization,
                'use_simplification': self.solver.use_simplification,
            },
            'operators': {
                'logical_operators': self.operators.logical_operators,
                'comparison_operators': self.operators.comparison_operators,
            }
        }


# Default configuration instance
default_config = DSLEngineConfig()