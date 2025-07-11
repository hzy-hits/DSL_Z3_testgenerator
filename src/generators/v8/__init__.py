"""
V8 Test Generator - Modular Architecture
统一的模块化测试生成器
"""

from .core import TestGenerator
from .parser import YAMLParser
from .value_generator import ValueGenerator
from .constraint_handler import ConstraintHandler
from .test_strategies import (
    FunctionalTestStrategy,
    BoundaryTestStrategy,
    NegativeTestStrategy,
    ConstraintTestStrategy
)

__version__ = '8.0.0'
__all__ = [
    'TestGenerator',
    'YAMLParser',
    'ValueGenerator',
    'ConstraintHandler',
    'FunctionalTestStrategy',
    'BoundaryTestStrategy',
    'NegativeTestStrategy',
    'ConstraintTestStrategy'
]