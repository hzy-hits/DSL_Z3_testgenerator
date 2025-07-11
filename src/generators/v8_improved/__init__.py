"""
V8 Improved Test Generator
改进的V8测试生成器 - 解决了原版的质量问题
"""

from .improved_test_generator import ImprovedTestGenerator
from .constraint_validator import ConstraintValidator
from .negative_test_strategy import ImprovedNegativeTestStrategy
from .boundary_test_strategy import ImprovedBoundaryTestStrategy
from .enhanced_constraint_solver import EnhancedConstraintSolver

__version__ = '8.1.0'
__all__ = [
    'ImprovedTestGenerator',
    'ConstraintValidator',
    'ImprovedNegativeTestStrategy',
    'ImprovedBoundaryTestStrategy',
    'EnhancedConstraintSolver'
]