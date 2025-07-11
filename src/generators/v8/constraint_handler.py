"""
Constraint Handler Module
约束处理器
"""

import re
import logging
from typing import Any, Dict, List
from .models import Entity

logger = logging.getLogger(__name__)


class ConstraintHandler:
    """约束处理器"""
    
    def evaluate(self, expression: str, data: Dict[str, Any]) -> bool:
        """求值约束表达式"""
        try:
            # 替换变量
            expr = expression
            for key, value in data.items():
                if key in expr:
                    if isinstance(value, str):
                        expr = expr.replace(key, f"'{value}'")
                    elif isinstance(value, list):
                        expr = expr.replace(key, str(value))
                    else:
                        expr = expr.replace(key, str(value))
            
            # 处理特殊函数
            if 'size(' in expr:
                # 处理size函数
                size_pattern = r'size\((\w+)\)'
                def size_replacer(match):
                    var_name = match.group(1)
                    if var_name in data and hasattr(data[var_name], '__len__'):
                        return str(len(data[var_name]))
                    return '0'
                expr = re.sub(size_pattern, size_replacer, expr)
            
            # 安全求值
            allowed_names = {
                'len': len,
                'abs': abs,
                'min': min,
                'max': max,
                'sum': sum
            }
            
            result = eval(expr, {"__builtins__": {}}, allowed_names)
            return bool(result)
        except Exception as e:
            logger.warning(f"Failed to evaluate constraint '{expression}': {e}")
            return True  # 默认满足
    
    def fix_constraint_violation(self, data: Dict[str, Any], constraint: str, 
                               entity: Entity) -> Dict[str, Any]:
        """修复约束违反"""
        # 简单的修复策略
        if '>' in constraint:
            parts = constraint.split('>')
            if len(parts) == 2:
                left = parts[0].strip()
                right = parts[1].strip()
                
                # 处理简单的比较
                if left in data and right.strip().isdigit():
                    target = int(right)
                    if isinstance(data[left], (int, float)):
                        data[left] = target + random.randint(1, 10)
                
                # 处理字段间比较
                elif left in data and right in data:
                    if isinstance(data[left], (int, float)) and isinstance(data[right], (int, float)):
                        data[left] = data[right] + random.randint(1, 10)
        
        elif '<' in constraint:
            parts = constraint.split('<')
            if len(parts) == 2:
                left = parts[0].strip()
                right = parts[1].strip()
                
                if left in data and right.strip().isdigit():
                    target = int(right)
                    if isinstance(data[left], (int, float)):
                        data[left] = max(0, target - random.randint(1, 10))
                
                elif left in data and right in data:
                    if isinstance(data[left], (int, float)) and isinstance(data[right], (int, float)):
                        data[left] = max(0, data[right] - random.randint(1, 10))
        
        elif '>=' in constraint:
            parts = constraint.split('>=')
            if len(parts) == 2:
                left = parts[0].strip()
                right = parts[1].strip()
                
                if left in data and right.strip().isdigit():
                    target = int(right)
                    if isinstance(data[left], (int, float)):
                        data[left] = target + random.randint(0, 5)
        
        return data


# 为了保持向后兼容，需要导入random
import random