"""
Data Models for V8 Generator
数据模型定义
"""

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional


@dataclass
class Attribute:
    """属性定义"""
    name: str
    type: str
    required: bool = True
    enum: List[Any] = None
    is_collection: bool = False
    is_temporal: bool = False
    default: Any = None
    min_size: Optional[int] = None
    max_size: Optional[int] = None
    min: Optional[float] = None
    max: Optional[float] = None


@dataclass
class Entity:
    """实体定义"""
    name: str
    attributes: List[Attribute] = field(default_factory=list)
    constraints: List[str] = field(default_factory=list)
    rules: List[Dict[str, Any]] = field(default_factory=list)


@dataclass
class Test:
    """测试用例定义"""
    test_name: str
    test_type: str
    description: str
    test_data: Dict[str, Any]
    expected_result: str
    priority: int = 5
    test_id: Optional[str] = None
    entity: Optional[str] = None
    timestamp: Optional[str] = None
    constraint: Optional[str] = None
    expected_error: Optional[str] = None