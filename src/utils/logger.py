"""
统一的日志配置
"""

import logging
from typing import Optional


def setup_logger(
    name: str = "dsl_test_generator",
    level: int = logging.INFO,
    format: Optional[str] = None
) -> logging.Logger:
    """
    设置日志记录器
    
    Args:
        name: 日志记录器名称
        level: 日志级别
        format: 日志格式
    
    Returns:
        配置好的日志记录器
    """
    if format is None:
        format = '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
    
    # 创建日志记录器
    logger = logging.getLogger(name)
    logger.setLevel(level)
    
    # 避免重复添加处理器
    if not logger.handlers:
        # 创建控制台处理器
        console_handler = logging.StreamHandler()
        console_handler.setLevel(level)
        
        # 创建格式化器
        formatter = logging.Formatter(format)
        console_handler.setFormatter(formatter)
        
        # 添加处理器到日志记录器
        logger.addHandler(console_handler)
    
    return logger