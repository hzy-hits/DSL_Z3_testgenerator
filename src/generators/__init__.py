"""
测试生成器模块

包含不同版本的测试生成器实现：
- V1: 基础 Z3 求解器实现
- V2: 统一架构，支持 Optional 字段
- V3: 高级版本，支持模板和配置驱动
"""

# 注意：由于模块依赖，实际导入需要在使用时进行
# 以下为使用示例：

# from .v1_generator import DSLTestGenerator as V1Generator
# from .v2_generator import UnifiedDSLTestGeneratorV2 as V2Generator  
# from .v3_generator import UnifiedDSLTestGeneratorV3 as V3Generator

__all__ = ['V1Generator', 'V2Generator', 'V3Generator']