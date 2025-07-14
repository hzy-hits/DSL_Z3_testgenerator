#!/usr/bin/env python3
"""
Extended Test Generator Script
扩展测试生成器脚本 - 支持状态机、场景和时序约束测试
"""

import sys
from pathlib import Path

# 添加 src 到 Python 路径
sys.path.insert(0, str(Path(__file__).parent / 'src'))

from generators.v8_extended.extended_test_generator import ExtendedTestGenerator


def main():
    """主入口函数"""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="Extended DSL Test Generator - 支持状态机、场景和时序约束测试",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  # 生成包含状态机测试的用例
  python generate_extended.py dispatch_system_requirements.yaml
  
  # 指定输出文件并启用详细日志
  python generate_extended.py dispatch_system_requirements.yaml -o extended_tests.json -v
  
  # 生成完整的派单系统测试
  python generate_extended.py dispatch_system_v2_compatible.yaml -o dispatch_extended_tests.json -v

功能特性:
  状态转换测试 - 测试状态机的所有转换
  场景测试 - 端到端业务流程测试  
  时序约束测试 - 时间窗口和时序规则测试
  传统测试 - 功能、边界、约束、负面测试
        """
    )
    
    parser.add_argument('input_file', help='输入的YAML DSL文件')
    parser.add_argument('-o', '--output', 
                       help='输出的JSON测试文件 (默认: extended_tests.json)',
                       default='extended_tests.json')
    parser.add_argument('-v', '--verbose', action='store_true',
                       help='启用详细日志输出')
    parser.add_argument('--version', action='version', 
                       version='Extended Test Generator v1.0.0')
    
    args = parser.parse_args()
    
    # 验证输入文件
    input_path = Path(args.input_file)
    if not input_path.exists():
        print(f"错误: 输入文件不存在: {args.input_file}")
        return 1
    
    if not input_path.suffix.lower() in ['.yaml', '.yml']:
        print(f"错误: 输入文件必须是YAML格式 (.yaml 或 .yml)")
        return 1
    
    print("启动扩展测试生成器...")
    print(f"输入文件: {args.input_file}")
    print(f"输出文件: {args.output}")
    
    # 创建生成器并生成测试
    generator = ExtendedTestGenerator(verbose=args.verbose)
    
    try:
        result = generator.generate_from_file(args.input_file, args.output)
        
        # 打印结果摘要
        print("\n测试生成完成!")
        print("=" * 50)
        print(f"总测试数量: {result['metadata']['total_tests']}")
        print(f"领域: {result['metadata']['domain']}")
        print(f"实体数量: {result['metadata']['total_entities']}")
        print(f"状态机数量: {result['metadata']['total_state_machines']}")
        print(f"测试需求数量: {result['metadata']['total_test_requirements']}")
        
        # 显示测试类型分布
        print("\n测试类型分布:")
        for test_type, count in result['summary']['test_types'].items():
            print(f"  - {test_type}: {count} 个")
        
        # 显示覆盖率
        print("\n测试覆盖率:")
        for coverage_type, percentage in result['summary']['coverage'].items():
            print(f"  - {coverage_type}: {percentage:.1f}%")
        
        print(f"\n测试文件已保存到: {args.output}")
        print("\n新增功能包括:")
        print("  状态转换测试 - 验证状态机行为")
        print("  场景测试 - 端到端业务流程")
        print("  时序约束测试 - 时间窗口验证")
        
        return 0
        
    except Exception as e:
        print(f"\n生成失败: {str(e)}")
        if args.verbose:
            import traceback
            print("\n详细错误信息:")
            traceback.print_exc()
        return 1


if __name__ == '__main__':
    exit(main())