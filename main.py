#!/usr/bin/env python3
"""
DSL Test Generator - 主入口程序
整合V8优化版本，提供统一的命令行接口
"""

import argparse
import sys
from pathlib import Path

# 添加 src 到 Python 路径
sys.path.insert(0, str(Path(__file__).parent))

from src.cli.generate import TestGeneratorCLI
from src.cli.evaluate import TestQualityEvaluator


def main():
    """主入口函数"""
    parser = argparse.ArgumentParser(
        description="DSL Test Generator - 高质量测试用例生成工具",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
子命令:
  generate    生成测试用例
  evaluate    评估测试质量

示例:
  # 生成测试用例
  python main.py generate examples/intermediate/shopping_cart.yaml
  
  # 批量生成
  python main.py generate --batch examples/
  
  # 评估测试质量
  python main.py evaluate outputs/shopping_cart_tests.json
  
  # 使用旧版兼容模式（直接传入文件）
  python main.py examples/intermediate/shopping_cart.yaml

更多帮助:
  python main.py generate --help
  python main.py evaluate --help
        """
    )
    
    parser.add_argument('--version', action='version', version='DSL Test Generator v8.0 (Optimized)')
    
    # 创建子命令
    subparsers = parser.add_subparsers(dest='command', help='可用命令')
    
    # generate 子命令
    parser_generate = subparsers.add_parser('generate', help='生成测试用例')
    parser_generate.add_argument('dsl_file', nargs='?', help='DSL YAML文件路径')
    parser_generate.add_argument('-o', '--output', help='输出文件路径')
    parser_generate.add_argument('-v', '--verbose', action='store_true', help='启用详细日志')
    parser_generate.add_argument('--report', action='store_true', help='生成详细质量报告')
    parser_generate.add_argument('--batch', help='批量处理目录下的所有YAML文件')
    parser_generate.add_argument('--validate', action='store_true', help='验证生成的测试')
    parser_generate.add_argument('--format', choices=['json', 'yaml', 'markdown', 'csv'], 
                              default='json', help='输出格式')
    
    # evaluate 子命令
    parser_evaluate = subparsers.add_parser('evaluate', help='评估测试质量')
    parser_evaluate.add_argument('test_file', help='测试文件路径（JSON格式）')
    parser_evaluate.add_argument('-v', '--verbose', action='store_true', help='显示详细信息')
    parser_evaluate.add_argument('-o', '--output', help='输出报告文件路径')
    parser_evaluate.add_argument('--format', choices=['json', 'markdown', 'text'], 
                              default='text', help='报告格式')
    
    # 兼容旧版用法：如果第一个参数是.yaml文件，自动使用generate命令
    if len(sys.argv) > 1 and sys.argv[1].endswith(('.yaml', '.yml')):
        # 重构参数以支持旧版用法
        sys.argv.insert(1, 'generate')
    
    # 解析参数
    args = parser.parse_args()
    
    # 执行相应的命令
    if args.command == 'generate':
        # 使用新的参数创建CLI实例
        sys.argv = ['main.py'] + sys.argv[2:]  # 移除'generate'子命令
        cli = TestGeneratorCLI()
        cli.run()
    elif args.command == 'evaluate':
        # 使用新的参数创建评估器实例
        sys.argv = ['main.py'] + sys.argv[2:]  # 移除'evaluate'子命令
        evaluator = TestQualityEvaluator()
        evaluator.run()
    else:
        # 没有指定命令，显示帮助
        parser.print_help()
        sys.exit(1)


if __name__ == "__main__":
    main()