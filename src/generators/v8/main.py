#!/usr/bin/env python3
"""
V8 Test Generator - Main Entry Point
统一的命令行接口
"""

import json
import argparse
import logging
from pathlib import Path
import sys

# 添加项目根目录到Python路径
project_root = Path(__file__).parent.parent.parent.parent
sys.path.insert(0, str(project_root))

from src.generators.v8 import TestGenerator, YAMLParser

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


def main():
    """主函数"""
    parser = argparse.ArgumentParser(description='V8 Modular Test Generator')
    parser.add_argument('dsl_file', help='Path to DSL YAML file')
    parser.add_argument('-o', '--output', default='generated_tests.json',
                       help='Output file path')
    parser.add_argument('-v', '--verbose', action='store_true',
                       help='Enable verbose logging')
    parser.add_argument('--format', choices=['json', 'yaml'], default='json',
                       help='Output format')
    
    args = parser.parse_args()
    
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)
    
    try:
        # 解析YAML
        yaml_parser = YAMLParser()
        entities = yaml_parser.parse_file(args.dsl_file)
        logger.info(f"Parsed {len(entities)} entities from {args.dsl_file}")
        
        # 生成测试
        generator = TestGenerator()
        test_suite = generator.generate_test_suite(entities)
        logger.info(f"Generated {test_suite['total_tests']} tests")
        
        # 添加源文件信息
        test_suite['dsl_file'] = args.dsl_file
        
        # 确保输出目录存在
        output_path = Path(args.output)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        # 保存结果
        if args.format == 'json':
            with open(output_path, 'w', encoding='utf-8') as f:
                json.dump(test_suite, f, indent=2, ensure_ascii=False)
        else:
            import yaml
            with open(output_path, 'w', encoding='utf-8') as f:
                yaml.dump(test_suite, f, default_flow_style=False, allow_unicode=True)
        
        logger.info(f"Output saved to: {args.output}")
        
        # 打印统计
        print("\nTest Statistics:")
        for test_type, count in sorted(test_suite['statistics']['by_type'].items()):
            print(f"  {test_type}: {count}")
        print(f"\nTotal: {test_suite['total_tests']} tests")
        
        # 打印实体统计
        print("\nTests by Entity:")
        for entity, count in test_suite['statistics']['by_entity'].items():
            print(f"  {entity}: {count}")
        
    except Exception as e:
        logger.error(f"Error: {e}")
        raise


if __name__ == '__main__':
    main()