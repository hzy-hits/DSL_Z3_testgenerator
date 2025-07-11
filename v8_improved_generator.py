#!/usr/bin/env python3
"""
V8 Improved Test Generator - Main Entry Point
改进的V8测试生成器主入口
"""

import json
import argparse
import logging
from pathlib import Path
import sys

# 添加项目根目录到Python路径
project_root = Path(__file__).parent
sys.path.insert(0, str(project_root))

from src.generators.v8 import YAMLParser
from src.generators.v8_improved import ImprovedTestGenerator

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


def main():
    """主函数"""
    parser = argparse.ArgumentParser(
        description='V8 Improved Test Generator - 生成高质量的测试用例',
        epilog="""
改进内容:
  - 负面测试生成正确的约束违反值而非错误类型
  - 边界值测试确保满足其他约束
  - 复杂约束（如订单总价）正确处理
  - Z3求解失败时有智能回退策略
  - 所有测试都经过约束验证
        """
    )
    parser.add_argument('dsl_file', help='DSL YAML文件路径')
    parser.add_argument('-o', '--output', default='improved_tests.json',
                       help='输出文件路径')
    parser.add_argument('-v', '--verbose', action='store_true',
                       help='启用详细日志')
    parser.add_argument('--validate-only', action='store_true',
                       help='仅验证现有测试文件')
    parser.add_argument('--format', choices=['json', 'yaml', 'markdown'], default='json',
                       help='输出格式')
    
    args = parser.parse_args()
    
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)
    
    # 验证模式
    if args.validate_only:
        validate_existing_tests(args.dsl_file)
        return
    
    try:
        # 解析YAML
        yaml_parser = YAMLParser()
        entities = yaml_parser.parse_file(args.dsl_file)
        logger.info(f"解析了 {len(entities)} 个实体从 {args.dsl_file}")
        
        # 生成测试
        generator = ImprovedTestGenerator()
        test_suite = generator.generate_test_suite(entities)
        logger.info(f"生成了 {test_suite['total_tests']} 个测试")
        
        # 添加源文件信息
        test_suite['dsl_file'] = args.dsl_file
        
        # 确保输出目录存在
        output_path = Path(args.output)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        # 保存结果
        if args.format == 'json':
            with open(output_path, 'w', encoding='utf-8') as f:
                json.dump(test_suite, f, indent=2, ensure_ascii=False)
        elif args.format == 'yaml':
            import yaml
            with open(output_path, 'w', encoding='utf-8') as f:
                yaml.dump(test_suite, f, default_flow_style=False, allow_unicode=True)
        elif args.format == 'markdown':
            save_as_markdown(test_suite, output_path)
        
        logger.info(f"输出保存到: {args.output}")
        
        # 打印统计和质量报告
        print_statistics(test_suite)
        
    except Exception as e:
        logger.error(f"错误: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


def validate_existing_tests(test_file: str):
    """验证现有的测试文件"""
    try:
        with open(test_file, 'r') as f:
            test_suite = json.load(f)
        
        print(f"\n验证测试文件: {test_file}")
        print("=" * 80)
        
        # 简单的验证逻辑
        total_tests = test_suite.get('total_tests', 0)
        tests = test_suite.get('tests', [])
        
        print(f"总测试数: {total_tests}")
        print(f"实际测试数: {len(tests)}")
        
        # 检查测试类型分布
        test_types = {}
        for test in tests:
            test_type = test.get('test_type', 'unknown')
            test_types[test_type] = test_types.get(test_type, 0) + 1
        
        print("\n测试类型分布:")
        for test_type, count in sorted(test_types.items()):
            print(f"  {test_type}: {count}")
        
        # 检查负面测试
        negative_tests = [t for t in tests if t.get('test_type') == 'negative']
        print(f"\n负面测试分析:")
        print(f"  总数: {len(negative_tests)}")
        
        # 检查是否使用了错误类型
        wrong_type_count = 0
        for test in negative_tests:
            test_data = test.get('test_data', {})
            for key, value in test_data.items():
                if value in ["not_a_number", None] or isinstance(value, str) and value.startswith("INVALID"):
                    wrong_type_count += 1
                    break
        
        print(f"  使用错误类型的测试: {wrong_type_count}")
        
    except Exception as e:
        print(f"验证失败: {e}")


def save_as_markdown(test_suite: dict, output_path: Path):
    """将测试套件保存为Markdown格式"""
    with open(output_path, 'w', encoding='utf-8') as f:
        f.write(f"# 测试套件报告\n\n")
        f.write(f"生成时间: {test_suite['generation_time']}\n")
        f.write(f"生成器版本: {test_suite.get('generator_version', 'unknown')}\n")
        f.write(f"总测试数: {test_suite['total_tests']}\n\n")
        
        # 统计信息
        f.write("## 统计信息\n\n")
        f.write("### 按类型统计\n")
        for test_type, count in test_suite['statistics']['by_type'].items():
            f.write(f"- {test_type}: {count}\n")
        
        f.write("\n### 按实体统计\n")
        for entity, count in test_suite['statistics']['by_entity'].items():
            f.write(f"- {entity}: {count}\n")
        
        # 质量报告
        if 'quality_report' in test_suite:
            f.write("\n## 质量报告\n\n")
            quality = test_suite['quality_report']
            
            f.write("### 约束覆盖\n")
            for entity, coverage in quality.get('constraint_coverage', {}).items():
                f.write(f"- {entity}: {coverage['covered']}/{coverage['total_constraints']}\n")
            
            f.write("\n### 边界覆盖\n")
            for entity, coverage in quality.get('boundary_coverage', {}).items():
                f.write(f"- {entity}: {coverage['covered']}/{coverage['total_boundaries']}\n")
        
        # 测试详情
        f.write("\n## 测试详情\n\n")
        for test in test_suite['tests']:
            f.write(f"### {test['test_name']}\n")
            f.write(f"- 类型: {test['test_type']}\n")
            f.write(f"- 描述: {test['description']}\n")
            f.write(f"- 预期结果: {test['expected_result']}\n")
            if 'constraint' in test:
                f.write(f"- 约束: {test['constraint']}\n")
            f.write(f"- 测试数据:\n```json\n{json.dumps(test['test_data'], indent=2, ensure_ascii=False)}\n```\n\n")


def print_statistics(test_suite: dict):
    """打印统计信息"""
    print("\n" + "=" * 80)
    print("测试生成统计")
    print("=" * 80)
    
    # 基本统计
    print(f"\n生成器版本: {test_suite.get('generator_version', 'unknown')}")
    print(f"总测试数: {test_suite['total_tests']}")
    
    # 按类型统计
    print("\n按类型统计:")
    for test_type, count in sorted(test_suite['statistics']['by_type'].items()):
        print(f"  {test_type}: {count}")
    
    # 按实体统计
    print("\n按实体统计:")
    for entity, count in test_suite['statistics']['by_entity'].items():
        print(f"  {entity}: {count}")
    
    # 约束满足统计
    if 'constraint_satisfaction' in test_suite['statistics']:
        cs = test_suite['statistics']['constraint_satisfaction']
        print(f"\n约束满足情况:")
        print(f"  满足约束的测试: {cs['satisfied']}")
        print(f"  违反约束的测试: {cs['violated']}")
    
    # 质量报告
    if 'quality_report' in test_suite:
        print("\n质量报告:")
        quality = test_suite['quality_report']
        
        # 约束覆盖
        if quality.get('constraint_coverage'):
            print("\n  约束覆盖:")
            for entity, coverage in quality['constraint_coverage'].items():
                percentage = (coverage['covered'] / coverage['total_constraints'] * 100) if coverage['total_constraints'] > 0 else 0
                print(f"    {entity}: {coverage['covered']}/{coverage['total_constraints']} ({percentage:.1f}%)")
        
        # 边界覆盖
        if quality.get('boundary_coverage'):
            print("\n  边界覆盖:")
            for entity, coverage in quality['boundary_coverage'].items():
                percentage = (coverage['covered'] / coverage['total_boundaries'] * 100) if coverage['total_boundaries'] > 0 else 0
                print(f"    {entity}: {coverage['covered']}/{coverage['total_boundaries']} ({percentage:.1f}%)")
        
        # 问题汇总
        if quality.get('issues'):
            print(f"\n  发现的问题: {len(quality['issues'])}")
            for issue in quality['issues'][:5]:  # 只显示前5个
                print(f"    - {issue}")
    
    print("\n" + "=" * 80)


if __name__ == '__main__':
    main()