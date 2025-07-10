#!/usr/bin/env python3
"""
DSL Test Generator - 主入口程序
使用 V3 版本作为默认生成器
"""

import argparse
import sys
from pathlib import Path

# 添加 src 到 Python 路径
sys.path.insert(0, str(Path(__file__).parent / 'src'))

from generators.v3_generator import UnifiedDSLTestGeneratorV3, TestGenerationConfig


def main():
    parser = argparse.ArgumentParser(
        description="DSL Test Generator - 自动生成高质量测试用例",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  # 基础用法
  python main.py examples/intermediate/user_account_system.yaml
  
  # 指定输出文件
  python main.py examples/intermediate/shopping_cart.yaml -o outputs/v3/cart_tests.json
  
  # 使用配置文件
  python main.py examples/advanced/advanced_ecommerce.yaml -c configs/test_config_v3.json
  
  # 启用性能模式
  python main.py examples/advanced/advanced_ecommerce.yaml --performance
        """
    )
    
    parser.add_argument("dsl_file", help="DSL YAML 文件路径")
    parser.add_argument("-o", "--output", help="输出文件路径 (默认: outputs/v3/<filename>_tests.json)")
    parser.add_argument("-c", "--config", help="配置文件路径 (JSON)")
    parser.add_argument("--max-tests", type=int, default=20, help="每种类型的最大测试数 (默认: 20)")
    parser.add_argument("--strategy", choices=['realistic', 'boundary', 'random'], 
                       default='realistic', help="值生成策略 (默认: realistic)")
    parser.add_argument("--performance", action="store_true", help="启用性能模式（缓存优化）")
    parser.add_argument("--no-templates", action="store_true", help="禁用模板测试")
    parser.add_argument("--version", action="version", version="DSL Test Generator v3.0")
    
    args = parser.parse_args()
    
    # 验证输入文件
    dsl_path = Path(args.dsl_file)
    if not dsl_path.exists():
        print(f"错误: DSL 文件不存在: {args.dsl_file}")
        sys.exit(1)
    
    # 设置默认输出路径
    if not args.output:
        output_dir = Path("outputs/v3")
        output_dir.mkdir(parents=True, exist_ok=True)
        output_file = output_dir / f"{dsl_path.stem}_tests.json"
        args.output = str(output_file)
    
    # 加载配置
    config_dict = {}
    if args.config:
        import json
        with open(args.config, 'r') as f:
            config_dict = json.load(f)
    
    # 命令行参数覆盖配置
    config_dict['max_tests_per_type'] = args.max_tests
    config_dict['value_strategy'] = args.strategy
    config_dict['performance_mode'] = args.performance
    config_dict['enable_templates'] = not args.no_templates
    
    config = TestGenerationConfig.from_dict(config_dict)
    
    try:
        # 生成测试
        print(f"使用 DSL 文件: {args.dsl_file}")
        generator = UnifiedDSLTestGeneratorV3(args.dsl_file, config)
        result = generator.generate_tests()
        
        # 保存结果
        import json
        with open(args.output, 'w', encoding='utf-8') as f:
            json.dump(result, f, ensure_ascii=False, indent=2)
        
        print(f"\n✅ 测试生成成功！")
        print(f"📄 输出文件: {args.output}")
        print(f"📊 生成了 {result['summary']['total_tests']} 个测试用例")
        
    except Exception as e:
        print(f"\n❌ 错误: {str(e)}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()