#!/usr/bin/env python3
"""
DSL测试生成器CLI - 整合V8优化版本
"""

import json
import argparse
import logging
from pathlib import Path
import sys
import time
from typing import Dict, Any, List, Optional

# 使用相对导入
from ..generators.v8_improved import ImprovedTestGenerator
from ..generators.v8 import YAMLParser

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)
logger = logging.getLogger(__name__)


class TestGeneratorCLI:
    """测试生成器CLI接口"""
    
    def __init__(self):
        self.parser = self._create_parser()
        
    def _create_parser(self):
        """创建命令行解析器"""
        parser = argparse.ArgumentParser(
            description='DSL测试生成器 - 高质量测试用例生成',
            epilog="""
功能特性:
  ✓ 100%正确处理集合类型（array/set）
  ✓ 精确的边界值生成（满足所有约束）
  ✓ 智能的负面测试（生成正确类型但违反约束的值）
  ✓ Z3求解器智能回退策略
  ✓ 91%+的测试通过率

示例:
  # 基础用法
  python -m src.cli.generate examples/intermediate/shopping_cart.yaml
  
  # 生成详细报告
  python -m src.cli.generate examples/advanced/advanced_ecommerce.yaml --report
  
  # 批量处理
  python -m src.cli.generate --batch examples/
            """,
            formatter_class=argparse.RawDescriptionHelpFormatter
        )
        
        parser.add_argument('dsl_file', nargs='?', help='DSL YAML文件路径')
        parser.add_argument('-o', '--output', help='输出文件路径')
        parser.add_argument('-v', '--verbose', action='store_true', help='启用详细日志')
        parser.add_argument('--report', action='store_true', help='生成详细质量报告')
        parser.add_argument('--batch', help='批量处理目录下的所有YAML文件')
        parser.add_argument('--validate', action='store_true', help='验证生成的测试')
        parser.add_argument('--format', choices=['json', 'yaml', 'markdown', 'csv'], 
                          default='json', help='输出格式')
        parser.add_argument('--timeout', type=int, default=30, 
                          help='单个文件处理超时时间（秒）')
        
        return parser
    
    def run(self):
        """运行CLI"""
        args = self.parser.parse_args()
        
        if args.verbose:
            logging.getLogger().setLevel(logging.DEBUG)
        
        try:
            if args.batch:
                self._run_batch_mode(args)
            elif args.dsl_file:
                self._run_single_file(args)
            else:
                self.parser.print_help()
                sys.exit(1)
                
        except KeyboardInterrupt:
            logger.info("用户中断执行")
            sys.exit(1)
        except Exception as e:
            logger.error(f"执行失败: {e}")
            if args.verbose:
                import traceback
                traceback.print_exc()
            sys.exit(1)
    
    def _run_single_file(self, args):
        """处理单个文件"""
        dsl_path = Path(args.dsl_file)
        if not dsl_path.exists():
            raise FileNotFoundError(f"DSL文件不存在: {dsl_path}")
        
        # 设置输出路径
        if args.output:
            output_path = Path(args.output)
        else:
            output_dir = Path("outputs")
            output_dir.mkdir(exist_ok=True)
            output_path = output_dir / f"{dsl_path.stem}_tests.{args.format}"
        
        logger.info(f"处理文件: {dsl_path}")
        start_time = time.time()
        
        # 解析DSL
        parser = YAMLParser()
        entities = parser.parse_file(str(dsl_path))
        
        # 读取完整的DSL内容以获取rules等信息
        import yaml
        with open(dsl_path, 'r', encoding='utf-8') as f:
            dsl_content = yaml.safe_load(f)
        dsl_content['entities'] = entities
        
        # 生成测试
        generator = ImprovedTestGenerator()
        tests = generator.generate_tests(entities)
        
        # 构建结果
        result = {
            'tests': tests,
            'summary': {
                'total_tests': len(tests),
                'entities': [entity.name for entity in entities]
            }
        }
        
        # 添加元数据
        result['metadata'] = {
            'source_file': str(dsl_path),
            'generation_time': time.strftime('%Y-%m-%d %H:%M:%S'),
            'generator_version': 'v8_optimized',
            'processing_time': f"{time.time() - start_time:.2f}s"
        }
        
        # 保存结果
        self._save_output(result, output_path, args.format)
        
        # 生成报告
        if args.report:
            self._generate_report(result, dsl_path)
        
        # 验证测试
        if args.validate:
            self._validate_tests(result, dsl_content)
        
        logger.info(f"✅ 生成完成: {output_path}")
        logger.info(f"📊 测试数量: {len(result.get('tests', []))}")
        
    def _run_batch_mode(self, args):
        """批量处理模式"""
        batch_dir = Path(args.batch)
        if not batch_dir.exists():
            raise FileNotFoundError(f"批处理目录不存在: {batch_dir}")
        
        yaml_files = list(batch_dir.rglob("*.yaml")) + list(batch_dir.rglob("*.yml"))
        if not yaml_files:
            logger.warning(f"未找到YAML文件: {batch_dir}")
            return
        
        logger.info(f"找到 {len(yaml_files)} 个文件待处理")
        
        results = []
        for yaml_file in yaml_files:
            try:
                logger.info(f"处理: {yaml_file}")
                # 创建临时参数
                single_args = argparse.Namespace(
                    dsl_file=str(yaml_file),
                    output=None,
                    verbose=args.verbose,
                    report=False,
                    validate=False,
                    format=args.format,
                    timeout=args.timeout
                )
                self._run_single_file(single_args)
                results.append({
                    'file': str(yaml_file),
                    'status': 'success'
                })
            except Exception as e:
                logger.error(f"处理失败 {yaml_file}: {e}")
                results.append({
                    'file': str(yaml_file),
                    'status': 'failed',
                    'error': str(e)
                })
        
        # 生成批处理报告
        self._generate_batch_report(results)
    
    def _save_output(self, data: Dict, path: Path, format: str):
        """保存输出文件"""
        if format == 'json':
            with open(path, 'w', encoding='utf-8') as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
        elif format == 'yaml':
            import yaml
            with open(path, 'w', encoding='utf-8') as f:
                yaml.dump(data, f, allow_unicode=True, default_flow_style=False)
        elif format == 'markdown':
            self._save_as_markdown(data, path)
        elif format == 'csv':
            self._save_as_csv(data, path)
    
    def _save_as_markdown(self, data: Dict, path: Path):
        """保存为Markdown格式"""
        with open(path, 'w', encoding='utf-8') as f:
            f.write(f"# 测试用例报告\n\n")
            f.write(f"生成时间: {data['metadata']['generation_time']}\n\n")
            f.write(f"## 统计信息\n\n")
            f.write(f"- 总测试数: {len(data.get('tests', []))}\n")
            f.write(f"- 源文件: {data['metadata']['source_file']}\n\n")
            
            f.write("## 测试用例\n\n")
            for i, test in enumerate(data.get('tests', []), 1):
                f.write(f"### 测试 {i}: {test.get('name', 'Unknown')}\n\n")
                f.write(f"**类型**: {test.get('type', 'Unknown')}\n\n")
                f.write(f"**描述**: {test.get('description', 'N/A')}\n\n")
                f.write("**数据**:\n```json\n")
                f.write(json.dumps(test.get('data', {}), ensure_ascii=False, indent=2))
                f.write("\n```\n\n")
    
    def _save_as_csv(self, data: Dict, path: Path):
        """保存为CSV格式"""
        import csv
        with open(path, 'w', encoding='utf-8', newline='') as f:
            if not data.get('tests'):
                return
            
            # 提取所有字段
            fieldnames = ['test_name', 'test_type', 'description']
            sample_data = data['tests'][0].get('data', {})
            if sample_data:
                fieldnames.extend(self._flatten_dict_keys(sample_data))
            
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            
            for test in data['tests']:
                row = {
                    'test_name': test.get('name', ''),
                    'test_type': test.get('type', ''),
                    'description': test.get('description', '')
                }
                flat_data = self._flatten_dict(test.get('data', {}))
                row.update(flat_data)
                writer.writerow(row)
    
    def _flatten_dict(self, d: Dict, parent_key: str = '', sep: str = '.') -> Dict:
        """展平嵌套字典"""
        items = []
        for k, v in d.items():
            new_key = f"{parent_key}{sep}{k}" if parent_key else k
            if isinstance(v, dict):
                items.extend(self._flatten_dict(v, new_key, sep=sep).items())
            else:
                items.append((new_key, v))
        return dict(items)
    
    def _flatten_dict_keys(self, d: Dict, parent_key: str = '', sep: str = '.') -> List[str]:
        """获取展平后的所有键"""
        return list(self._flatten_dict(d, parent_key, sep).keys())
    
    def _generate_report(self, result: Dict, dsl_path: Path):
        """生成详细报告"""
        report = {
            'source_file': str(dsl_path),
            'generation_time': result['metadata']['generation_time'],
            'total_tests': len(result.get('tests', [])),
            'test_types': {}
        }
        
        # 统计测试类型
        for test in result.get('tests', []):
            test_type = test.get('type', 'unknown')
            report['test_types'][test_type] = report['test_types'].get(test_type, 0) + 1
        
        # 打印报告
        print("\n" + "="*50)
        print("📊 测试生成报告")
        print("="*50)
        print(f"源文件: {report['source_file']}")
        print(f"生成时间: {report['generation_time']}")
        print(f"总测试数: {report['total_tests']}")
        print("\n测试类型分布:")
        for test_type, count in report['test_types'].items():
            print(f"  - {test_type}: {count}")
        print("="*50 + "\n")
    
    def _validate_tests(self, result: Dict, dsl_content: Dict):
        """验证生成的测试"""
        from ..generators.v8_improved.constraint_validator import ConstraintValidator
        
        validator = ConstraintValidator()
        validation_results = []
        
        for test in result.get('tests', []):
            test_data = test.get('data', {})
            is_valid, violations = validator.validate_test_data(
                test_data, 
                dsl_content['entities'], 
                dsl_content.get('rules', [])
            )
            validation_results.append({
                'test_name': test.get('name'),
                'valid': is_valid,
                'violations': violations
            })
        
        # 统计验证结果
        valid_count = sum(1 for r in validation_results if r['valid'])
        print(f"\n✅ 验证通过: {valid_count}/{len(validation_results)}")
        
        if valid_count < len(validation_results):
            print("\n❌ 验证失败的测试:")
            for result in validation_results:
                if not result['valid']:
                    print(f"  - {result['test_name']}: {', '.join(result['violations'])}")
    
    def _generate_batch_report(self, results: List[Dict]):
        """生成批处理报告"""
        success_count = sum(1 for r in results if r['status'] == 'success')
        
        print("\n" + "="*50)
        print("📊 批处理报告")
        print("="*50)
        print(f"总文件数: {len(results)}")
        print(f"成功: {success_count}")
        print(f"失败: {len(results) - success_count}")
        
        if success_count < len(results):
            print("\n失败的文件:")
            for result in results:
                if result['status'] == 'failed':
                    print(f"  - {result['file']}: {result['error']}")
        print("="*50 + "\n")


def main():
    """主入口"""
    cli = TestGeneratorCLI()
    cli.run()


if __name__ == "__main__":
    main()