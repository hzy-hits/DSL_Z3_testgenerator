#!/usr/bin/env python3
"""
比较不同版本的测试生成器性能和质量
"""

import time
import subprocess
import json
import yaml
from pathlib import Path
from typing import Dict, List, Any
import statistics


class VersionComparator:
    """版本比较器"""
    
    def __init__(self, examples_dir: str = "examples"):
        self.examples_dir = Path(examples_dir)
        self.versions = {
            "v1": "dsl2test.py",
            "v2": "unified_dsl2test_v2.py", 
            "v3": "unified_dsl2test_v3.py"
        }
        self.results = {}
    
    def run_comparison(self, test_files: List[str] = None):
        """运行比较测试"""
        if test_files is None:
            test_files = list(self.examples_dir.glob("*.yaml"))
        else:
            test_files = [Path(f) for f in test_files]
        
        print("版本性能和质量比较")
        print("=" * 80)
        
        for test_file in test_files:
            print(f"\n测试文件: {test_file.name}")
            print("-" * 60)
            
            # 加载 DSL 获取基本信息
            with open(test_file, 'r', encoding='utf-8') as f:
                dsl = yaml.safe_load(f)
            
            domain = dsl.get('domain', 'Unknown')
            print(f"领域: {domain}")
            
            file_results = {}
            
            for version_name, generator_script in self.versions.items():
                if not Path(generator_script).exists():
                    print(f"  {version_name}: 生成器不存在")
                    continue
                
                print(f"\n  运行 {version_name}...")
                result = self._run_generator(generator_script, test_file, version_name)
                file_results[version_name] = result
                
                if result['success']:
                    self._print_version_result(version_name, result)
                else:
                    print(f"    ❌ 生成失败: {result['error']}")
            
            self.results[test_file.name] = file_results
        
        # 打印总结
        self._print_summary()
    
    def _run_generator(self, generator: str, test_file: Path, version: str) -> Dict[str, Any]:
        """运行单个生成器"""
        output_file = f"temp_output_{version}_{test_file.stem}.json"
        
        # 构建命令
        cmd = ["python", generator, str(test_file), "-o", output_file]
        
        # V3 特殊参数
        if version == "v3":
            cmd.extend(["-c", "test_config_v3.json", "--performance"])
        
        # 记录开始时间
        start_time = time.time()
        
        try:
            # 运行生成器
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
            
            # 记录结束时间
            end_time = time.time()
            duration = end_time - start_time
            
            if result.returncode != 0:
                return {
                    'success': False,
                    'error': result.stderr,
                    'duration': duration
                }
            
            # 解析输出
            with open(output_file, 'r', encoding='utf-8') as f:
                output_data = json.load(f)
            
            # 提取统计信息
            stats = self._extract_statistics(output_data, version)
            stats['duration'] = duration
            stats['success'] = True
            
            # 清理临时文件
            Path(output_file).unlink(missing_ok=True)
            
            return stats
            
        except subprocess.TimeoutExpired:
            return {
                'success': False,
                'error': 'Timeout (30s)',
                'duration': 30
            }
        except Exception as e:
            return {
                'success': False,
                'error': str(e),
                'duration': 0
            }
    
    def _extract_statistics(self, data: Dict[str, Any], version: str) -> Dict[str, Any]:
        """提取统计信息"""
        stats = {}
        
        if version == "v1":
            # V1 格式
            total_tests = 0
            test_types = {}
            
            for suite_name, suite_data in data.items():
                if isinstance(suite_data, dict) and 'tests' in suite_data:
                    test_count = len(suite_data['tests'])
                    total_tests += test_count
                    test_types[suite_name] = test_count
            
            stats['total_tests'] = total_tests
            stats['test_types'] = test_types
            stats['unique_tests'] = total_tests  # V1 没有去重
            
        else:
            # V2/V3 格式
            summary = data.get('summary', {})
            meta = data.get('meta', {})
            
            stats['total_tests'] = summary.get('total_tests', 0)
            stats['test_types'] = summary.get('test_distribution', {})
            stats['coverage'] = summary.get('coverage_rate', 'N/A')
            
            # V3 特有统计
            if version == "v3" and 'generation_stats' in meta:
                gen_stats = meta['generation_stats']
                stats['solver_calls'] = gen_stats.get('solver_calls', 0)
                stats['cache_hits'] = gen_stats.get('cache_hits', 0)
                stats['generation_time'] = gen_stats.get('duration', 0)
        
        return stats
    
    def _print_version_result(self, version: str, result: Dict[str, Any]):
        """打印版本结果"""
        print(f"    ✅ 成功")
        print(f"    总测试数: {result.get('total_tests', 0)}")
        print(f"    生成时间: {result['duration']:.3f}s")
        
        if 'coverage' in result:
            print(f"    覆盖率: {result['coverage']}")
        
        if 'solver_calls' in result:
            print(f"    求解器调用: {result['solver_calls']}")
            print(f"    缓存命中: {result['cache_hits']}")
        
        # 测试类型分布
        test_types = result.get('test_types', {})
        if test_types:
            print("    测试类型分布:")
            for test_type, count in sorted(test_types.items(), key=lambda x: x[1], reverse=True):
                print(f"      - {test_type}: {count}")
    
    def _print_summary(self):
        """打印总结"""
        print("\n" + "=" * 80)
        print("性能和质量总结")
        print("=" * 80)
        
        # 收集所有版本的数据
        version_stats = {v: {'times': [], 'tests': [], 'files': 0} for v in self.versions.keys()}
        
        for file_name, file_results in self.results.items():
            for version, result in file_results.items():
                if result['success']:
                    version_stats[version]['times'].append(result['duration'])
                    version_stats[version]['tests'].append(result.get('total_tests', 0))
                    version_stats[version]['files'] += 1
        
        # 打印每个版本的统计
        print("\n版本对比:")
        print("-" * 60)
        print(f"{'版本':<10} {'成功文件':<10} {'平均时间':<12} {'平均测试数':<12} {'总测试数':<10}")
        print("-" * 60)
        
        for version in self.versions.keys():
            stats = version_stats[version]
            if stats['times']:
                avg_time = statistics.mean(stats['times'])
                avg_tests = statistics.mean(stats['tests'])
                total_tests = sum(stats['tests'])
                print(f"{version:<10} {stats['files']:<10} {avg_time:<12.3f} {avg_tests:<12.1f} {total_tests:<10}")
            else:
                print(f"{version:<10} {'0':<10} {'N/A':<12} {'N/A':<12} {'0':<10}")
        
        # 性能排名
        print("\n性能排名 (按平均生成时间):")
        print("-" * 40)
        
        valid_versions = [(v, statistics.mean(s['times'])) 
                         for v, s in version_stats.items() if s['times']]
        valid_versions.sort(key=lambda x: x[1])
        
        for i, (version, avg_time) in enumerate(valid_versions, 1):
            print(f"{i}. {version}: {avg_time:.3f}s")
        
        # 测试数量排名
        print("\n测试数量排名 (按平均测试数):")
        print("-" * 40)
        
        test_versions = [(v, statistics.mean(s['tests'])) 
                        for v, s in version_stats.items() if s['tests']]
        test_versions.sort(key=lambda x: x[1], reverse=True)
        
        for i, (version, avg_tests) in enumerate(test_versions, 1):
            print(f"{i}. {version}: {avg_tests:.1f} tests")
        
        # 特性对比
        print("\n特性对比:")
        print("-" * 60)
        features = {
            "v1": ["Z3 约束求解", "基础测试生成", "简单去重"],
            "v2": ["Z3 约束求解", "增强类型支持", "Optional 字段", "智能去重", "场景测试", "组合测试"],
            "v3": ["高级约束求解", "测试模板", "性能优化", "缓存机制", "自定义验证器", "时间约束", "安全测试"]
        }
        
        for version, feature_list in features.items():
            print(f"\n{version} 特性:")
            for feature in feature_list:
                print(f"  ✓ {feature}")


def main():
    """主函数"""
    import argparse
    
    parser = argparse.ArgumentParser(description="比较不同版本的测试生成器")
    parser.add_argument("--files", nargs="+", help="指定要测试的文件")
    parser.add_argument("--examples-dir", default="examples", help="示例文件目录")
    
    args = parser.parse_args()
    
    comparator = VersionComparator(args.examples_dir)
    
    # 运行比较
    if args.files:
        comparator.run_comparison(args.files)
    else:
        # 默认测试几个代表性文件
        test_files = [
            "examples/user_account_system.yaml",
            "examples/shopping_cart.yaml",
            "examples/order_processing_system.yaml"
        ]
        # 如果高级示例存在，也加入测试
        if Path("examples/advanced_ecommerce.yaml").exists():
            test_files.append("examples/advanced_ecommerce.yaml")
        
        comparator.run_comparison(test_files)


if __name__ == "__main__":
    main()