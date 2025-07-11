#!/usr/bin/env python3
"""
综合测试评估脚本 - 对所有DSL示例进行全面测试和评估
"""

import os
import json
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Tuple
import time

# 添加项目根目录到Python路径
sys.path.insert(0, str(Path(__file__).parent))


class ComprehensiveTestEvaluator:
    """综合测试评估器"""
    
    def __init__(self):
        self.results = {
            'total_files': 0,
            'successful_generation': 0,
            'failed_generation': 0,
            'test_quality': {},
            'common_issues': {},
            'improvement_suggestions': []
        }
        
    def run_comprehensive_evaluation(self):
        """运行综合评估"""
        print("=" * 80)
        print("DSL测试生成器综合评估")
        print("=" * 80)
        
        # 收集所有DSL文件
        dsl_files = self._collect_dsl_files()
        self.results['total_files'] = len(dsl_files)
        
        print(f"\n找到 {len(dsl_files)} 个DSL文件")
        
        # 为每个文件生成和评估测试
        for i, dsl_file in enumerate(dsl_files):
            print(f"\n[{i+1}/{len(dsl_files)}] 处理: {dsl_file}")
            self._process_dsl_file(dsl_file)
        
        # 生成总结报告
        self._generate_summary_report()
        
    def _collect_dsl_files(self) -> List[str]:
        """收集所有DSL示例文件"""
        dsl_files = []
        for root, dirs, files in os.walk('examples'):
            for file in files:
                if file.endswith('.yaml'):
                    dsl_files.append(os.path.join(root, file))
        return sorted(dsl_files)
    
    def _process_dsl_file(self, dsl_file: str):
        """处理单个DSL文件"""
        file_name = Path(dsl_file).stem
        output_dir = 'comprehensive_test_outputs'
        os.makedirs(output_dir, exist_ok=True)
        
        # 1. 使用改进版生成器生成测试
        output_file = os.path.join(output_dir, f"{file_name}_tests.json")
        generation_success = self._generate_tests(dsl_file, output_file)
        
        if generation_success:
            self.results['successful_generation'] += 1
            
            # 2. 评估生成的测试质量
            quality_results = self._evaluate_test_quality(output_file, dsl_file)
            self.results['test_quality'][file_name] = quality_results
            
            # 3. 分析常见问题
            self._analyze_issues(file_name, quality_results)
        else:
            self.results['failed_generation'] += 1
            self.results['test_quality'][file_name] = {'error': 'Generation failed'}
    
    def _generate_tests(self, dsl_file: str, output_file: str) -> bool:
        """生成测试用例"""
        try:
            cmd = [
                'python', 'v8_improved_generator.py',
                dsl_file, '-o', output_file
            ]
            
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
            
            if result.returncode == 0:
                print(f"  ✓ 测试生成成功")
                return True
            else:
                print(f"  ✗ 测试生成失败: {result.stderr[:200]}")
                return False
                
        except subprocess.TimeoutExpired:
            print(f"  ✗ 测试生成超时")
            return False
        except Exception as e:
            print(f"  ✗ 测试生成异常: {e}")
            return False
    
    def _evaluate_test_quality(self, test_file: str, dsl_file: str) -> Dict:
        """评估测试质量"""
        try:
            # 使用评估脚本
            cmd = ['python', 'evaluate_test_quality.py', test_file]
            result = subprocess.run(cmd, capture_output=True, text=True)
            
            # 解析输出
            output = result.stdout + result.stderr
            
            # 提取关键指标
            quality_metrics = {
                'total_tests': 0,
                'passed': 0,
                'failed': 0,
                'pass_rate': 0.0,
                'violations': [],
                'test_types': {}
            }
            
            # 解析输出中的数据
            lines = output.split('\n')
            for line in lines:
                if '总测试数:' in line:
                    quality_metrics['total_tests'] = int(line.split(':')[1].strip())
                elif '通过:' in line and '(' in line:
                    parts = line.split(':')[1].strip().split('(')
                    quality_metrics['passed'] = int(parts[0].strip())
                    quality_metrics['pass_rate'] = float(parts[1].replace('%)', '').strip())
                elif '失败:' in line and '(' in line:
                    parts = line.split(':')[1].strip().split('(')
                    quality_metrics['failed'] = int(parts[0].strip())
                elif '违反约束:' in line:
                    quality_metrics['violations'].append(line.strip())
            
            # 加载测试文件分析详情
            if os.path.exists(test_file):
                with open(test_file, 'r') as f:
                    test_data = json.load(f)
                    
                # 分析测试类型分布
                for test in test_data.get('tests', []):
                    test_type = test.get('test_type', 'unknown')
                    quality_metrics['test_types'][test_type] = quality_metrics['test_types'].get(test_type, 0) + 1
            
            print(f"  ✓ 质量评估完成: {quality_metrics['passed']}/{quality_metrics['total_tests']} 通过 ({quality_metrics['pass_rate']:.1f}%)")
            
            return quality_metrics
            
        except Exception as e:
            print(f"  ✗ 质量评估失败: {e}")
            return {'error': str(e)}
    
    def _analyze_issues(self, file_name: str, quality_results: Dict):
        """分析常见问题"""
        if 'error' in quality_results:
            return
        
        # 统计常见违反的约束
        for violation in quality_results.get('violations', []):
            if violation not in self.results['common_issues']:
                self.results['common_issues'][violation] = 0
            self.results['common_issues'][violation] += 1
    
    def _generate_summary_report(self):
        """生成总结报告"""
        print("\n" + "=" * 80)
        print("综合评估总结")
        print("=" * 80)
        
        # 基本统计
        print(f"\n文件统计:")
        print(f"  总文件数: {self.results['total_files']}")
        print(f"  成功生成: {self.results['successful_generation']}")
        print(f"  生成失败: {self.results['failed_generation']}")
        
        # 质量统计
        total_tests = 0
        total_passed = 0
        total_failed = 0
        
        print(f"\n质量统计:")
        for file_name, metrics in self.results['test_quality'].items():
            if 'error' not in metrics:
                total_tests += metrics.get('total_tests', 0)
                total_passed += metrics.get('passed', 0)
                total_failed += metrics.get('failed', 0)
                
                print(f"  {file_name}: {metrics.get('pass_rate', 0):.1f}% 通过率")
        
        if total_tests > 0:
            overall_pass_rate = (total_passed / total_tests) * 100
            print(f"\n总体统计:")
            print(f"  总测试数: {total_tests}")
            print(f"  总通过数: {total_passed}")
            print(f"  总失败数: {total_failed}")
            print(f"  总体通过率: {overall_pass_rate:.1f}%")
        
        # 常见问题
        if self.results['common_issues']:
            print(f"\n最常见的问题:")
            sorted_issues = sorted(self.results['common_issues'].items(), 
                                 key=lambda x: x[1], reverse=True)
            for issue, count in sorted_issues[:10]:
                print(f"  - {issue} (出现 {count} 次)")
        
        # 保存详细报告
        self._save_detailed_report()
    
    def _save_detailed_report(self):
        """保存详细报告"""
        report_file = 'comprehensive_evaluation_report.json'
        
        # 准备详细数据
        detailed_report = {
            'evaluation_time': time.strftime('%Y-%m-%d %H:%M:%S'),
            'summary': self.results,
            'recommendations': self._generate_recommendations()
        }
        
        with open(report_file, 'w', encoding='utf-8') as f:
            json.dump(detailed_report, f, indent=2, ensure_ascii=False)
        
        print(f"\n详细报告已保存到: {report_file}")
    
    def _generate_recommendations(self) -> List[str]:
        """生成改进建议"""
        recommendations = []
        
        # 分析结果并生成建议
        if self.results['failed_generation'] > 0:
            recommendations.append("修复生成失败的问题，确保所有DSL文件都能成功生成测试")
        
        # 检查常见问题
        for issue, count in self.results['common_issues'].items():
            if 'size(' in issue and count > 3:
                recommendations.append("改进集合类型的识别和生成，确保正确处理array/set类型")
            elif '>=' in issue or '<=' in issue:
                recommendations.append("优化边界值生成策略，确保生成的值满足范围约束")
            elif 'Type mismatch' in issue:
                recommendations.append("增强类型推断系统，确保生成正确类型的数据")
        
        # 检查通过率
        total_tests = sum(m.get('total_tests', 0) for m in self.results['test_quality'].values() if 'error' not in m)
        total_passed = sum(m.get('passed', 0) for m in self.results['test_quality'].values() if 'error' not in m)
        
        if total_tests > 0:
            overall_pass_rate = (total_passed / total_tests) * 100
            if overall_pass_rate < 80:
                recommendations.append(f"当前总体通过率仅为 {overall_pass_rate:.1f}%，需要重点改进约束处理逻辑")
        
        return recommendations


def analyze_specific_issues():
    """分析具体问题并生成改进方案"""
    print("\n" + "=" * 80)
    print("具体问题分析")
    print("=" * 80)
    
    # 读取一个测试文件分析具体问题
    test_file = 'improved_shopping_cart_tests.json'
    if os.path.exists(test_file):
        with open(test_file, 'r') as f:
            test_data = json.load(f)
        
        print(f"\n分析文件: {test_file}")
        
        # 分析类型问题
        type_issues = []
        for test in test_data.get('tests', []):
            test_data_dict = test.get('test_data', {})
            for key, value in test_data_dict.items():
                # 检查应该是集合但生成为字符串的情况
                if 'categories' in key and isinstance(value, str):
                    type_issues.append(f"{test['test_name']}: {key} 应该是数组但生成为字符串")
                elif 'items' in key and key != 'items' and isinstance(value, str):
                    type_issues.append(f"{test['test_name']}: {key} 可能应该是数组")
        
        if type_issues:
            print("\n类型推断问题:")
            for issue in type_issues[:5]:
                print(f"  - {issue}")
    
    print("\n建议的改进优先级:")
    print("1. 修复集合类型推断 - 确保array/set类型正确生成")
    print("2. 改进边界值生成 - 使用Z3求解器生成精确的边界值")
    print("3. 增强约束解析 - 从DSL中提取更准确的类型信息")
    print("4. 优化负面测试 - 生成更有针对性的约束违反")


def main():
    """主函数"""
    evaluator = ComprehensiveTestEvaluator()
    
    print("开始综合评估...")
    evaluator.run_comprehensive_evaluation()
    
    # 分析具体问题
    analyze_specific_issues()
    
    print("\n评估完成！")


if __name__ == '__main__':
    main()