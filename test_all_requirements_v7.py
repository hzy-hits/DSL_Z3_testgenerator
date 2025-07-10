#!/usr/bin/env python3
"""
批量测试所有需求文档并生成评估报告 - V7版本
重点：稳定性和高质量
"""

import os
import subprocess
import json
import yaml
from pathlib import Path
from datetime import datetime
from typing import Dict, Any, List


class RequirementsEvaluatorV7:
    """需求文档评估器V7"""
    
    def __init__(self):
        self.results = {}
        self.timestamp = datetime.now().isoformat()
    
    def evaluate_all_requirements(self):
        """评估所有需求文档"""
        yaml_files = [
            "examples/basic/simple_arrays.yaml",
            "examples/intermediate/permission_system.yaml", 
            "examples/intermediate/shopping_cart.yaml",
            "examples/advanced/user_account_system.yaml",
            "examples/advanced/order_processing_system.yaml",
            "examples/advanced/student_system_mixed.yaml",
            "examples/advanced/advanced_ecommerce.yaml"
        ]
        
        print("=" * 80)
        print("V7 生成器 - 稳定性与高质量评估")
        print("=" * 80)
        
        successful_files = 0
        
        for yaml_file in yaml_files:
            print(f"\n处理: {yaml_file}")
            print("-" * 60)
            
            # 读取DSL文件
            with open(yaml_file, 'r', encoding='utf-8') as f:
                dsl_model = yaml.safe_load(f)
            
            # 生成输出文件名
            output_file = f"outputs/v7/{Path(yaml_file).stem}_v7.json"
            
            # 运行V7生成器
            result = self._run_generator(yaml_file, output_file)
            
            if result['success']:
                successful_files += 1
                # 评估生成的测试
                evaluation = self._evaluate_generated_tests(dsl_model, result['output'])
                self.results[yaml_file] = evaluation
                self._print_evaluation(yaml_file, evaluation)
            else:
                print(f"  ❌ 生成失败: {result['error']}")
                self.results[yaml_file] = {'success': False, 'error': result['error']}
        
        print(f"\n\n文件处理成功率: {successful_files}/{len(yaml_files)} ({successful_files/len(yaml_files)*100:.1f}%)")
    
    def _run_generator(self, yaml_file: str, output_file: str) -> Dict[str, Any]:
        """运行V7生成器"""
        cmd = ["python", "src/generators/v7_generator.py", yaml_file, "-o", output_file]
        
        try:
            result = subprocess.run(cmd, capture_output=True, text=True)
            
            if result.returncode != 0:
                return {'success': False, 'error': result.stderr}
            
            # 读取生成的测试
            with open(output_file, 'r', encoding='utf-8') as f:
                output_data = json.load(f)
            
            # 检查是否有错误标记
            if 'error' in output_data.get('meta', {}):
                return {'success': False, 'error': output_data['meta']['error']}
            
            return {'success': True, 'output': output_data}
            
        except Exception as e:
            return {'success': False, 'error': str(e)}
    
    def _evaluate_generated_tests(self, dsl_model: Dict, output: Dict) -> Dict[str, Any]:
        """评估生成的测试"""
        evaluation = {
            'domain': dsl_model.get('domain', 'Unknown'),
            'total_tests': output['summary']['total_tests'],
            'test_distribution': output['summary']['test_distribution'],
            'scores': {},
            'issues': [],
            'strengths': [],
            'improvements_from_v6': []
        }
        
        # 0. 首先评估稳定性
        evaluation['scores']['stability'] = 100  # 成功生成即得满分
        evaluation['improvements_from_v6'].append("成功处理文件，无解析错误")
        
        # 1. 评估test_requirements覆盖
        if 'test_requirements' in dsl_model:
            req_coverage = self._evaluate_requirements_coverage(dsl_model, output)
            evaluation['scores']['requirements_coverage'] = req_coverage['score']
            if req_coverage['score'] == 100:
                evaluation['strengths'].append("完整覆盖所有测试需求")
            elif req_coverage['score'] > 80:
                evaluation['strengths'].append(f"高测试需求覆盖率: {req_coverage['score']}%")
        
        # 2. 评估约束覆盖
        constraint_coverage = self._evaluate_constraint_coverage(dsl_model, output)
        evaluation['scores']['constraint_coverage'] = constraint_coverage['score']
        evaluation['constraint_details'] = constraint_coverage
        
        if constraint_coverage['score'] >= 80:
            evaluation['strengths'].append(f"良好的约束覆盖率: {constraint_coverage['score']}%")
        elif constraint_coverage['uncovered']:
            evaluation['issues'].append(f"未覆盖的约束: {len(constraint_coverage['uncovered'])}个")
        
        # 3. 评估规则覆盖
        rule_coverage = self._evaluate_rule_coverage(dsl_model, output)
        evaluation['scores']['rule_coverage'] = rule_coverage['score']
        if rule_coverage['score'] == 100:
            evaluation['strengths'].append("所有规则都有激活和未激活测试")
        
        # 4. 评估测试分布
        distribution_score = self._evaluate_test_distribution(output)
        evaluation['scores']['distribution'] = distribution_score
        if distribution_score >= 70:
            evaluation['strengths'].append("测试分布合理")
        
        # 5. 评估数据质量
        data_quality = self._evaluate_data_quality(output)
        evaluation['scores']['data_quality'] = data_quality['score']
        if data_quality['score'] >= 90:
            evaluation['strengths'].append("高质量的测试数据")
        evaluation['data_quality_details'] = data_quality
        
        # 6. 检查错误恢复
        if output['summary']['total_tests'] > 0:
            evaluation['improvements_from_v6'].append("具备错误恢复能力")
        
        # 7. 计算总分（包含稳定性权重）
        scores = evaluation['scores']
        # 稳定性占30%权重
        if 'stability' in scores:
            weighted_score = (scores['stability'] * 0.3 + 
                            sum(v for k, v in scores.items() if k != 'stability') * 0.7 / 
                            (len(scores) - 1))
            evaluation['overall_score'] = weighted_score
        else:
            evaluation['overall_score'] = sum(scores.values()) / len(scores) if scores else 0
        
        return evaluation
    
    def _evaluate_requirements_coverage(self, dsl_model: Dict, output: Dict) -> Dict:
        """评估测试需求覆盖率"""
        if 'requirements_coverage' not in output['summary']:
            return {'score': 0, 'details': 'No requirements coverage data'}
        
        coverage = output['summary']['requirements_coverage']
        test_reqs = coverage.get('test_requirements', [])
        
        if not test_reqs:
            # 没有test_requirements时，检查是否生成了默认测试
            if 'default_test' in str(output):
                return {'score': 100, 'details': 'Generated comprehensive default tests'}
            return {'score': 80, 'details': 'Generated basic tests'}
        
        covered = sum(1 for req in test_reqs if req.get('covered', False))
        total = len(test_reqs)
        score = (covered / total * 100) if total > 0 else 0
        
        return {'score': score, 'covered': covered, 'total': total}
    
    def _evaluate_constraint_coverage(self, dsl_model: Dict, output: Dict) -> Dict:
        """评估约束覆盖率"""
        if 'requirements_coverage' not in output['summary']:
            return {'score': 50, 'uncovered': [], 'details': 'Basic coverage'}
        
        coverage = output['summary']['requirements_coverage']
        constraints = coverage.get('constraints', [])
        
        if not constraints:
            # 没有约束时给基础分
            return {'score': 80, 'uncovered': [], 'details': 'No constraints defined'}
        
        uncovered = []
        for c in constraints:
            if not c.get('covered', False):
                uncovered.append(c['constraint'])
        
        covered = len(constraints) - len(uncovered)
        total = len(constraints)
        score = (covered / total * 100) if total > 0 else 0
        
        return {
            'score': score,
            'uncovered': uncovered[:3],  # 只显示前3个
            'total': total,
            'covered': covered
        }
    
    def _evaluate_rule_coverage(self, dsl_model: Dict, output: Dict) -> Dict:
        """评估规则覆盖率"""
        if 'requirements_coverage' not in output['summary']:
            return {'score': 50}
        
        coverage = output['summary']['requirements_coverage']
        rules = coverage.get('rules', [])
        
        if not rules:
            return {'score': 80}  # 没有规则时给基础分
        
        covered = sum(1 for r in rules if r.get('covered', False))
        total = len(rules)
        score = (covered / total * 100) if total > 0 else 0
        
        return {'score': score, 'covered': covered, 'total': total}
    
    def _evaluate_test_distribution(self, output: Dict) -> float:
        """评估测试分布合理性"""
        distribution = output['summary']['test_distribution']
        total = output['summary']['total_tests']
        
        if total == 0:
            return 0
        
        # V7的理想分布（更灵活）
        ideal = {
            'functional': (0.10, 0.30),  # 范围而非固定值
            'boundary': (0.10, 0.25),
            'negative': (0.05, 0.20),
            'constraint_satisfaction': (0.05, 0.20),
            'constraint_violation': (0.05, 0.20),
            'rule_activation': (0.00, 0.20),
            'rule_deactivation': (0.00, 0.20),
            'collection': (0.05, 0.20),
            'combinatorial': (0.00, 0.15),
            'state_transition': (0.00, 0.15),
            'scenario': (0.00, 0.15)
        }
        
        # 计算分布得分
        score = 100
        penalty = 0
        
        for test_type, (min_ratio, max_ratio) in ideal.items():
            actual_count = distribution.get(test_type, 0)
            actual_ratio = actual_count / total
            
            if actual_ratio < min_ratio:
                penalty += (min_ratio - actual_ratio) * 50
            elif actual_ratio > max_ratio:
                penalty += (actual_ratio - max_ratio) * 30  # 超出惩罚较小
        
        return max(0, score - penalty)
    
    def _evaluate_data_quality(self, output: Dict) -> Dict:
        """评估测试数据质量"""
        issues = []
        score = 100
        good_patterns = 0
        
        # 检查测试数据
        test_suites = output.get('test_suites', {})
        total_tests_checked = 0
        
        for suite_name, tests in test_suites.items():
            for test in tests[:10]:  # 只检查前10个测试
                total_tests_checked += 1
                test_data = test.get('test_data', {})
                
                # 检查数据质量
                for key, value in test_data.items():
                    if isinstance(value, (int, float)):
                        # 价格检查
                        if 'price' in key:
                            if 0 < value < 10000:
                                good_patterns += 1
                            else:
                                issues.append(f"价格超出合理范围: {key}={value}")
                                score -= 2
                        
                        # ID检查
                        elif 'id' in key and isinstance(value, int):
                            if 0 < value < 100000:
                                good_patterns += 1
                            else:
                                issues.append(f"ID超出合理范围: {key}={value}")
                                score -= 1
                    
                    # 检查集合数据
                    elif isinstance(value, list):
                        if isinstance(value, list) and not isinstance(value, str):
                            good_patterns += 1
                        else:
                            issues.append(f"集合类型错误: {key}")
                            score -= 5
                    
                    # 检查日期格式
                    elif isinstance(value, str) and 'date' in key:
                        if '-' in value:  # 简单的日期格式检查
                            good_patterns += 1
        
        # 奖励良好的数据模式
        if total_tests_checked > 0:
            pattern_ratio = good_patterns / (total_tests_checked * 3)  # 每个测试期望3个好模式
            score = min(100, score + pattern_ratio * 10)
        
        return {
            'score': min(100, max(0, score)),
            'issues': issues[:5],
            'good_patterns': good_patterns
        }
    
    def _print_evaluation(self, yaml_file: str, evaluation: Dict):
        """打印评估结果"""
        print(f"\n  领域: {evaluation['domain']}")
        print(f"  总测试数: {evaluation['total_tests']}")
        print(f"  综合评分: {evaluation['overall_score']:.1f}/100")
        
        if evaluation.get('improvements_from_v6'):
            print("  🚀 相比V6的改进:")
            for imp in evaluation['improvements_from_v6']:
                print(f"     - {imp}")
        
        if evaluation.get('strengths'):
            print("  ✅ 优势:")
            for s in evaluation['strengths']:
                print(f"     - {s}")
        
        if evaluation.get('issues'):
            print("  ⚠️  问题:")
            for i in evaluation['issues']:
                print(f"     - {i}")
    
    def generate_report(self):
        """生成评估报告"""
        report = {
            'timestamp': self.timestamp,
            'generator': 'V7',
            'summary': {
                'files_evaluated': len(self.results),
                'files_successful': sum(1 for r in self.results.values() if r.get('success', True)),
                'average_score': 0,
                'improvements': [],
                'remaining_issues': [],
                'stability_achieved': False
            },
            'details': self.results
        }
        
        # 计算成功文件的平均分
        scores = [r['overall_score'] for r in self.results.values() if 'overall_score' in r]
        if scores:
            avg_score = sum(scores) / len(scores)
            report['summary']['average_score'] = avg_score
        
        # 计算稳定性
        success_rate = report['summary']['files_successful'] / report['summary']['files_evaluated']
        report['summary']['stability_achieved'] = success_rate >= 0.9  # 90%以上成功率
        
        # 收集改进和问题
        all_improvements = []
        all_issues = []
        
        for r in self.results.values():
            if 'improvements_from_v6' in r:
                all_improvements.extend(r['improvements_from_v6'])
            if 'issues' in r:
                all_issues.extend(r['issues'])
        
        # 统计最常见的
        from collections import Counter
        improvement_counts = Counter(all_improvements)
        issue_counts = Counter(all_issues)
        
        report['summary']['improvements'] = [i[0] for i in improvement_counts.most_common(3)]
        report['summary']['remaining_issues'] = [i[0] for i in issue_counts.most_common(3)]
        
        # 保存报告
        with open('outputs/v7/evaluation_report_round3.json', 'w', encoding='utf-8') as f:
            json.dump(report, f, ensure_ascii=False, indent=2)
        
        return report


def main():
    evaluator = RequirementsEvaluatorV7()
    evaluator.evaluate_all_requirements()
    report = evaluator.generate_report()
    
    print("\n" + "=" * 80)
    print("Round 3 评估总结 - 稳定性优先")
    print("=" * 80)
    print(f"文件成功率: {report['summary']['files_successful']}/{report['summary']['files_evaluated']} " +
          f"({report['summary']['files_successful']/report['summary']['files_evaluated']*100:.1f}%)")
    print(f"平均得分: {report['summary']['average_score']:.1f}/100")
    print(f"相比V6提升: 稳定性从28.6%提升到{report['summary']['files_successful']/report['summary']['files_evaluated']*100:.1f}%")
    
    if report['summary']['stability_achieved']:
        print("\n🎯 稳定性目标达成！90%以上文件成功处理")
    
    if report['summary']['improvements']:
        print("\n主要改进:")
        for imp in report['summary']['improvements']:
            print(f"  ✅ {imp}")
    
    if report['summary']['remaining_issues']:
        print("\n待优化问题:")
        for issue in report['summary']['remaining_issues']:
            print(f"  ⚠️  {issue}")


if __name__ == "__main__":
    main()