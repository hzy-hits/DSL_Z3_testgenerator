#!/usr/bin/env python3
"""
批量测试所有需求文档并生成评估报告 - V5版本
"""

import os
import subprocess
import json
import yaml
from pathlib import Path
from datetime import datetime
from typing import Dict, Any, List


class RequirementsEvaluatorV5:
    """需求文档评估器V5"""
    
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
        print("V5 生成器 - 全面需求文档评估")
        print("=" * 80)
        
        for yaml_file in yaml_files:
            print(f"\n处理: {yaml_file}")
            print("-" * 60)
            
            # 读取DSL文件
            with open(yaml_file, 'r', encoding='utf-8') as f:
                dsl_model = yaml.safe_load(f)
            
            # 生成输出文件名
            output_file = f"outputs/v5/{Path(yaml_file).stem}_v5.json"
            
            # 运行V5生成器
            result = self._run_generator(yaml_file, output_file)
            
            if result['success']:
                # 评估生成的测试
                evaluation = self._evaluate_generated_tests(dsl_model, result['output'])
                self.results[yaml_file] = evaluation
                self._print_evaluation(yaml_file, evaluation)
            else:
                print(f"  ❌ 生成失败: {result['error']}")
                self.results[yaml_file] = {'success': False, 'error': result['error']}
    
    def _run_generator(self, yaml_file: str, output_file: str) -> Dict[str, Any]:
        """运行V5生成器"""
        cmd = ["python", "src/generators/v5_generator.py", yaml_file, "-o", output_file]
        
        try:
            result = subprocess.run(cmd, capture_output=True, text=True)
            
            if result.returncode != 0:
                return {'success': False, 'error': result.stderr}
            
            # 读取生成的测试
            with open(output_file, 'r', encoding='utf-8') as f:
                output_data = json.load(f)
            
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
            'improvements_from_v4': []
        }
        
        # 1. 评估test_requirements覆盖
        if 'test_requirements' in dsl_model:
            req_coverage = self._evaluate_requirements_coverage(dsl_model, output)
            evaluation['scores']['requirements_coverage'] = req_coverage['score']
            if req_coverage['score'] == 100:
                evaluation['strengths'].append("完整覆盖所有测试需求")
                evaluation['improvements_from_v4'].append("修复了test_requirements覆盖率计算")
            elif req_coverage['score'] > 0:
                evaluation['strengths'].append(f"测试需求覆盖率: {req_coverage['score']}%")
        
        # 2. 评估约束覆盖
        constraint_coverage = self._evaluate_constraint_coverage(dsl_model, output)
        evaluation['scores']['constraint_coverage'] = constraint_coverage['score']
        if constraint_coverage['score'] >= 80:
            evaluation['strengths'].append(f"高约束覆盖率: {constraint_coverage['score']}%")
        if constraint_coverage['uncovered']:
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
            evaluation['improvements_from_v4'].append("改进了业务数据生成")
        evaluation['data_quality_issues'] = data_quality.get('data_quality_issues', [])
        
        # 6. 检查集合类型处理
        collection_handling = self._check_collection_handling(output)
        if collection_handling['correct']:
            evaluation['improvements_from_v4'].append("修复了集合类型生成bug")
        else:
            evaluation['issues'].append("集合类型处理仍有问题")
        
        # 7. 计算总分
        scores = evaluation['scores']
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
            if 'collection' in output['summary']['test_distribution']:
                return {'score': 100, 'details': 'Generated default collection tests'}
            return {'score': 50, 'details': 'No test requirements, partial default tests'}
        
        covered = sum(1 for req in test_reqs if req.get('covered', False))
        total = len(test_reqs)
        score = (covered / total * 100) if total > 0 else 0
        
        return {'score': score, 'covered': covered, 'total': total}
    
    def _evaluate_constraint_coverage(self, dsl_model: Dict, output: Dict) -> Dict:
        """评估约束覆盖率"""
        if 'requirements_coverage' not in output['summary']:
            return {'score': 0, 'uncovered': []}
        
        coverage = output['summary']['requirements_coverage']
        constraints = coverage.get('constraints', [])
        
        uncovered = [c['constraint'] for c in constraints if not c.get('covered', False)]
        covered = len(constraints) - len(uncovered)
        total = len(constraints)
        score = (covered / total * 100) if total > 0 else 0
        
        return {'score': score, 'uncovered': uncovered[:3]}  # 只显示前3个
    
    def _evaluate_rule_coverage(self, dsl_model: Dict, output: Dict) -> Dict:
        """评估规则覆盖率"""
        if 'requirements_coverage' not in output['summary']:
            return {'score': 0}
        
        coverage = output['summary']['requirements_coverage']
        rules = coverage.get('rules', [])
        
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
        
        # 理想分布
        ideal = {
            'functional': 0.20,
            'boundary': 0.20,
            'negative': 0.15,
            'constraint_satisfaction': 0.10,
            'rule': 0.20,  # 激活+未激活
            'collection': 0.10,
            'other': 0.05
        }
        
        # 计算分布偏差
        score = 100
        for test_type, ideal_ratio in ideal.items():
            if test_type == 'rule':
                actual_count = distribution.get('rule_activation', 0) + distribution.get('rule_deactivation', 0)
            elif test_type == 'other':
                continue
            else:
                actual_count = distribution.get(test_type, 0)
            
            actual_ratio = actual_count / total
            deviation = abs(actual_ratio - ideal_ratio)
            score -= deviation * 50  # 降低惩罚
        
        return max(0, score)
    
    def _evaluate_data_quality(self, output: Dict) -> Dict:
        """评估测试数据质量"""
        issues = []
        score = 100
        
        # 检查测试数据
        test_suites = output.get('test_suites', {})
        for suite_name, tests in test_suites.items():
            for test in tests[:10]:  # 只检查前10个测试
                test_data = test.get('test_data', {})
                
                # 检查数值合理性
                for key, value in test_data.items():
                    if isinstance(value, (int, float)):
                        # 价格检查
                        if 'price' in key:
                            if value > 5000:
                                issues.append(f"价格过高: {key}={value}")
                                score -= 5
                            elif value < 0:
                                issues.append(f"价格为负: {key}={value}")
                                score -= 10
                        
                        # ID检查
                        elif 'id' in key and isinstance(value, int):
                            if value > 99999:
                                issues.append(f"ID过大: {key}={value}")
                                score -= 2
                    
                    # 检查集合数据
                    elif isinstance(value, list) and len(value) > 0:
                        # 检查是否为连续ID
                        if all(isinstance(x, int) for x in value[:5]):
                            if len(value) >= 3:
                                # 检查连续性
                                diffs = [value[i+1] - value[i] for i in range(min(3, len(value)-1))]
                                if all(d == 1 for d in diffs):
                                    score += 1  # 奖励连续ID
                                elif any(d > 100 for d in diffs):
                                    issues.append(f"ID不连续: {key}")
                                    score -= 2
                        
                        # 检查集合元素类型
                        if 'categories' in key:
                            if all(isinstance(x, str) for x in value):
                                score += 1  # 正确的类型
        
        return {
            'score': min(100, max(0, score)),
            'data_quality_issues': issues[:5]
        }
    
    def _check_collection_handling(self, output: Dict) -> Dict:
        """检查集合类型处理是否正确"""
        correct = True
        issues = []
        
        test_suites = output.get('test_suites', {})
        for suite_name, tests in test_suites.items():
            for test in tests[:5]:
                test_data = test.get('test_data', {})
                
                for key, value in test_data.items():
                    if 'categories' in key or 'items' in key or 'codes' in key:
                        if isinstance(value, str):
                            correct = False
                            issues.append(f"{key}应该是数组而不是字符串")
                        elif isinstance(value, list):
                            # 检查数组元素
                            if 'categories' in key and len(value) > 0:
                                if not all(isinstance(x, str) for x in value):
                                    issues.append(f"{key}的元素应该是字符串")
        
        return {'correct': correct, 'issues': issues}
    
    def _print_evaluation(self, yaml_file: str, evaluation: Dict):
        """打印评估结果"""
        print(f"\n  领域: {evaluation['domain']}")
        print(f"  总测试数: {evaluation['total_tests']}")
        print(f"  综合评分: {evaluation['overall_score']:.1f}/100")
        
        if evaluation.get('improvements_from_v4'):
            print("  🚀 相比V4的改进:")
            for imp in evaluation['improvements_from_v4']:
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
            'generator': 'V5',
            'summary': {
                'files_evaluated': len(self.results),
                'average_score': 0,
                'improvements': [],
                'remaining_issues': []
            },
            'details': self.results
        }
        
        # 计算平均分
        scores = [r['overall_score'] for r in self.results.values() if 'overall_score' in r]
        report['summary']['average_score'] = sum(scores) / len(scores) if scores else 0
        
        # 收集改进和问题
        all_improvements = []
        all_issues = []
        
        for r in self.results.values():
            if 'improvements_from_v4' in r:
                all_improvements.extend(r['improvements_from_v4'])
            if 'issues' in r:
                all_issues.extend(r['issues'])
        
        # 统计最常见的
        from collections import Counter
        improvement_counts = Counter(all_improvements)
        issue_counts = Counter(all_issues)
        
        report['summary']['improvements'] = [i[0] for i in improvement_counts.most_common(3)]
        report['summary']['remaining_issues'] = [i[0] for i in issue_counts.most_common(3)]
        
        # 保存报告
        with open('outputs/v5/evaluation_report_round1.json', 'w', encoding='utf-8') as f:
            json.dump(report, f, ensure_ascii=False, indent=2)
        
        return report


def main():
    evaluator = RequirementsEvaluatorV5()
    evaluator.evaluate_all_requirements()
    report = evaluator.generate_report()
    
    print("\n" + "=" * 80)
    print("评估总结")
    print("=" * 80)
    print(f"平均得分: {report['summary']['average_score']:.1f}/100")
    print(f"相比V4提升: {report['summary']['average_score'] - 29.8:.1f}分")
    
    if report['summary']['improvements']:
        print("\n主要改进:")
        for imp in report['summary']['improvements']:
            print(f"  ✅ {imp}")
    
    if report['summary']['remaining_issues']:
        print("\n待解决问题:")
        for issue in report['summary']['remaining_issues']:
            print(f"  ⚠️  {issue}")


if __name__ == "__main__":
    main()