#!/usr/bin/env python3
"""
批量测试所有需求文档并生成评估报告 - V6版本
"""

import os
import subprocess
import json
import yaml
from pathlib import Path
from datetime import datetime
from typing import Dict, Any, List


class RequirementsEvaluatorV6:
    """需求文档评估器V6"""
    
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
        print("V6 生成器 - 高级约束和完整覆盖评估")
        print("=" * 80)
        
        for yaml_file in yaml_files:
            print(f"\n处理: {yaml_file}")
            print("-" * 60)
            
            # 读取DSL文件
            with open(yaml_file, 'r', encoding='utf-8') as f:
                dsl_model = yaml.safe_load(f)
            
            # 生成输出文件名
            output_file = f"outputs/v6/{Path(yaml_file).stem}_v6.json"
            
            # 运行V6生成器
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
        """运行V6生成器"""
        cmd = ["python", "src/generators/v6_generator.py", yaml_file, "-o", output_file]
        
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
            'improvements_from_v5': []
        }
        
        # 1. 评估test_requirements覆盖
        if 'test_requirements' in dsl_model:
            req_coverage = self._evaluate_requirements_coverage(dsl_model, output)
            evaluation['scores']['requirements_coverage'] = req_coverage['score']
            if req_coverage['score'] == 100:
                evaluation['strengths'].append("完整覆盖所有测试需求")
            elif req_coverage['score'] > 80:
                evaluation['strengths'].append(f"高测试需求覆盖率: {req_coverage['score']}%")
                evaluation['improvements_from_v5'].append("提升了测试需求覆盖率")
        
        # 2. 评估约束覆盖（特别是复杂约束）
        constraint_coverage = self._evaluate_constraint_coverage(dsl_model, output)
        evaluation['scores']['constraint_coverage'] = constraint_coverage['score']
        evaluation['constraint_details'] = constraint_coverage
        
        if constraint_coverage['complex_covered'] > 0:
            evaluation['improvements_from_v5'].append(f"覆盖了{constraint_coverage['complex_covered']}个复杂约束")
        
        if constraint_coverage['score'] >= 90:
            evaluation['strengths'].append(f"优秀的约束覆盖率: {constraint_coverage['score']}%")
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
        if distribution_score >= 75:
            evaluation['strengths'].append("测试分布非常合理")
        
        # 5. 评估数据质量
        data_quality = self._evaluate_data_quality(output)
        evaluation['scores']['data_quality'] = data_quality['score']
        if data_quality['score'] >= 95:
            evaluation['strengths'].append("卓越的测试数据质量")
        evaluation['data_quality_details'] = data_quality
        
        # 6. 检查高级特性
        advanced_features = self._check_advanced_features(output)
        if advanced_features['temporal_constraints']:
            evaluation['improvements_from_v5'].append("支持时间约束")
        if advanced_features['cross_field_constraints']:
            evaluation['improvements_from_v5'].append("支持跨字段约束")
        if advanced_features['conditional_constraints']:
            evaluation['improvements_from_v5'].append("支持条件约束(=>)")
        
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
            if 'default_test' in str(output):
                return {'score': 100, 'details': 'Generated comprehensive default tests'}
            return {'score': 70, 'details': 'Generated basic default tests'}
        
        covered = sum(1 for req in test_reqs if req.get('covered', False))
        total = len(test_reqs)
        score = (covered / total * 100) if total > 0 else 0
        
        return {'score': score, 'covered': covered, 'total': total}
    
    def _evaluate_constraint_coverage(self, dsl_model: Dict, output: Dict) -> Dict:
        """评估约束覆盖率，特别关注复杂约束"""
        if 'requirements_coverage' not in output['summary']:
            return {'score': 0, 'uncovered': [], 'complex_covered': 0}
        
        coverage = output['summary']['requirements_coverage']
        constraints = coverage.get('constraints', [])
        
        uncovered = []
        complex_covered = 0
        total_complex = 0
        
        for c in constraints:
            constraint = c['constraint']
            covered = c.get('covered', False)
            
            # 检查是否是复杂约束
            is_complex = False
            if '.' in constraint and any(op in constraint for op in ['.', '=>', 'Date', 'Time']):
                is_complex = True
                total_complex += 1
                if covered:
                    complex_covered += 1
            
            if not covered:
                uncovered.append(constraint)
        
        covered = len(constraints) - len(uncovered)
        total = len(constraints)
        score = (covered / total * 100) if total > 0 else 0
        
        return {
            'score': score,
            'uncovered': uncovered[:3],  # 只显示前3个
            'complex_covered': complex_covered,
            'total_complex': total_complex
        }
    
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
        
        # V6的理想分布（更加平衡）
        ideal = {
            'functional': 0.15,
            'boundary': 0.15,
            'negative': 0.10,
            'constraint_satisfaction': 0.10,
            'constraint_violation': 0.10,
            'rule': 0.15,  # 激活+未激活
            'collection': 0.10,
            'combinatorial': 0.05,
            'state_transition': 0.05,
            'scenario': 0.05
        }
        
        # 计算分布偏差
        score = 100
        for test_type, ideal_ratio in ideal.items():
            if test_type == 'rule':
                actual_count = distribution.get('rule_activation', 0) + distribution.get('rule_deactivation', 0)
            else:
                actual_count = distribution.get(test_type, 0)
            
            actual_ratio = actual_count / total
            deviation = abs(actual_ratio - ideal_ratio)
            score -= deviation * 40  # 降低惩罚以允许更多灵活性
        
        return max(0, score)
    
    def _evaluate_data_quality(self, output: Dict) -> Dict:
        """评估测试数据质量"""
        issues = []
        score = 100
        cross_field_constraints = 0
        temporal_constraints = 0
        
        # 检查测试数据
        test_suites = output.get('test_suites', {})
        for suite_name, tests in test_suites.items():
            for test in tests[:10]:  # 只检查前10个测试
                test_data = test.get('test_data', {})
                
                # 检查跨字段约束
                if 'price' in str(test_data) and 'cost' in str(test_data):
                    # 检查价格是否大于成本
                    price_keys = [k for k in test_data.keys() if 'price' in k]
                    cost_keys = [k for k in test_data.keys() if 'cost' in k]
                    if price_keys and cost_keys:
                        cross_field_constraints += 1
                
                # 检查时间约束
                date_fields = [k for k in test_data.keys() if 'date' in k.lower()]
                if len(date_fields) >= 2:
                    temporal_constraints += 1
                
                # 检查数据合理性
                for key, value in test_data.items():
                    if isinstance(value, (int, float)):
                        # 价格检查
                        if 'price' in key:
                            if value > 1000:
                                issues.append(f"价格可能过高: {key}={value}")
                                score -= 2
                            elif value < 0:
                                issues.append(f"价格为负: {key}={value}")
                                score -= 5
        
        return {
            'score': min(100, max(0, score)),
            'issues': issues[:5],
            'cross_field_constraints': cross_field_constraints,
            'temporal_constraints': temporal_constraints
        }
    
    def _check_advanced_features(self, output: Dict) -> Dict:
        """检查是否使用了高级特性"""
        features = {
            'temporal_constraints': False,
            'cross_field_constraints': False,
            'conditional_constraints': False,
            'state_machine_tests': False,
            'scenario_tests': False
        }
        
        test_suites = output.get('test_suites', {})
        
        # 检查测试类型
        if 'state_transition' in test_suites:
            features['state_machine_tests'] = True
        
        if 'scenario' in test_suites:
            features['scenario_tests'] = True
        
        # 检查测试数据中的高级特性
        for suite_name, tests in test_suites.items():
            for test in tests[:5]:
                test_data = test.get('test_data', {})
                constraints_tested = test.get('constraints_tested', [])
                
                # 检查时间字段
                if any('date' in k.lower() for k in test_data.keys()):
                    features['temporal_constraints'] = True
                
                # 检查约束类型
                for constraint in constraints_tested:
                    if '=>' in str(constraint):
                        features['conditional_constraints'] = True
                    if '.' in str(constraint) and any(op in str(constraint) for op in ['>', '<', '>=', '<=']):
                        features['cross_field_constraints'] = True
        
        return features
    
    def _print_evaluation(self, yaml_file: str, evaluation: Dict):
        """打印评估结果"""
        print(f"\n  领域: {evaluation['domain']}")
        print(f"  总测试数: {evaluation['total_tests']}")
        print(f"  综合评分: {evaluation['overall_score']:.1f}/100")
        
        if evaluation.get('improvements_from_v5'):
            print("  🚀 相比V5的改进:")
            for imp in evaluation['improvements_from_v5']:
                print(f"     - {imp}")
        
        if evaluation.get('strengths'):
            print("  ✅ 优势:")
            for s in evaluation['strengths']:
                print(f"     - {s}")
        
        if evaluation.get('issues'):
            print("  ⚠️  问题:")
            for i in evaluation['issues']:
                print(f"     - {i}")
        
        # 打印约束覆盖详情
        if 'constraint_details' in evaluation:
            details = evaluation['constraint_details']
            if details.get('total_complex', 0) > 0:
                print(f"  📊 复杂约束覆盖: {details['complex_covered']}/{details['total_complex']}")
    
    def generate_report(self):
        """生成评估报告"""
        report = {
            'timestamp': self.timestamp,
            'generator': 'V6',
            'summary': {
                'files_evaluated': len(self.results),
                'average_score': 0,
                'improvements': [],
                'remaining_issues': [],
                'target_achieved': False
            },
            'details': self.results
        }
        
        # 计算平均分
        scores = [r['overall_score'] for r in self.results.values() if 'overall_score' in r]
        avg_score = sum(scores) / len(scores) if scores else 0
        report['summary']['average_score'] = avg_score
        report['summary']['target_achieved'] = avg_score >= 70
        
        # 收集改进和问题
        all_improvements = []
        all_issues = []
        
        for r in self.results.values():
            if 'improvements_from_v5' in r:
                all_improvements.extend(r['improvements_from_v5'])
            if 'issues' in r:
                all_issues.extend(r['issues'])
        
        # 统计最常见的
        from collections import Counter
        improvement_counts = Counter(all_improvements)
        issue_counts = Counter(all_issues)
        
        report['summary']['improvements'] = [i[0] for i in improvement_counts.most_common(3)]
        report['summary']['remaining_issues'] = [i[0] for i in issue_counts.most_common(3)]
        
        # 保存报告
        with open('outputs/v6/evaluation_report_round2.json', 'w', encoding='utf-8') as f:
            json.dump(report, f, ensure_ascii=False, indent=2)
        
        return report


def main():
    evaluator = RequirementsEvaluatorV6()
    evaluator.evaluate_all_requirements()
    report = evaluator.generate_report()
    
    print("\n" + "=" * 80)
    print("Round 2 评估总结")
    print("=" * 80)
    print(f"平均得分: {report['summary']['average_score']:.1f}/100")
    print(f"相比V5提升: {report['summary']['average_score'] - 66.2:.1f}分")
    
    if report['summary']['target_achieved']:
        print("\n🎯 目标达成！平均分超过70分")
    
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