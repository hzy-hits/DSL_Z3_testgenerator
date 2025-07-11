#!/usr/bin/env python3
"""
V8生成器质量评估系统
评估测试生成的各项指标并给出改进建议
"""

import json
import yaml
import os
from typing import Dict, List, Any, Tuple
from pathlib import Path
import subprocess
from datetime import datetime

class TestQualityEvaluator:
    """测试质量评估器"""
    
    def __init__(self):
        self.scores = {}
        self.issues = []
        self.improvements = []
    
    def evaluate_file(self, yaml_file: str, json_output: str) -> Dict[str, Any]:
        """评估单个文件的测试生成质量"""
        # 解析YAML获取预期
        with open(yaml_file, 'r', encoding='utf-8') as f:
            dsl_spec = yaml.safe_load(f)
        
        # 解析生成的测试
        with open(json_output, 'r', encoding='utf-8') as f:
            test_data = json.load(f)
        
        tests = test_data.get('tests', [])
        
        # 评估各个维度
        scores = {
            'completeness': self._evaluate_completeness(dsl_spec, tests),
            'coverage': self._evaluate_coverage(dsl_spec, tests),
            'data_quality': self._evaluate_data_quality(tests),
            'constraint_handling': self._evaluate_constraints(dsl_spec, tests),
            'test_diversity': self._evaluate_diversity(tests),
            'business_realism': self._evaluate_business_realism(tests)
        }
        
        # 计算总分
        total_score = sum(scores.values()) / len(scores) * 100
        
        return {
            'file': yaml_file,
            'total_score': round(total_score, 1),
            'scores': scores,
            'test_count': len(tests),
            'issues': self.issues,
            'improvements': self.improvements
        }
    
    def _evaluate_completeness(self, spec: Dict, tests: List[Dict]) -> float:
        """评估完整性：是否涵盖所有实体和属性"""
        score = 1.0
        entities = spec.get('entities', [])
        
        # 获取所有实体名
        entity_names = set()
        if isinstance(entities, list):
            for entity in entities:
                if 'name' in entity:
                    entity_names.add(entity['name'])
        
        # 检查每个实体是否有测试
        tested_entities = set()
        for test in tests:
            if 'entity' in test:
                tested_entities.add(test['entity'])
        
        if entity_names:
            coverage_ratio = len(tested_entities) / len(entity_names)
            score *= coverage_ratio
            
            missing = entity_names - tested_entities
            if missing:
                self.issues.append(f"Missing tests for entities: {missing}")
        
        # 检查属性覆盖
        attribute_coverage = self._check_attribute_coverage(spec, tests)
        score *= attribute_coverage
        
        return score
    
    def _evaluate_coverage(self, spec: Dict, tests: List[Dict]) -> float:
        """评估测试覆盖率"""
        score = 1.0
        
        # 检查测试类型分布
        test_types = {}
        for test in tests:
            test_type = test.get('test_type', 'unknown')
            test_types[test_type] = test_types.get(test_type, 0) + 1
        
        # 期望的测试类型
        expected_types = ['functional', 'boundary', 'negative', 'constraint_satisfaction']
        covered_types = sum(1 for t in expected_types if t in test_types)
        
        if expected_types:
            type_coverage = covered_types / len(expected_types)
            score *= type_coverage
            
            if type_coverage < 1.0:
                missing_types = [t for t in expected_types if t not in test_types]
                self.issues.append(f"Missing test types: {missing_types}")
        
        # 检查约束覆盖
        constraint_coverage = self._check_constraint_coverage(spec, tests)
        score *= constraint_coverage
        
        return score
    
    def _evaluate_data_quality(self, tests: List[Dict]) -> float:
        """评估数据质量"""
        if not tests:
            return 0.0
        
        quality_scores = []
        
        for test in tests:
            test_data = test.get('test_data', {})
            test_score = 1.0
            
            # 检查数据完整性
            if not test_data:
                test_score *= 0.5
                self.issues.append(f"Empty test data in {test.get('test_name')}")
            
            # 检查数据类型正确性
            for key, value in test_data.items():
                if 'items' in key and not isinstance(value, list):
                    test_score *= 0.7
                    self.issues.append(f"'{key}' should be a list in {test.get('test_name')}")
                
                if 'price' in key or 'amount' in key:
                    if not isinstance(value, (int, float)) or value < 0:
                        test_score *= 0.8
                        self.issues.append(f"Invalid price/amount in {test.get('test_name')}")
                
                if '_id' in key and isinstance(value, str):
                    test_score *= 0.9
                    self.improvements.append(f"ID fields should be numeric")
            
            quality_scores.append(test_score)
        
        return sum(quality_scores) / len(quality_scores)
    
    def _evaluate_constraints(self, spec: Dict, tests: List[Dict]) -> float:
        """评估约束处理"""
        score = 1.0
        all_constraints = []
        
        # 收集所有约束
        entities = spec.get('entities', [])
        if isinstance(entities, list):
            for entity in entities:
                constraints = entity.get('constraints', [])
                for constraint in constraints:
                    if isinstance(constraint, dict):
                        expr = constraint.get('expression', '')
                    else:
                        expr = str(constraint)
                    if expr:
                        all_constraints.append(expr)
        
        if not all_constraints:
            return 1.0  # 没有约束时给满分
        
        # 检查约束测试
        constraint_tests = [t for t in tests if 'constraint' in t.get('test_type', '')]
        
        if all_constraints and not constraint_tests:
            score *= 0.5
            self.issues.append("No constraint tests generated despite having constraints")
        
        # 检查约束覆盖率
        tested_constraints = set()
        for test in constraint_tests:
            constraint = test.get('constraint', '')
            if constraint:
                tested_constraints.add(constraint)
        
        if all_constraints:
            coverage = len(tested_constraints) / len(all_constraints)
            score *= coverage
            
            if coverage < 1.0:
                untested = set(all_constraints) - tested_constraints
                if untested:
                    self.issues.append(f"Untested constraints: {list(untested)[:2]}...")
        
        return score
    
    def _evaluate_diversity(self, tests: List[Dict]) -> float:
        """评估测试多样性"""
        if not tests:
            return 0.0
        
        score = 1.0
        
        # 检查数据重复度
        test_data_hashes = set()
        duplicate_count = 0
        
        for test in tests:
            data_str = json.dumps(test.get('test_data', {}), sort_keys=True)
            if data_str in test_data_hashes:
                duplicate_count += 1
            test_data_hashes.add(data_str)
        
        if len(tests) > 0:
            uniqueness = 1 - (duplicate_count / len(tests))
            score *= uniqueness
            
            if uniqueness < 0.9:
                self.issues.append(f"High data duplication: {duplicate_count} duplicate tests")
        
        # 检查值的多样性
        value_diversity = self._check_value_diversity(tests)
        score *= value_diversity
        
        return score
    
    def _evaluate_business_realism(self, tests: List[Dict]) -> float:
        """评估业务真实性"""
        score = 1.0
        realistic_patterns = 0
        total_checks = 0
        
        for test in tests:
            data = test.get('test_data', {})
            
            # 检查价格真实性
            for key, value in data.items():
                if 'price' in key and isinstance(value, (int, float)):
                    total_checks += 1
                    if 0.99 <= value <= 9999.99:
                        realistic_patterns += 1
                
                # 检查邮箱格式
                if 'email' in key and isinstance(value, str):
                    total_checks += 1
                    if '@' in value and '.' in value:
                        realistic_patterns += 1
                
                # 检查ID格式
                if '_id' in key and isinstance(value, int):
                    total_checks += 1
                    if value > 0:
                        realistic_patterns += 1
        
        if total_checks > 0:
            realism_ratio = realistic_patterns / total_checks
            score *= realism_ratio
            
            if realism_ratio < 0.8:
                self.improvements.append("Improve business data realism")
        
        return score
    
    def _check_attribute_coverage(self, spec: Dict, tests: List[Dict]) -> float:
        """检查属性覆盖率"""
        all_attributes = set()
        tested_attributes = set()
        
        # 收集所有属性
        entities = spec.get('entities', [])
        if isinstance(entities, list):
            for entity in entities:
                attributes = entity.get('attributes', [])
                if isinstance(attributes, list):
                    for attr in attributes:
                        if isinstance(attr, dict) and 'name' in attr:
                            all_attributes.add(attr['name'])
        
        # 收集测试中的属性
        for test in tests:
            data = test.get('test_data', {})
            tested_attributes.update(data.keys())
        
        if all_attributes:
            return len(tested_attributes.intersection(all_attributes)) / len(all_attributes)
        return 1.0
    
    def _check_constraint_coverage(self, spec: Dict, tests: List[Dict]) -> float:
        """检查约束覆盖率"""
        # 简化实现
        constraint_tests = [t for t in tests if 'constraint' in t.get('test_type', '')]
        if constraint_tests:
            return 1.0
        
        # 检查是否有约束需要测试
        has_constraints = False
        entities = spec.get('entities', [])
        if isinstance(entities, list):
            for entity in entities:
                if entity.get('constraints'):
                    has_constraints = True
                    break
        
        return 0.5 if has_constraints else 1.0
    
    def _check_value_diversity(self, tests: List[Dict]) -> float:
        """检查值的多样性"""
        value_sets = {}
        
        for test in tests:
            data = test.get('test_data', {})
            for key, value in data.items():
                if key not in value_sets:
                    value_sets[key] = set()
                
                # 将值转换为可哈希类型
                if isinstance(value, list):
                    value = tuple(value)
                elif isinstance(value, dict):
                    value = tuple(sorted(value.items()))
                
                value_sets[key].add(value)
        
        # 计算平均多样性
        diversity_scores = []
        for key, values in value_sets.items():
            if len(values) > 1:
                # 多样性分数 = unique_values / total_tests
                diversity = min(len(values) / len(tests), 1.0)
                diversity_scores.append(diversity)
        
        return sum(diversity_scores) / len(diversity_scores) if diversity_scores else 0.8


def evaluate_all_examples():
    """评估所有示例文件"""
    evaluator = TestQualityEvaluator()
    results = []
    
    # 获取所有生成的测试文件
    test_files = []
    examples_dir = Path('examples')
    output_dir = Path('test_outputs/v8_batch')
    
    for yaml_file in examples_dir.rglob('*.yaml'):
        json_file = output_dir / f"v8_{yaml_file.stem}.json"
        if json_file.exists():
            test_files.append((str(yaml_file), str(json_file)))
    
    print(f"Evaluating {len(test_files)} test files...\n")
    
    # 评估每个文件
    for yaml_file, json_file in test_files:
        evaluator.issues = []  # 重置问题列表
        evaluator.improvements = []  # 重置改进建议
        
        result = evaluator.evaluate_file(yaml_file, json_file)
        results.append(result)
        
        # 打印单个文件结果
        print(f"{'='*60}")
        print(f"File: {Path(yaml_file).name}")
        print(f"Total Score: {result['total_score']}/100")
        print(f"Test Count: {result['test_count']}")
        print("\nDetailed Scores:")
        for metric, score in result['scores'].items():
            print(f"  {metric}: {score*100:.1f}%")
        
        if result['issues']:
            print("\nIssues Found:")
            for issue in result['issues'][:3]:
                print(f"  - {issue}")
        
        if result['improvements']:
            print("\nSuggested Improvements:")
            for improvement in result['improvements'][:3]:
                print(f"  - {improvement}")
    
    # 计算总体分数
    if results:
        avg_score = sum(r['total_score'] for r in results) / len(results)
        print(f"\n{'='*60}")
        print(f"OVERALL AVERAGE SCORE: {avg_score:.1f}/100")
        
        # 统计常见问题
        all_issues = []
        for r in results:
            all_issues.extend(r['issues'])
        
        if all_issues:
            print("\nMost Common Issues:")
            issue_counts = {}
            for issue in all_issues:
                # 简化问题描述
                key = issue.split(':')[0]
                issue_counts[key] = issue_counts.get(key, 0) + 1
            
            for issue, count in sorted(issue_counts.items(), key=lambda x: x[1], reverse=True)[:5]:
                print(f"  - {issue} (occurred {count} times)")
    
    return results


def main():
    """主函数"""
    # 先生成所有测试
    print("Generating tests for all examples...")
    os.system("python test_v8_all_examples.py > /dev/null 2>&1")
    
    print("\nEvaluating test quality...")
    results = evaluate_all_examples()
    
    # 保存评估报告
    report = {
        'evaluation_time': datetime.now().isoformat(),
        'total_files': len(results),
        'average_score': sum(r['total_score'] for r in results) / len(results) if results else 0,
        'results': results
    }
    
    with open('test_outputs/v8_evaluation_report.json', 'w') as f:
        json.dump(report, f, indent=2)
    
    print(f"\nEvaluation report saved to: test_outputs/v8_evaluation_report.json")


if __name__ == '__main__':
    main()