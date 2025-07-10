#!/usr/bin/env python3
"""
独立测试评分系统 - 作为独立判官评估生成的测试用例质量
"""

import json
import argparse
from typing import Dict, List, Any, Tuple
from pathlib import Path
import statistics


class IndependentTestEvaluator:
    """独立的测试质量评估器"""
    
    def __init__(self):
        self.evaluation_criteria = {
            "correctness": {
                "weight": 0.25,
                "description": "测试数据的正确性和合法性"
            },
            "coverage": {
                "weight": 0.20,
                "description": "业务规则和约束的覆盖程度"
            },
            "diversity": {
                "weight": 0.15,
                "description": "测试场景的多样性"
            },
            "boundary": {
                "weight": 0.15,
                "description": "边界值测试的完整性"
            },
            "negative": {
                "weight": 0.10,
                "description": "负面测试的充分性"
            },
            "readability": {
                "weight": 0.10,
                "description": "测试的可读性和描述清晰度"
            },
            "efficiency": {
                "weight": 0.05,
                "description": "测试集的效率（避免冗余）"
            }
        }
    
    def evaluate_test_suite(self, test_file_path: str, dsl_file_path: str = None) -> Dict[str, Any]:
        """评估测试套件的质量"""
        # 加载测试数据
        with open(test_file_path, 'r', encoding='utf-8') as f:
            test_data = json.load(f)
        
        # 如果提供了DSL文件，加载以进行更深入的分析
        dsl_model = None
        if dsl_file_path and Path(dsl_file_path).exists():
            import yaml
            with open(dsl_file_path, 'r', encoding='utf-8') as f:
                dsl_model = yaml.safe_load(f)
        
        # 执行各项评估
        scores = {
            "correctness": self._evaluate_correctness(test_data, dsl_model),
            "coverage": self._evaluate_coverage(test_data, dsl_model),
            "diversity": self._evaluate_diversity(test_data),
            "boundary": self._evaluate_boundary_testing(test_data),
            "negative": self._evaluate_negative_testing(test_data),
            "readability": self._evaluate_readability(test_data),
            "efficiency": self._evaluate_efficiency(test_data)
        }
        
        # 计算总分
        total_score = sum(scores[criterion] * self.evaluation_criteria[criterion]["weight"] 
                         for criterion in scores)
        
        # 生成详细报告
        report = self._generate_detailed_report(test_data, scores, total_score, dsl_model)
        
        return report
    
    def _evaluate_correctness(self, test_data: Dict, dsl_model: Dict = None) -> float:
        """评估测试数据的正确性"""
        score = 10.0
        issues = []
        
        tests = self._extract_all_tests(test_data)
        
        for test in tests:
            test_values = test.get('test_data', test.get('values', test.get('concrete_input', {})))
            
            # 检查数据类型正确性
            if dsl_model:
                for entity in dsl_model.get('entities', []):
                    entity_name = entity['name'].lower()
                    for attr in entity.get('attributes', []):
                        attr_name = f"{entity_name}_{attr['name']}"
                        if attr_name in test_values:
                            value = test_values[attr_name]
                            attr_type = attr.get('type', 'string')
                            
                            # 类型检查
                            if not self._check_type_compatibility(value, attr_type):
                                score -= 0.5
                                issues.append(f"类型不匹配: {attr_name} 应为 {attr_type}")
                            
                            # 范围检查
                            if 'min' in attr and isinstance(value, (int, float)) and value < attr['min']:
                                score -= 0.3
                                issues.append(f"值低于最小值: {attr_name} = {value} < {attr['min']}")
                            
                            if 'max' in attr and isinstance(value, (int, float)) and value > attr['max']:
                                score -= 0.3
                                issues.append(f"值超过最大值: {attr_name} = {value} > {attr['max']}")
        
        return max(0, score)
    
    def _evaluate_coverage(self, test_data: Dict, dsl_model: Dict = None) -> float:
        """评估测试覆盖率"""
        if not dsl_model:
            # 基于测试类型的简单评估
            test_types = set()
            tests = self._extract_all_tests(test_data)
            for test in tests:
                test_type = test.get('type', test.get('test_type', 'unknown'))
                test_types.add(test_type)
            
            expected_types = {'boundary', 'valid', 'invalid', 'rule_coverage', 'negative', 'generated'}
            coverage_ratio = len(test_types & expected_types) / len(expected_types)
            return coverage_ratio * 10
        
        # 详细的覆盖率分析
        covered_rules = set()
        covered_constraints = set()
        covered_entities = set()
        
        tests = self._extract_all_tests(test_data)
        
        for test in tests:
            # 从描述中提取覆盖的规则
            desc = test.get('description', '')
            if 'rule:' in desc.lower():
                covered_rules.add(desc)
            
            # 检查测试数据覆盖的实体
            test_values = test.get('test_data', test.get('values', {}))
            for key in test_values:
                entity_name = key.split('_')[0]
                covered_entities.add(entity_name)
        
        # 计算覆盖率
        total_rules = len(dsl_model.get('rules', [])) if dsl_model else 1
        total_constraints = len(dsl_model.get('constraints', [])) if dsl_model else 1
        total_entities = len(dsl_model.get('entities', [])) if dsl_model else 1
        
        rule_coverage = len(covered_rules) / total_rules if total_rules > 0 else 1.0
        entity_coverage = len(covered_entities) / total_entities if total_entities > 0 else 1.0
        
        return ((rule_coverage + entity_coverage) / 2) * 10
    
    def _evaluate_diversity(self, test_data: Dict) -> float:
        """评估测试多样性"""
        tests = self._extract_all_tests(test_data)
        
        # 统计不同类型的测试
        type_counts = {}
        value_sets = []
        
        for test in tests:
            # 测试类型多样性
            test_type = test.get('type', test.get('test_type', 'unknown'))
            type_counts[test_type] = type_counts.get(test_type, 0) + 1
            
            # 数据值多样性
            test_values = test.get('test_data', test.get('values', {}))
            value_sets.append(frozenset(str(v) for v in test_values.values()))
        
        # 计算类型分布的均匀性
        if len(type_counts) > 1:
            counts = list(type_counts.values())
            mean_count = statistics.mean(counts)
            std_dev = statistics.stdev(counts)
            uniformity = 1 - (std_dev / mean_count if mean_count > 0 else 0)
        else:
            uniformity = 0.5
        
        # 计算值的独特性
        unique_ratio = len(set(value_sets)) / len(value_sets) if value_sets else 0
        
        # 综合评分
        diversity_score = (uniformity * 0.4 + unique_ratio * 0.6) * 10
        
        return min(10, diversity_score)
    
    def _evaluate_boundary_testing(self, test_data: Dict) -> float:
        """评估边界值测试"""
        tests = self._extract_all_tests(test_data)
        
        boundary_tests = 0
        boundary_indicators = ['boundary', 'min', 'max', 'edge', 'limit', '边界']
        
        for test in tests:
            test_name = test.get('name', '').lower()
            test_desc = test.get('description', '').lower()
            test_type = test.get('type', test.get('test_type', '')).lower()
            
            # 检查是否为边界测试
            if any(indicator in test_name + test_desc + test_type for indicator in boundary_indicators):
                boundary_tests += 1
        
        # 边界测试应占总测试的合理比例（15-25%）
        boundary_ratio = boundary_tests / len(tests) if tests else 0
        
        if 0.15 <= boundary_ratio <= 0.25:
            score = 10
        elif 0.1 <= boundary_ratio <= 0.3:
            score = 8
        elif boundary_ratio < 0.1:
            score = 5
        else:
            score = 7  # 太多边界测试也不好
        
        return score
    
    def _evaluate_negative_testing(self, test_data: Dict) -> float:
        """评估负面测试"""
        tests = self._extract_all_tests(test_data)
        
        negative_tests = 0
        negative_indicators = ['negative', 'invalid', 'fail', 'error', 'reject', '无效', '失败']
        
        for test in tests:
            test_name = test.get('name', '').lower()
            test_desc = test.get('description', '').lower()
            test_type = test.get('type', test.get('test_type', '')).lower()
            expected = test.get('expected_result', '').lower()
            
            # 检查是否为负面测试
            if (any(indicator in test_name + test_desc + test_type for indicator in negative_indicators) or
                expected in ['fail', 'error', 'reject']):
                negative_tests += 1
        
        # 负面测试应占总测试的合理比例（10-20%）
        negative_ratio = negative_tests / len(tests) if tests else 0
        
        if 0.1 <= negative_ratio <= 0.2:
            score = 10
        elif 0.05 <= negative_ratio <= 0.25:
            score = 8
        elif negative_ratio < 0.05:
            score = 5
        else:
            score = 7
        
        return score
    
    def _evaluate_readability(self, test_data: Dict) -> float:
        """评估测试的可读性"""
        tests = self._extract_all_tests(test_data)
        
        readability_score = 10.0
        
        for test in tests:
            # 检查是否有清晰的名称
            if not test.get('name', '').strip():
                readability_score -= 0.2
            
            # 检查是否有描述
            if not test.get('description', '').strip():
                readability_score -= 0.1
            
            # 检查描述的质量
            desc = test.get('description', '')
            if desc and len(desc) < 10:
                readability_score -= 0.05
            
            # 检查是否有预期结果
            if not test.get('expected_result'):
                readability_score -= 0.1
        
        return max(0, readability_score)
    
    def _evaluate_efficiency(self, test_data: Dict) -> float:
        """评估测试集的效率（避免冗余）"""
        tests = self._extract_all_tests(test_data)
        
        # 检查重复的测试数据
        value_signatures = []
        for test in tests:
            test_values = test.get('test_data', test.get('values', {}))
            # 创建值的签名
            signature = tuple(sorted((k, str(v)) for k, v in test_values.items()))
            value_signatures.append(signature)
        
        # 计算独特测试的比例
        unique_ratio = len(set(value_signatures)) / len(value_signatures) if value_signatures else 1.0
        
        # 检查测试数量是否合理
        if len(tests) > 100:
            # 过多的测试可能表示效率低下
            size_penalty = min(0.2, (len(tests) - 100) / 500)
            unique_ratio -= size_penalty
        
        return max(0, unique_ratio * 10)
    
    def _extract_all_tests(self, test_data: Dict) -> List[Dict]:
        """从测试数据中提取所有测试用例"""
        tests = []
        
        # 处理不同的测试数据格式
        if 'test_cases' in test_data:
            tests.extend(test_data['test_cases'])
        
        if 'test_suites' in test_data:
            for suite_name, suite_tests in test_data['test_suites'].items():
                if isinstance(suite_tests, list):
                    tests.extend(suite_tests)
        
        if 'tests' in test_data:
            tests.extend(test_data['tests'])
        
        # 如果直接是测试列表
        if isinstance(test_data, list):
            tests = test_data
        
        return tests
    
    def _check_type_compatibility(self, value: Any, expected_type: str) -> bool:
        """检查值是否与期望类型兼容"""
        type_mapping = {
            'integer': (int,),
            'real': (int, float),
            'boolean': (bool,),
            'string': (str,),
        }
        
        # 处理数组和集合类型
        if expected_type.startswith('array[') or expected_type.startswith('set['):
            return isinstance(value, list)
        
        expected_python_types = type_mapping.get(expected_type, (object,))
        return isinstance(value, expected_python_types)
    
    def _generate_detailed_report(self, test_data: Dict, scores: Dict, total_score: float, 
                                 dsl_model: Dict = None) -> Dict[str, Any]:
        """生成详细的评估报告"""
        tests = self._extract_all_tests(test_data)
        
        # 生成等级评定
        grade = self._calculate_grade(total_score)
        
        # 统计信息
        test_types = {}
        for test in tests:
            test_type = test.get('type', test.get('test_type', 'unknown'))
            test_types[test_type] = test_types.get(test_type, 0) + 1
        
        # 生成改进建议
        suggestions = self._generate_suggestions(scores)
        
        report = {
            "总体评分": round(total_score, 2),
            "等级": grade,
            "详细得分": {
                criterion: {
                    "得分": round(score, 2),
                    "权重": self.evaluation_criteria[criterion]["weight"],
                    "说明": self.evaluation_criteria[criterion]["description"]
                }
                for criterion, score in scores.items()
            },
            "测试统计": {
                "测试总数": len(tests),
                "测试类型分布": test_types,
                "平均测试数据量": round(statistics.mean([len(t.get('test_data', t.get('values', {}))) 
                                                        for t in tests]), 2) if tests else 0
            },
            "改进建议": suggestions,
            "评估时间": self._get_current_time()
        }
        
        return report
    
    def _calculate_grade(self, score: float) -> str:
        """根据分数计算等级"""
        if score >= 9.5:
            return "A+ (卓越)"
        elif score >= 9.0:
            return "A (优秀)"
        elif score >= 8.5:
            return "B+ (良好)"
        elif score >= 8.0:
            return "B (较好)"
        elif score >= 7.5:
            return "C+ (中等)"
        elif score >= 7.0:
            return "C (合格)"
        elif score >= 6.0:
            return "D (需改进)"
        else:
            return "F (不合格)"
    
    def _generate_suggestions(self, scores: Dict) -> List[str]:
        """根据评分生成改进建议"""
        suggestions = []
        
        # 针对每个低分项生成建议
        for criterion, score in scores.items():
            if score < 7.0:
                if criterion == "correctness":
                    suggestions.append("提高数据正确性：确保所有测试数据符合DSL定义的类型和约束")
                elif criterion == "coverage":
                    suggestions.append("增加测试覆盖率：确保覆盖所有业务规则和约束条件")
                elif criterion == "diversity":
                    suggestions.append("增加测试多样性：使用更多不同的测试数据组合")
                elif criterion == "boundary":
                    suggestions.append("加强边界测试：为所有数值属性添加最小值、最大值测试")
                elif criterion == "negative":
                    suggestions.append("增加负面测试：测试各种无效输入和错误场景")
                elif criterion == "readability":
                    suggestions.append("提高可读性：为每个测试添加清晰的名称和描述")
                elif criterion == "efficiency":
                    suggestions.append("优化测试集：消除重复测试，减少冗余")
        
        # 针对高分项的保持建议
        high_score_criteria = [c for c, s in scores.items() if s >= 9.0]
        if high_score_criteria:
            suggestions.append(f"保持优势：在 {', '.join(high_score_criteria)} 方面表现优秀，请继续保持")
        
        if not suggestions:
            suggestions.append("整体表现优秀！建议定期复审并更新测试用例以适应需求变化")
        
        return suggestions
    
    def _get_current_time(self) -> str:
        """获取当前时间"""
        from datetime import datetime
        return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def main():
    parser = argparse.ArgumentParser(description="独立测试质量评估系统")
    parser.add_argument("test_file", help="测试文件路径（JSON格式）")
    parser.add_argument("--dsl", help="DSL文件路径（YAML格式），用于更深入的分析")
    parser.add_argument("--output", help="输出报告路径")
    parser.add_argument("--format", choices=["json", "text"], default="text", help="输出格式")
    
    args = parser.parse_args()
    
    # 创建评估器
    evaluator = IndependentTestEvaluator()
    
    # 执行评估
    report = evaluator.evaluate_test_suite(args.test_file, args.dsl)
    
    # 输出结果
    if args.format == "json":
        output = json.dumps(report, ensure_ascii=False, indent=2)
    else:
        # 格式化文本输出
        output = f"""
================================================================================
                          测试质量评估报告
================================================================================

总体评分: {report['总体评分']}/10.0
等  级: {report['等级']}

详细评分:
--------------------------------------------------------------------------------
"""
        for criterion, details in report['详细得分'].items():
            output += f"  {criterion:<15} {details['得分']:>5.2f}/10  (权重: {details['权重']*100:.0f}%)  {details['说明']}\n"
        
        output += f"""
测试统计:
--------------------------------------------------------------------------------
  测试总数: {report['测试统计']['测试总数']}
  平均数据量: {report['测试统计']['平均测试数据量']}
  
  类型分布:
"""
        for test_type, count in report['测试统计']['测试类型分布'].items():
            output += f"    - {test_type}: {count}\n"
        
        output += """
改进建议:
--------------------------------------------------------------------------------
"""
        for i, suggestion in enumerate(report['改进建议'], 1):
            output += f"  {i}. {suggestion}\n"
        
        output += f"""
================================================================================
评估时间: {report['评估时间']}
================================================================================
"""
    
    # 保存或打印结果
    if args.output:
        with open(args.output, 'w', encoding='utf-8') as f:
            f.write(output)
        print(f"评估报告已保存到: {args.output}")
    else:
        print(output)


if __name__ == "__main__":
    main()