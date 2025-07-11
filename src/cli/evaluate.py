#!/usr/bin/env python3
"""
测试质量评估工具
"""

import json
import argparse
import logging
from pathlib import Path
from typing import Dict, List, Any, Tuple
import sys

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)


class TestQualityEvaluator:
    """测试质量评估器"""
    
    def __init__(self):
        self.parser = self._create_parser()
        self.results = {
            'total_tests': 0,
            'passed_tests': 0,
            'failed_tests': 0,
            'issues': [],
            'test_types': {},
            'quality_score': 0
        }
    
    def _create_parser(self):
        """创建命令行解析器"""
        parser = argparse.ArgumentParser(
            description='测试质量评估工具 - 验证生成的测试用例质量',
            formatter_class=argparse.RawDescriptionHelpFormatter
        )
        
        parser.add_argument('test_file', help='测试文件路径（JSON格式）')
        parser.add_argument('-v', '--verbose', action='store_true', help='显示详细信息')
        parser.add_argument('-o', '--output', help='输出报告文件路径')
        parser.add_argument('--format', choices=['json', 'markdown', 'text'], 
                          default='text', help='报告格式')
        
        return parser
    
    def run(self):
        """运行评估"""
        args = self.parser.parse_args()
        
        try:
            # 加载测试文件
            test_data = self._load_test_file(args.test_file)
            
            # 执行评估
            self._evaluate_tests(test_data, args.verbose)
            
            # 生成报告
            report = self._generate_report()
            
            # 输出报告
            if args.output:
                self._save_report(report, args.output, args.format)
            else:
                self._print_report(report, args.format)
                
        except Exception as e:
            logger.error(f"评估失败: {e}")
            if args.verbose:
                import traceback
                traceback.print_exc()
            sys.exit(1)
    
    def _load_test_file(self, file_path: str) -> Dict:
        """加载测试文件"""
        path = Path(file_path)
        if not path.exists():
            raise FileNotFoundError(f"测试文件不存在: {file_path}")
        
        with open(path, 'r', encoding='utf-8') as f:
            return json.load(f)
    
    def _evaluate_tests(self, test_data: Dict, verbose: bool = False):
        """评估测试质量"""
        tests = test_data.get('tests', [])
        self.results['total_tests'] = len(tests)
        
        for test in tests:
            # 兼容不同的字段名
            test_type = test.get('type', test.get('test_type', 'unknown'))
            self.results['test_types'][test_type] = \
                self.results['test_types'].get(test_type, 0) + 1
            
            # 评估单个测试
            passed, issues = self._evaluate_single_test(test, test_data)
            
            if passed:
                self.results['passed_tests'] += 1
            else:
                self.results['failed_tests'] += 1
                self.results['issues'].extend(issues)
            
            if verbose and issues:
                logger.info(f"测试 '{test.get('name')}' 发现问题: {issues}")
        
        # 计算质量分数
        self._calculate_quality_score()
    
    def _evaluate_single_test(self, test: Dict, test_data: Dict) -> Tuple[bool, List[str]]:
        """评估单个测试"""
        issues = []
        # 兼容不同的字段名
        test_type = test.get('type', test.get('test_type', ''))
        data = test.get('data', test.get('test_data', {}))
        name = test.get('name', test.get('test_name', ''))
        
        # 检查基本结构
        if not name:
            issues.append("缺少测试名称")
        if not test_type:
            issues.append("缺少测试类型")
        if not data:
            issues.append("缺少测试数据")
        
        # 根据测试类型进行特定检查
        if test_type == 'negative':
            issues.extend(self._check_negative_test(test, data))
        elif test_type == 'boundary':
            issues.extend(self._check_boundary_test(test, data))
        elif test_type == 'constraint':
            issues.extend(self._check_constraint_test(test, data))
        
        # 检查数据类型
        issues.extend(self._check_data_types(data))
        
        return len(issues) == 0, issues
    
    def _check_negative_test(self, test: Dict, data: Dict) -> List[str]:
        """检查负面测试"""
        issues = []
        
        # 负面测试应该包含违反约束的值
        for entity_name, entity_data in data.items():
            if isinstance(entity_data, dict):
                for attr_name, value in entity_data.items():
                    # 检查是否真的是违反约束的值
                    if value is None:
                        continue
                    
                    # 检查常见的负面测试模式
                    if isinstance(value, str) and value in ['not_a_number', 'invalid']:
                        issues.append(f"{entity_name}.{attr_name}: 使用了错误类型而非约束违反值")
        
        return issues
    
    def _check_boundary_test(self, test: Dict, data: Dict) -> List[str]:
        """检查边界测试"""
        issues = []
        
        # 边界测试应该使用极限值
        for entity_name, entity_data in data.items():
            if isinstance(entity_data, dict):
                for attr_name, value in entity_data.items():
                    # 检查ID字段
                    if 'id' in attr_name.lower() and value == 0:
                        issues.append(f"{entity_name}.{attr_name}: ID不应该为0")
                    
                    # 检查价格字段
                    if 'price' in attr_name.lower() and isinstance(value, (int, float)) and value < 0.01:
                        issues.append(f"{entity_name}.{attr_name}: 价格不应该小于0.01")
        
        return issues
    
    def _check_constraint_test(self, test: Dict, data: Dict) -> List[str]:
        """检查约束测试"""
        issues = []
        
        # 约束测试应该满足或违反特定约束
        constraint_info = test.get('constraint_info', {})
        if not constraint_info:
            issues.append("约束测试缺少约束信息")
        
        return issues
    
    def _check_data_types(self, data: Dict) -> List[str]:
        """检查数据类型"""
        issues = []
        
        for entity_name, entity_data in data.items():
            if isinstance(entity_data, dict):
                for attr_name, value in entity_data.items():
                    # 检查集合类型
                    if 'categories' in attr_name or 'tags' in attr_name or 'items' in attr_name:
                        if not isinstance(value, list):
                            issues.append(f"{entity_name}.{attr_name}: 应该是数组类型，实际是{type(value).__name__}")
        
        return issues
    
    def _calculate_quality_score(self):
        """计算质量分数"""
        if self.results['total_tests'] == 0:
            self.results['quality_score'] = 0
            return
        
        # 基础分数：通过率
        base_score = (self.results['passed_tests'] / self.results['total_tests']) * 100
        
        # 测试类型多样性加分
        type_diversity_score = min(len(self.results['test_types']) * 5, 20)
        
        # 严重问题扣分
        critical_issues = [issue for issue in self.results['issues'] 
                          if '错误类型' in issue or 'ID不应该为0' in issue]
        critical_penalty = min(len(critical_issues) * 5, 30)
        
        # 计算最终分数
        self.results['quality_score'] = max(0, min(100, 
            base_score + type_diversity_score - critical_penalty))
    
    def _generate_report(self) -> Dict:
        """生成评估报告"""
        return {
            'summary': {
                'total_tests': self.results['total_tests'],
                'passed_tests': self.results['passed_tests'],
                'failed_tests': self.results['failed_tests'],
                'pass_rate': f"{(self.results['passed_tests'] / max(1, self.results['total_tests']) * 100):.1f}%",
                'quality_score': f"{self.results['quality_score']:.1f}/100"
            },
            'test_types': self.results['test_types'],
            'issues': self.results['issues'][:10] if self.results['issues'] else [],  # 只显示前10个问题
            'recommendations': self._generate_recommendations()
        }
    
    def _generate_recommendations(self) -> List[str]:
        """生成改进建议"""
        recommendations = []
        
        if self.results['quality_score'] < 80:
            recommendations.append("建议检查并修复测试生成逻辑")
        
        # 检查特定问题
        wrong_type_issues = [i for i in self.results['issues'] if '错误类型' in i]
        if wrong_type_issues:
            recommendations.append("负面测试应该生成违反约束的值，而不是错误类型")
        
        id_zero_issues = [i for i in self.results['issues'] if 'ID不应该为0' in i]
        if id_zero_issues:
            recommendations.append("ID字段的最小值应该是1而不是0")
        
        if 'negative' not in self.results['test_types']:
            recommendations.append("缺少负面测试用例")
        
        if 'boundary' not in self.results['test_types']:
            recommendations.append("缺少边界测试用例")
        
        return recommendations
    
    def _print_report(self, report: Dict, format: str):
        """打印报告"""
        if format == 'json':
            print(json.dumps(report, ensure_ascii=False, indent=2))
        elif format == 'markdown':
            print(self._format_markdown_report(report))
        else:  # text
            print(self._format_text_report(report))
    
    def _format_text_report(self, report: Dict) -> str:
        """格式化文本报告"""
        lines = []
        lines.append("="*50)
        lines.append("📊 测试质量评估报告")
        lines.append("="*50)
        
        summary = report['summary']
        lines.append(f"总测试数: {summary['total_tests']}")
        lines.append(f"通过: {summary['passed_tests']}")
        lines.append(f"失败: {summary['failed_tests']}")
        lines.append(f"通过率: {summary['pass_rate']}")
        lines.append(f"质量分数: {summary['quality_score']}")
        
        lines.append("\n测试类型分布:")
        for test_type, count in report['test_types'].items():
            lines.append(f"  - {test_type}: {count}")
        
        if report['issues']:
            lines.append("\n主要问题:")
            for issue in report['issues']:
                lines.append(f"  ❌ {issue}")
        
        if report['recommendations']:
            lines.append("\n改进建议:")
            for rec in report['recommendations']:
                lines.append(f"  💡 {rec}")
        
        lines.append("="*50)
        
        return "\n".join(lines)
    
    def _format_markdown_report(self, report: Dict) -> str:
        """格式化Markdown报告"""
        lines = []
        lines.append("# 测试质量评估报告\n")
        
        summary = report['summary']
        lines.append("## 📊 总体统计\n")
        lines.append(f"- **总测试数**: {summary['total_tests']}")
        lines.append(f"- **通过**: {summary['passed_tests']}")
        lines.append(f"- **失败**: {summary['failed_tests']}")
        lines.append(f"- **通过率**: {summary['pass_rate']}")
        lines.append(f"- **质量分数**: {summary['quality_score']}")
        
        lines.append("\n## 📈 测试类型分布\n")
        for test_type, count in report['test_types'].items():
            lines.append(f"- {test_type}: {count}")
        
        if report['issues']:
            lines.append("\n## ❌ 主要问题\n")
            for issue in report['issues']:
                lines.append(f"- {issue}")
        
        if report['recommendations']:
            lines.append("\n## 💡 改进建议\n")
            for rec in report['recommendations']:
                lines.append(f"- {rec}")
        
        return "\n".join(lines)
    
    def _save_report(self, report: Dict, output_path: str, format: str):
        """保存报告"""
        path = Path(output_path)
        
        if format == 'json':
            with open(path, 'w', encoding='utf-8') as f:
                json.dump(report, f, ensure_ascii=False, indent=2)
        elif format == 'markdown':
            with open(path, 'w', encoding='utf-8') as f:
                f.write(self._format_markdown_report(report))
        else:  # text
            with open(path, 'w', encoding='utf-8') as f:
                f.write(self._format_text_report(report))
        
        logger.info(f"报告已保存: {path}")


def main():
    """主入口"""
    evaluator = TestQualityEvaluator()
    evaluator.run()


if __name__ == "__main__":
    main()