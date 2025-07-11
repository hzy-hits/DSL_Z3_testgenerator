#!/usr/bin/env python3
"""
评估生成的测试用例质量，检查约束满足情况
"""

import json
import sys
import re
from pathlib import Path


def evaluate_constraint(constraint: str, test_data: dict) -> bool:
    """评估单个约束 - 简单实现"""
    try:
        # 预处理约束表达式
        expr = constraint
        
        # 处理实体前缀（如 Order.total_amount -> total_amount）
        for entity_prefix in ['Product.', 'Order.', 'Cart.', 'Customer.']:
            expr = expr.replace(entity_prefix, '')
        
        # 处理size函数
        def replace_size(match):
            var_name = match.group(1)
            if var_name in test_data:
                value = test_data[var_name]
                if isinstance(value, (list, set, tuple)):
                    return str(len(value))
            return '0'
        
        expr = re.sub(r'size\((\w+)\)', replace_size, expr)
        
        # 替换变量值
        for key, value in test_data.items():
            if key in expr:
                if isinstance(value, str):
                    expr = expr.replace(key, f'"{value}"')
                elif value is None:
                    expr = expr.replace(key, 'None')
                else:
                    expr = expr.replace(key, str(value))
        
        # 安全评估
        try:
            result = eval(expr, {"__builtins__": {}}, {})
            return bool(result)
        except:
            return None
            
    except Exception as e:
        print(f"  警告: 无法评估约束 '{constraint}': {e}")
        return None


def check_order_total_constraint(test_data: dict) -> bool:
    """检查订单总价约束"""
    # Order.total_amount == Order.subtotal + Order.tax_amount + Order.shipping_cost - (Order.subtotal * Order.discount_percentage / 100)
    if all(k in test_data for k in ['total_amount', 'subtotal', 'tax_amount', 'shipping_cost', 'discount_percentage']):
        expected_total = (test_data['subtotal'] + 
                         test_data['tax_amount'] + 
                         test_data['shipping_cost'] - 
                         (test_data['subtotal'] * test_data['discount_percentage'] / 100))
        actual_total = test_data['total_amount']
        return abs(expected_total - actual_total) < 0.01  # 允许小的浮点误差
    return True  # 如果字段不全，跳过检查


def evaluate_test_file(test_file: str, dsl_file: str = None):
    """评估测试文件中的所有测试用例"""
    print(f"\n评估测试文件: {test_file}")
    print("=" * 80)
    
    # 读取测试数据
    with open(test_file, 'r') as f:
        test_suite = json.load(f)
    
    total_tests = test_suite.get('total_tests', 0)
    tests = test_suite.get('tests', [])
    
    print(f"总测试数: {total_tests}")
    print(f"实体: {', '.join(test_suite.get('entities', []))}")
    
    # 定义基本约束
    basic_constraints = {
        'Cart': [
            'total_price >= 0',
            'size(items) <= 50',
            'size(discount_codes) <= 5'
        ],
        'Product': [
            'price > 0',
            'id >= 1',
            'size(categories) >= 1'
        ],
        'Order': [
            'subtotal > 0',
            'tax_amount >= 0',
            'shipping_cost >= 0',
            'discount_percentage >= 0',
            'discount_percentage <= 100'
        ]
    }
    
    # 评估结果统计
    results = {
        'total': 0,
        'passed': 0,
        'failed': 0,
        'skipped': 0,
        'by_type': {},
        'violations': []
    }
    
    print("\n测试评估结果:")
    print("-" * 80)
    
    for test in tests:
        results['total'] += 1
        test_type = test.get('test_type', 'unknown')
        test_name = test.get('test_name', 'unnamed')
        test_data = test.get('test_data', {})
        entity = test.get('entity', 'unknown')
        
        # 初始化类型统计
        if test_type not in results['by_type']:
            results['by_type'][test_type] = {'total': 0, 'passed': 0, 'failed': 0}
        results['by_type'][test_type]['total'] += 1
        
        # 获取该实体的约束
        constraints = basic_constraints.get(entity, [])
        
        # 特殊处理订单总价约束
        if entity == 'Order':
            order_constraint_ok = check_order_total_constraint(test_data)
            if not order_constraint_ok:
                print(f"\n✗ {test_name} ({test_type})")
                print(f"  违反订单总价约束")
                print(f"  数据: {json.dumps(test_data, indent=2)}")
                results['failed'] += 1
                results['by_type'][test_type]['failed'] += 1
                results['violations'].append({
                    'test': test_name,
                    'constraint': 'order_total_calculation',
                    'data': test_data
                })
                continue
        
        # 检查基本约束
        all_passed = True
        violated_constraints = []
        
        for constraint in constraints:
            result = evaluate_constraint(constraint, test_data)
            if result is False:
                all_passed = False
                violated_constraints.append(constraint)
        
        # 负面测试预期失败
        if test_type == 'negative':
            # 负面测试应该违反某些约束
            if violated_constraints:
                results['passed'] += 1
                results['by_type'][test_type]['passed'] += 1
                print(f"✓ {test_name} ({test_type}) - 正确违反约束")
            else:
                results['failed'] += 1
                results['by_type'][test_type]['failed'] += 1
                print(f"\n✗ {test_name} ({test_type})")
                print(f"  错误: 负面测试未违反任何约束")
                print(f"  数据: {json.dumps(test_data, indent=2)}")
        else:
            # 其他测试应该满足所有约束
            if all_passed:
                results['passed'] += 1
                results['by_type'][test_type]['passed'] += 1
                # print(f"✓ {test_name} ({test_type})")
            else:
                results['failed'] += 1
                results['by_type'][test_type]['failed'] += 1
                print(f"\n✗ {test_name} ({test_type})")
                print(f"  违反约束: {', '.join(violated_constraints)}")
                print(f"  数据: {json.dumps(test_data, indent=2)}")
                results['violations'].append({
                    'test': test_name,
                    'constraints': violated_constraints,
                    'data': test_data
                })
    
    # 打印总结
    print("\n" + "=" * 80)
    print("评估总结:")
    print(f"  总测试数: {results['total']}")
    print(f"  通过: {results['passed']} ({results['passed']/results['total']*100:.1f}%)")
    print(f"  失败: {results['failed']} ({results['failed']/results['total']*100:.1f}%)")
    
    print("\n按类型统计:")
    for test_type, stats in results['by_type'].items():
        total = stats['total']
        passed = stats['passed']
        print(f"  {test_type}: {passed}/{total} 通过 ({passed/total*100:.1f}%)")
    
    if results['violations']:
        print(f"\n发现 {len(results['violations'])} 个约束违反问题")
    
    return results


def main():
    """主函数"""
    import argparse
    parser = argparse.ArgumentParser(description='评估测试用例质量')
    parser.add_argument('test_file', help='测试文件路径')
    parser.add_argument('--dsl', help='对应的DSL文件路径（可选）')
    
    args = parser.parse_args()
    
    if not Path(args.test_file).exists():
        print(f"错误: 测试文件不存在: {args.test_file}")
        sys.exit(1)
    
    results = evaluate_test_file(args.test_file, args.dsl)
    
    # 返回状态码
    sys.exit(0 if results['failed'] == 0 else 1)


if __name__ == '__main__':
    main()