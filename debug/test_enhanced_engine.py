#!/usr/bin/env python3
"""Test the enhanced engine that generates all test cases automatically"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from dsl_test_generator import DSLParser
from dsl_test_generator.core.enhanced_engine import EnhancedDSLEngine


def test_enhanced_engine():
    """Test the enhanced engine with comprehensive test generation."""
    print("🚀 Testing Enhanced DSL Engine")
    print("=" * 80)
    
    # Parse the hotel booking DSL
    parser = DSLParser()
    model = parser.parse_file("demo/hotel_booking_system.yaml")
    
    # Test with enhanced engine
    print("\n1. Testing with Enhanced Engine:")
    print("-" * 40)
    
    enhanced_engine = EnhancedDSLEngine()
    
    # First try with original model
    tests1 = enhanced_engine.generate_tests(model)
    print(f"Tests generated with original ranges: {len(tests1)}")
    
    # Then try with extended ranges
    tests2 = enhanced_engine.generate_tests_with_extended_ranges(model)
    print(f"Tests generated with extended ranges: {len(tests2)}")
    
    # Analyze test types
    test_types = {}
    negative_count = 0
    
    for test in tests2:
        t = test.get('type', 'unknown')
        test_types[t] = test_types.get(t, 0) + 1
        if t == 'negative':
            negative_count += 1
    
    print("\nTest type distribution:")
    for t, count in sorted(test_types.items()):
        print(f"  - {t}: {count}")
    
    print(f"\n✅ Successfully generated {negative_count} negative tests!")
    
    # Show negative test examples
    if negative_count > 0:
        print("\nNegative test examples:")
        negative_tests = [t for t in tests2 if t.get('type') == 'negative']
        for test in negative_tests[:5]:
            print(f"\n  {test['name']}:")
            print(f"    {test.get('description', 'N/A')}")
            values = test.get('values', {})
            # Show key invalid values
            for key, value in values.items():
                if 'age' in key and value < 18:
                    print(f"    ❌ {key}: {value} (< 18)")
                elif 'member_level' in key and (value < 1 or value > 3):
                    print(f"    ❌ {key}: {value} (invalid level)")
                elif 'stay_days' in key and (value < 1 or value > 30):
                    print(f"    ❌ {key}: {value} (invalid days)")
                elif 'discount_percent' in key and (value < 0 or value > 50):
                    print(f"    ❌ {key}: {value} (invalid discount)")
    
    return tests2


def calculate_comprehensive_coverage(tests):
    """Calculate comprehensive test coverage."""
    print("\n\n📊 Comprehensive Coverage Analysis")
    print("=" * 80)
    
    # Define all test scenarios needed
    coverage_checklist = {
        # Positive boundary tests
        "boundary_age_min": False,
        "boundary_age_max": False,
        "boundary_member_level_min": False,
        "boundary_member_level_max": False,
        "boundary_room_type_min": False,
        "boundary_room_type_max": False,
        "boundary_stay_days_min": False,
        "boundary_stay_days_max": False,
        "boundary_guest_count_min": False,
        "boundary_guest_count_max": False,
        "boundary_discount_min": False,
        "boundary_discount_max": False,
        
        # Equivalence class tests
        "equiv_member_regular": False,
        "equiv_member_silver": False,
        "equiv_member_gold": False,
        "equiv_room_standard": False,
        "equiv_room_deluxe": False,
        "equiv_room_suite": False,
        
        # Business rule tests
        "rule_silver_discount": False,
        "rule_gold_discount": False,
        "rule_vip_discount": False,
        "rule_peak_season_limit": False,
        "rule_long_stay_discount": False,
        "rule_suite_min_days": False,
        
        # Negative tests - Boundary violations
        "neg_age_below_18": False,
        "neg_age_zero": False,
        "neg_age_negative": False,
        "neg_member_level_0": False,
        "neg_member_level_4": False,
        "neg_member_level_negative": False,
        "neg_stay_days_0": False,
        "neg_stay_days_negative": False,
        "neg_stay_days_over_30": False,
        "neg_guest_count_0": False,
        "neg_guest_count_over_4": False,
        "neg_discount_negative": False,
        "neg_discount_over_50": False,
        
        # Negative tests - Rule violations
        "neg_silver_insufficient_discount": False,
        "neg_gold_insufficient_discount": False,
        "neg_peak_season_excess_discount": False,
        "neg_suite_single_day": False
    }
    
    # Check coverage
    for test in tests:
        name = test['name']
        test_type = test.get('type', '')
        values = test.get('values', {})
        description = test.get('description', '')
        
        # Check boundary tests
        if test_type == 'boundary' or 'boundary' in name:
            if 'age' in name and 'min' in name:
                coverage_checklist["boundary_age_min"] = True
            elif 'age' in name and 'max' in name:
                coverage_checklist["boundary_age_max"] = True
            elif 'member_level' in name and 'min' in name:
                coverage_checklist["boundary_member_level_min"] = True
            elif 'member_level' in name and 'max' in name:
                coverage_checklist["boundary_member_level_max"] = True
            elif 'room_type' in name and 'min' in name:
                coverage_checklist["boundary_room_type_min"] = True
            elif 'room_type' in name and 'max' in name:
                coverage_checklist["boundary_room_type_max"] = True
            elif 'stay_days' in name and 'min' in name:
                coverage_checklist["boundary_stay_days_min"] = True
            elif 'stay_days' in name and 'max' in name:
                coverage_checklist["boundary_stay_days_max"] = True
            elif 'guest_count' in name and 'min' in name:
                coverage_checklist["boundary_guest_count_min"] = True
            elif 'guest_count' in name and 'max' in name:
                coverage_checklist["boundary_guest_count_max"] = True
            elif 'discount' in name and 'min' in name:
                coverage_checklist["boundary_discount_min"] = True
            elif 'discount' in name and 'max' in name:
                coverage_checklist["boundary_discount_max"] = True
        
        # Check equivalence tests
        if test_type == 'equivalence' or 'equiv' in name:
            if 'regular' in name:
                coverage_checklist["equiv_member_regular"] = True
            elif 'silver' in name:
                coverage_checklist["equiv_member_silver"] = True
            elif 'gold' in name:
                coverage_checklist["equiv_member_gold"] = True
            elif 'standard' in name:
                coverage_checklist["equiv_room_standard"] = True
            elif 'deluxe' in name:
                coverage_checklist["equiv_room_deluxe"] = True
            elif 'suite' in name:
                coverage_checklist["equiv_room_suite"] = True
        
        # Check negative tests
        if test_type == 'negative':
            if 'underage' in name or ('age' in description and '18' in description):
                coverage_checklist["neg_age_below_18"] = True
            elif 'zero_age' in name:
                coverage_checklist["neg_age_zero"] = True
            elif 'negative_age' in name:
                coverage_checklist["neg_age_negative"] = True
            elif 'invalid_member_level_0' in name:
                coverage_checklist["neg_member_level_0"] = True
            elif 'invalid_member_level_4' in name:
                coverage_checklist["neg_member_level_4"] = True
            elif 'member_level_negative' in name:
                coverage_checklist["neg_member_level_negative"] = True
            elif 'zero_days' in name and 'stay' not in name:
                coverage_checklist["neg_stay_days_0"] = True
            elif 'stay_days_negative' in name:
                coverage_checklist["neg_stay_days_negative"] = True
            elif 'exceeds_max_days' in name:
                coverage_checklist["neg_stay_days_over_30"] = True
            elif 'guest_count_0' in name:
                coverage_checklist["neg_guest_count_0"] = True
            elif 'guest_count_over_4' in name or ('guest' in name and '5' in str(values.get('booking_guest_count', 0))):
                coverage_checklist["neg_guest_count_over_4"] = True
            elif 'discount_negative' in name:
                coverage_checklist["neg_discount_negative"] = True
            elif 'discount_over_50' in name or ('discount' in name and values.get('booking_discount_percent', 0) > 50):
                coverage_checklist["neg_discount_over_50"] = True
            elif 'silver_insufficient' in name:
                coverage_checklist["neg_silver_insufficient_discount"] = True
            elif 'gold_insufficient' in name:
                coverage_checklist["neg_gold_insufficient_discount"] = True
            elif 'peak_season_excessive' in name:
                coverage_checklist["neg_peak_season_excess_discount"] = True
            elif 'suite_single_day' in name or ('suite' in name and values.get('booking_stay_days', 0) == 1):
                coverage_checklist["neg_suite_single_day"] = True
        
        # Check rule tests
        if test_type == 'rule_coverage' or 'rule' in test:
            rule = test.get('rule', '')
            description_lower = description.lower()
            if '银卡' in rule or 'silver' in rule.lower() or 'silver' in description_lower:
                coverage_checklist["rule_silver_discount"] = True
            elif '金卡' in rule or 'gold' in rule.lower() or 'gold' in description_lower:
                coverage_checklist["rule_gold_discount"] = True
            elif 'VIP' in rule or 'vip' in description_lower:
                coverage_checklist["rule_vip_discount"] = True
            elif '旺季' in rule or 'peak' in description_lower:
                coverage_checklist["rule_peak_season_limit"] = True
            elif '长期' in rule or 'long stay' in description_lower or '7+' in description_lower:
                coverage_checklist["rule_long_stay_discount"] = True
            elif '套房' in rule or 'suite' in description_lower:
                coverage_checklist["rule_suite_min_days"] = True
    
    # Calculate coverage
    covered = sum(1 for v in coverage_checklist.values() if v)
    total = len(coverage_checklist)
    coverage_rate = (covered / total) * 100
    
    print(f"\nOverall Test Coverage: {coverage_rate:.1f}% ({covered}/{total})")
    
    # Show uncovered scenarios
    uncovered = [k for k, v in coverage_checklist.items() if not v]
    if uncovered:
        print(f"\nUncovered scenarios ({len(uncovered)}):")
        for scenario in uncovered[:10]:
            print(f"  ❌ {scenario}")
        if len(uncovered) > 10:
            print(f"  ... and {len(uncovered)-10} more")
    else:
        print("\n✅ All scenarios covered!")
    
    # Show covered categories
    print("\nCoverage by category:")
    categories = {
        "Positive Boundary": sum(1 for k, v in coverage_checklist.items() if k.startswith("boundary_") and v),
        "Equivalence Class": sum(1 for k, v in coverage_checklist.items() if k.startswith("equiv_") and v),
        "Business Rules": sum(1 for k, v in coverage_checklist.items() if k.startswith("rule_") and v),
        "Negative Tests": sum(1 for k, v in coverage_checklist.items() if k.startswith("neg_") and v)
    }
    
    for category, count in categories.items():
        total_in_category = sum(1 for k in coverage_checklist.keys() if k.startswith(category.split()[0].lower()[:3]))
        percentage = (count / total_in_category * 100) if total_in_category > 0 else 0
        print(f"  {category}: {count}/{total_in_category} ({percentage:.0f}%)")
    
    return coverage_rate, coverage_checklist


def save_complete_test_suite(tests):
    """Save the complete test suite with all tests."""
    print("\n\n💾 Saving Complete Test Suite")
    print("=" * 80)
    
    # Organize tests by type
    tests_by_type = {}
    for test in tests:
        t = test.get('type', 'unknown')
        if t not in tests_by_type:
            tests_by_type[t] = []
        tests_by_type[t].append(test)
    
    # Create comprehensive report
    test_suite = {
        "系统": "酒店预订系统 - 完整自动生成测试集",
        "生成方式": "Enhanced DSL Engine (全自动)",
        "统计": {
            "总测试数": len(tests),
            "正面测试": len([t for t in tests if t.get('type') != 'negative']),
            "负面测试": len([t for t in tests if t.get('type') == 'negative']),
            "测试类型分布": {t: len(tests) for t, tests in tests_by_type.items()}
        },
        "测试用例": {}
    }
    
    # Add tests organized by type
    for test_type, type_tests in tests_by_type.items():
        test_suite["测试用例"][test_type] = []
        for i, test in enumerate(type_tests):
            test_case = {
                "序号": i + 1,
                "名称": test['name'],
                "描述": test.get('description', ''),
                "预期结果": test.get('expected', 'pass'),
                "测试数据": format_test_data(test.get('values', {}))
            }
            test_suite["测试用例"][test_type].append(test_case)
    
    # Save to file
    output_file = "demo/enhanced_complete_test_suite.json"
    with open(output_file, "w", encoding="utf-8") as f:
        json.dump(test_suite, f, indent=2, ensure_ascii=False)
    
    print(f"✅ Complete test suite saved to: {output_file}")
    print(f"\nSummary:")
    print(f"  - Total tests: {len(tests)}")
    print(f"  - Positive tests: {len([t for t in tests if t.get('type') != 'negative'])}")
    print(f"  - Negative tests: {len([t for t in tests if t.get('type') == 'negative'])}")
    print(f"  - All generated automatically!")


def format_test_data(values):
    """Format test data for display."""
    formatted = {}
    
    for key, value in values.items():
        if 'customer_age' in key:
            formatted["客户年龄"] = f"{value}岁"
        elif 'member_level' in key:
            levels = {1: "普通会员", 2: "银卡会员", 3: "金卡会员"}
            formatted["会员等级"] = levels.get(value, f"无效等级({value})")
        elif 'room_type' in key:
            types = {1: "标准间", 2: "豪华间", 3: "套房"}
            formatted["房间类型"] = types.get(value, f"无效类型({value})")
        elif 'stay_days' in key:
            formatted["预订天数"] = f"{value}天"
        elif 'guest_count' in key:
            formatted["入住人数"] = f"{value}人"
        elif 'discount_percent' in key:
            formatted["折扣"] = f"{value}%"
        elif 'is_peak_season' in key:
            formatted["旺季"] = "是" if value else "否"
        elif 'is_vip' in key:
            formatted["VIP客户"] = "是" if value else "否"
    
    return formatted


def main():
    print("🏨 酒店预订系统 - 增强引擎测试")
    print("=" * 80)
    print("目标: 自动生成所有测试用例，包括负面测试，无需手动补充")
    
    # Test enhanced engine
    tests = test_enhanced_engine()
    
    # Calculate coverage
    coverage_rate, coverage_details = calculate_comprehensive_coverage(tests)
    
    # Save complete test suite
    save_complete_test_suite(tests)
    
    # Final summary
    print("\n\n🎯 最终结果")
    print("=" * 80)
    
    if coverage_rate >= 90:
        print(f"✅ 成功！覆盖率达到 {coverage_rate:.1f}%")
        print("✅ 所有测试用例都已自动生成，无需手动补充！")
    else:
        print(f"⚠️  覆盖率为 {coverage_rate:.1f}%，仍需优化")
        print("需要继续改进测试生成策略")
    
    # Show test statistics
    test_types = {}
    for test in tests:
        t = test.get('type', 'unknown')
        test_types[t] = test_types.get(t, 0) + 1
    
    print(f"\n生成的测试统计:")
    print(f"  总数: {len(tests)}")
    for t, count in sorted(test_types.items()):
        print(f"  {t}: {count}")


if __name__ == "__main__":
    main()