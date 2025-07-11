#!/usr/bin/env python3
"""
测试V8生成器在所有示例文件上的表现
"""

import os
import json
import subprocess
from pathlib import Path

def test_example(yaml_file: str, output_dir: str):
    """测试单个示例文件"""
    file_name = Path(yaml_file).stem
    output_file = os.path.join(output_dir, f"v8_{file_name}.json")
    
    # 运行生成器
    cmd = [
        'python', 'src/generators/v8_practical.py',
        yaml_file, 
        '-o', output_file
    ]
    
    try:
        result = subprocess.run(cmd, capture_output=True, text=True)
        
        if result.returncode == 0:
            # 读取生成的测试
            with open(output_file, 'r') as f:
                data = json.load(f)
            
            total_tests = data.get('total_tests', 0)
            print(f"✓ {file_name}: {total_tests} tests generated")
            
            # 验证测试质量
            validate_tests(data['tests'], file_name)
            
            return True
        else:
            print(f"✗ {file_name}: Generation failed")
            print(f"  Error: {result.stderr}")
            return False
            
    except Exception as e:
        print(f"✗ {file_name}: Exception - {str(e)}")
        return False

def validate_tests(tests: list, file_name: str):
    """验证测试质量"""
    issues = []
    
    for test in tests:
        test_data = test.get('test_data', {})
        
        # 检查基本结构
        if not test.get('test_name'):
            issues.append(f"Test missing name")
        if not test.get('test_type'):
            issues.append(f"Test missing type")
        
        # 检查数据完整性
        for key, value in test_data.items():
            if value is None and test['test_type'] != 'negative':
                issues.append(f"Test {test.get('test_name')}: {key} is None")
    
    if issues:
        print(f"  Quality issues in {file_name}:")
        for issue in issues[:3]:  # 只显示前3个问题
            print(f"    - {issue}")

def main():
    # 创建输出目录
    output_dir = 'test_outputs/v8_batch'
    os.makedirs(output_dir, exist_ok=True)
    
    # 获取所有示例文件
    example_files = []
    for root, dirs, files in os.walk('examples'):
        for file in files:
            if file.endswith('.yaml'):
                example_files.append(os.path.join(root, file))
    
    print(f"Testing V8 generator on {len(example_files)} example files...\n")
    
    # 测试每个文件
    success_count = 0
    for yaml_file in sorted(example_files):
        if test_example(yaml_file, output_dir):
            success_count += 1
    
    # 打印总结
    print(f"\nSummary:")
    print(f"  Total files: {len(example_files)}")
    print(f"  Successful: {success_count}")
    print(f"  Failed: {len(example_files) - success_count}")
    print(f"  Success rate: {success_count/len(example_files)*100:.1f}%")

if __name__ == '__main__':
    main()