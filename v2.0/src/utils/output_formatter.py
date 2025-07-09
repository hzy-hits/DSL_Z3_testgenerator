"""
Output Formatter for V2.0

Formats test cases for different output formats.
"""

import json
from typing import List, Dict, Any, Optional
from datetime import datetime
import xml.etree.ElementTree as ET
from xml.dom import minidom

from ..core.models import TestCase, CoverageReport, DSLModel
from ..core.test_generator import GenerationResult


class OutputFormatter:
    """Format test cases for different targets"""
    
    def format_json(self, 
                   result: GenerationResult,
                   model: DSLModel,
                   pretty: bool = True) -> str:
        """Format as JSON"""
        output = {
            "metadata": {
                "domain": model.domain,
                "generated_at": datetime.now().isoformat(),
                "total_tests": len(result.test_cases),
                "coverage": {
                    "constraints": f"{result.coverage_report.constraint_coverage:.2%}",
                    "rules": f"{result.coverage_report.rule_coverage:.2%}",
                    "boundaries": f"{result.coverage_report.boundary_coverage:.2%}"
                }
            },
            "warnings": result.warnings,
            "test_cases": []
        }
        
        for test in result.test_cases:
            test_data = {
                "name": test.name,
                "objective": {
                    "type": test.objective.type,
                    "target": test.objective.target,
                    "reason": test.objective.reason
                },
                "test_data": test.values,
                "expected": test.expected,
                "coverage": list(test.coverage),
                "validation_errors": test.validation_errors
            }
            output["test_cases"].append(test_data)
        
        if pretty:
            return json.dumps(output, indent=2, ensure_ascii=False)
        else:
            return json.dumps(output, ensure_ascii=False)
    
    def format_junit(self, 
                    result: GenerationResult,
                    model: DSLModel) -> str:
        """Format as JUnit XML"""
        # Create test suite
        testsuite = ET.Element("testsuite")
        testsuite.set("name", f"{model.domain} Test Suite")
        testsuite.set("tests", str(len(result.test_cases)))
        testsuite.set("timestamp", datetime.now().isoformat())
        
        # Add test cases
        failures = 0
        for test in result.test_cases:
            testcase = ET.SubElement(testsuite, "testcase")
            testcase.set("name", test.name)
            testcase.set("classname", model.domain.replace(" ", "_"))
            
            # Add test data as system-out
            system_out = ET.SubElement(testcase, "system-out")
            system_out.text = json.dumps({
                "objective": test.objective.reason,
                "test_data": test.values,
                "coverage": list(test.coverage)
            }, indent=2)
            
            # Add failures if any
            if test.validation_errors:
                failures += 1
                failure = ET.SubElement(testcase, "failure")
                failure.set("message", "; ".join(test.validation_errors))
        
        testsuite.set("failures", str(failures))
        
        # Pretty print
        rough_string = ET.tostring(testsuite, encoding='unicode')
        reparsed = minidom.parseString(rough_string)
        return reparsed.toprettyxml(indent="  ")
    
    def format_csv(self, 
                  result: GenerationResult,
                  model: DSLModel) -> str:
        """Format as CSV"""
        import csv
        import io
        
        output = io.StringIO()
        
        # Get all attribute names
        all_attrs = [attr.full_name for attr in model.get_all_attributes()]
        
        # Create header
        header = ["test_name", "objective_type", "objective_reason"] + all_attrs + ["expected", "is_valid"]
        
        writer = csv.DictWriter(output, fieldnames=header)
        writer.writeheader()
        
        # Write test cases
        for test in result.test_cases:
            row = {
                "test_name": test.name,
                "objective_type": test.objective.type,
                "objective_reason": test.objective.reason,
                "expected": test.expected,
                "is_valid": "true" if not test.validation_errors else "false"
            }
            
            # Add test data
            for attr in all_attrs:
                row[attr] = test.values.get(attr, "")
            
            writer.writerow(row)
        
        return output.getvalue()
    
    def format_markdown(self, 
                       result: GenerationResult,
                       model: DSLModel) -> str:
        """Format as Markdown report"""
        lines = []
        
        # Header
        lines.append(f"# Test Generation Report - {model.domain}")
        lines.append("")
        lines.append(f"Generated at: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        lines.append("")
        
        # Summary
        lines.append("## Summary")
        lines.append("")
        lines.append(f"- Total test cases: {len(result.test_cases)}")
        lines.append(f"- Failed objectives: {len(result.failed_objectives)}")
        lines.append(f"- Warnings: {len(result.warnings)}")
        lines.append("")
        
        # Coverage
        lines.append("## Coverage")
        lines.append("")
        lines.append(f"- Constraint coverage: {result.coverage_report.constraint_coverage:.2%}")
        lines.append(f"- Rule coverage: {result.coverage_report.rule_coverage:.2%}")
        lines.append(f"- Boundary coverage: {result.coverage_report.boundary_coverage:.2%}")
        lines.append("")
        
        # Warnings
        if result.warnings:
            lines.append("## Warnings")
            lines.append("")
            for warning in result.warnings:
                lines.append(f"- {warning}")
            lines.append("")
        
        # Test Cases
        lines.append("## Test Cases")
        lines.append("")
        
        for i, test in enumerate(result.test_cases, 1):
            lines.append(f"### {i}. {test.name}")
            lines.append("")
            lines.append(f"**Objective:** {test.objective.reason}")
            lines.append("")
            lines.append("**Test Data:**")
            lines.append("```json")
            lines.append(json.dumps(test.values, indent=2))
            lines.append("```")
            lines.append("")
            
            if test.validation_errors:
                lines.append("**Validation Errors:**")
                for error in test.validation_errors:
                    lines.append(f"- {error}")
                lines.append("")
            
            lines.append(f"**Coverage:** {', '.join(sorted(test.coverage))}")
            lines.append("")
        
        # Failed Objectives
        if result.failed_objectives:
            lines.append("## Failed Objectives")
            lines.append("")
            for obj in result.failed_objectives:
                lines.append(f"- {obj.reason}")
            lines.append("")
        
        return "\n".join(lines)
    
    def format_python(self, 
                     result: GenerationResult,
                     model: DSLModel,
                     framework: str = "pytest") -> str:
        """Generate Python test code"""
        lines = []
        
        # Header
        lines.append(f'"""')
        lines.append(f'Generated tests for {model.domain}')
        lines.append(f'Generated at: {datetime.now().isoformat()}')
        lines.append(f'"""')
        lines.append("")
        
        if framework == "pytest":
            lines.append("import pytest")
            lines.append("")
            
            # Generate test class
            class_name = model.domain.replace(" ", "").replace("-", "_") + "Tests"
            lines.append(f"class Test{class_name}:")
            lines.append("")
            
            for test in result.test_cases:
                # Generate test method
                method_name = test.name.replace("-", "_")
                lines.append(f"    def {method_name}(self):")
                lines.append(f'        """')
                lines.append(f"        {test.objective.reason}")
                lines.append(f'        """')
                lines.append(f"        # Test data")
                lines.append(f"        data = {json.dumps(test.values, indent=8)[:-1]}        }}")
                lines.append("")
                lines.append(f"        # TODO: Implement actual test logic")
                lines.append(f"        # This test covers: {', '.join(sorted(test.coverage))}")
                
                if test.validation_errors:
                    lines.append(f"        # WARNING: Validation errors: {test.validation_errors}")
                
                lines.append(f"        assert True  # Placeholder")
                lines.append("")
        
        elif framework == "unittest":
            lines.append("import unittest")
            lines.append("")
            
            # Generate test class
            class_name = model.domain.replace(" ", "").replace("-", "_") + "Tests"
            lines.append(f"class {class_name}(unittest.TestCase):")
            lines.append("")
            
            for test in result.test_cases:
                # Generate test method
                method_name = test.name.replace("-", "_")
                lines.append(f"    def {method_name}(self):")
                lines.append(f'        """')
                lines.append(f"        {test.objective.reason}")
                lines.append(f'        """')
                lines.append(f"        # Test data")
                lines.append(f"        data = {json.dumps(test.values, indent=8)[:-1]}        }}")
                lines.append("")
                lines.append(f"        # TODO: Implement actual test logic")
                lines.append(f"        # This test covers: {', '.join(sorted(test.coverage))}")
                
                if test.validation_errors:
                    lines.append(f"        # WARNING: Validation errors: {test.validation_errors}")
                
                lines.append(f"        self.assertTrue(True)  # Placeholder")
                lines.append("")
            
            lines.append("")
            lines.append("if __name__ == '__main__':")
            lines.append("    unittest.main()")
        
        return "\n".join(lines)