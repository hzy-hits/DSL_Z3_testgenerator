"""Command-line interface for DSL Test Generator."""

import argparse
import json
import sys
from pathlib import Path

from . import DSLEngine, DSLParser


def main():
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        description="Generate test cases from DSL specifications"
    )
    
    parser.add_argument(
        "input",
        type=str,
        help="Path to DSL specification file (YAML)"
    )
    
    parser.add_argument(
        "-o", "--output",
        type=str,
        help="Output file for test cases (JSON format)"
    )
    
    parser.add_argument(
        "-f", "--format",
        choices=["json", "yaml", "table"],
        default="json",
        help="Output format (default: json)"
    )
    
    parser.add_argument(
        "-v", "--verbose",
        action="store_true",
        help="Enable verbose output"
    )
    
    args = parser.parse_args()
    
    # Parse DSL
    try:
        dsl_parser = DSLParser()
        model = dsl_parser.parse_file(args.input)
        
        if args.verbose:
            print(f"Parsed DSL for domain: {model.domain}")
            print(f"  Entities: {len(model.entities)}")
            print(f"  Constraints: {len(model.constraints)}")
            print(f"  Rules: {len(model.rules)}")
    except Exception as e:
        print(f"Error parsing DSL: {e}", file=sys.stderr)
        return 1
    
    # Generate tests
    try:
        engine = DSLEngine()
        test_cases = engine.generate_tests(model)
        
        if args.verbose:
            print(f"\nGenerated {len(test_cases)} test cases")
    except Exception as e:
        print(f"Error generating tests: {e}", file=sys.stderr)
        return 1
    
    # Output results
    if args.format == "json":
        output = json.dumps(test_cases, indent=2)
    elif args.format == "yaml":
        import yaml
        output = yaml.dump(test_cases, default_flow_style=False)
    else:  # table
        output = _format_as_table(test_cases)
    
    if args.output:
        Path(args.output).write_text(output)
        if args.verbose:
            print(f"Test cases written to: {args.output}")
    else:
        print(output)
    
    return 0


def _format_as_table(test_cases):
    """Format test cases as a simple table."""
    lines = ["Test Cases", "=" * 80]
    
    for i, tc in enumerate(test_cases, 1):
        lines.append(f"\nTest {i}: {tc.get('name', 'unnamed')}")
        lines.append(f"Type: {tc.get('type', 'unknown')}")
        if 'description' in tc:
            lines.append(f"Description: {tc['description']}")
        lines.append("Values:")
        
        for key, value in tc.get('values', {}).items():
            lines.append(f"  {key}: {value}")
    
    return "\n".join(lines)


if __name__ == "__main__":
    sys.exit(main())