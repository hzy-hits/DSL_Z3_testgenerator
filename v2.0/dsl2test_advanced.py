#!/usr/bin/env python3
"""
DSL Test Generator V2.0 - Advanced CLI with combination analysis

Usage:
    python dsl2test_advanced.py --input model.yaml --output tests.json --analyze-combinations
"""

import argparse
import sys
import json
import logging
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent))

from src.layers import DSLParser
from src.core import TestGenerator
from src.strategies.advanced_test_planner import AdvancedTestPlanner
from src.strategies.combination_analyzer import CombinationAnalyzer
from src.utils import OutputFormatter


def setup_logging(verbose: bool):
    """Setup logging configuration"""
    level = logging.DEBUG if verbose else logging.INFO
    logging.basicConfig(
        level=level,
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
    )


def main():
    """Main CLI entry point"""
    parser = argparse.ArgumentParser(
        description="DSL Test Generator V2.0 - Advanced version with combination analysis"
    )
    
    # Required arguments
    parser.add_argument(
        "--input", "-i",
        required=True,
        help="Input DSL YAML file"
    )
    
    parser.add_argument(
        "--output", "-o",
        required=True,
        help="Output file path"
    )
    
    # Optional arguments
    parser.add_argument(
        "--format", "-f",
        choices=["json", "junit", "csv", "markdown", "pytest", "unittest"],
        default="json",
        help="Output format (default: json)"
    )
    
    parser.add_argument(
        "--analyze-combinations",
        action="store_true",
        help="Analyze rule combinations and show potential conflicts"
    )
    
    parser.add_argument(
        "--use-advanced-planner",
        action="store_true",
        help="Use advanced test planner with combination support"
    )
    
    parser.add_argument(
        "--max-tests",
        type=int,
        help="Maximum number of tests to generate"
    )
    
    parser.add_argument(
        "--no-minimize",
        action="store_true",
        help="Disable test minimization"
    )
    
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Enable verbose logging"
    )
    
    args = parser.parse_args()
    
    # Setup logging
    setup_logging(args.verbose)
    logger = logging.getLogger(__name__)
    
    try:
        # Parse DSL file
        logger.info(f"Parsing DSL file: {args.input}")
        parser = DSLParser()
        model = parser.parse_file(args.input)
        logger.info(f"Successfully parsed DSL for domain: {model.domain}")
        
        # Combination analysis
        if args.analyze_combinations:
            print("\n🔍 Analyzing rule combinations...")
            analyzer = CombinationAnalyzer(model)
            
            # Get relationships
            relations = analyzer.analyze_rule_relationships()
            conflicts = [r for r in relations if r.relation_type == "conflicting"]
            
            if conflicts:
                print("\n⚠️  Conflicts found:")
                for rel in conflicts:
                    print(f"  ❌ {rel.rule1.name} ↔ {rel.rule2.name}")
                    print(f"     Reason: {rel.conflict_reason}")
                    print(f"     Shared: {', '.join(rel.shared_attributes)}")
            else:
                print("  ✅ No rule conflicts found")
            
            # Get scenarios
            scenarios = analyzer.generate_combination_scenarios()
            print(f"\n📊 Combination scenarios: {len(scenarios)}")
            
            # Get suggestions
            suggestions = analyzer.suggest_critical_combinations()
            if suggestions:
                print(f"\n💡 Critical test suggestions: {len(suggestions)}")
                for s in suggestions[:3]:
                    print(f"  - {s['description']}")
        
        # Choose planner
        if args.use_advanced_planner:
            logger.info("Using advanced test planner...")
            from src.strategies.test_planner import TestPlanner
            planner = AdvancedTestPlanner(model)
        else:
            logger.info("Using standard test planner...")
            from src.strategies.test_planner import TestPlanner
            planner = TestPlanner(model)
        
        # Generate tests
        logger.info("Starting test generation...")
        generator = TestGenerator(
            minimize=not args.no_minimize,
            verify_all=True
        )
        
        coverage_goals = {
            'constraint': 1.0,
            'rule': 1.0,
            'boundary': 1.0
        }
        
        result = generator.generate(
            model=model,
            coverage_goals=coverage_goals,
            max_tests=args.max_tests
        )
        
        # Log results
        logger.info(f"Generated {len(result.test_cases)} test cases")
        logger.info(f"Coverage - Constraints: {result.coverage_report.constraint_coverage:.2%}, "
                   f"Rules: {result.coverage_report.rule_coverage:.2%}, "
                   f"Boundaries: {result.coverage_report.boundary_coverage:.2%}")
        
        # Format output
        formatter = OutputFormatter()
        
        if args.format == "json":
            output = formatter.format_json(result, model)
        elif args.format == "junit":
            output = formatter.format_junit(result, model)
        elif args.format == "csv":
            output = formatter.format_csv(result, model)
        elif args.format == "markdown":
            output = formatter.format_markdown(result, model)
        elif args.format in ["pytest", "unittest"]:
            output = formatter.format_python(result, model, framework=args.format)
        
        # Write output
        output_path = Path(args.output)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(output)
        
        logger.info(f"Test cases written to: {args.output}")
        
        # Print summary
        print(f"\n✅ Test Generation Complete!")
        print(f"Domain: {model.domain}")
        print(f"Tests generated: {len(result.test_cases)}")
        print(f"Constraint coverage: {result.coverage_report.constraint_coverage:.2%}")
        print(f"Rule coverage: {result.coverage_report.rule_coverage:.2%}")
        print(f"Boundary coverage: {result.coverage_report.boundary_coverage:.2%}")
        
    except Exception as e:
        logger.error(f"Error: {e}", exc_info=args.verbose)
        sys.exit(1)


if __name__ == "__main__":
    main()