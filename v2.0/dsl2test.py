#!/usr/bin/env python3
"""
DSL Test Generator V2.0 - CLI Interface

Usage:
    python dsl2test.py --input model.yaml --output tests.json
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
        description="DSL Test Generator V2.0 - Generate minimal correct test cases"
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
        "--coverage-goal",
        type=float,
        default=1.0,
        help="Coverage goal (0.0-1.0, default: 1.0)"
    )
    
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Enable verbose logging"
    )
    
    parser.add_argument(
        "--validate-only",
        action="store_true",
        help="Only validate the DSL model without generating tests"
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
        
        # Validate only mode
        if args.validate_only:
            errors = model.validate()
            if errors:
                print("Validation errors:")
                for error in errors:
                    print(f"  - {error}")
                sys.exit(1)
            else:
                print("DSL model is valid!")
                sys.exit(0)
        
        # Generate tests
        logger.info("Starting test generation...")
        generator = TestGenerator(
            minimize=not args.no_minimize,
            verify_all=True
        )
        
        coverage_goals = {
            'constraint': args.coverage_goal,
            'rule': args.coverage_goal,
            'boundary': args.coverage_goal
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
        
        if result.warnings:
            logger.warning(f"Generation warnings: {len(result.warnings)}")
            for warning in result.warnings:
                logger.warning(f"  - {warning}")
        
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
        else:
            raise ValueError(f"Unknown format: {args.format}")
        
        # Write output
        output_path = Path(args.output)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(output)
        
        logger.info(f"Test cases written to: {args.output}")
        
        # Print summary
        print(f"\nTest Generation Complete!")
        print(f"Domain: {model.domain}")
        print(f"Tests generated: {len(result.test_cases)}")
        print(f"Failed objectives: {len(result.failed_objectives)}")
        print(f"Constraint coverage: {result.coverage_report.constraint_coverage:.2%}")
        print(f"Rule coverage: {result.coverage_report.rule_coverage:.2%}")
        print(f"Boundary coverage: {result.coverage_report.boundary_coverage:.2%}")
        
        if result.failed_objectives:
            print(f"\nWarning: {len(result.failed_objectives)} objectives could not be satisfied")
        
    except Exception as e:
        logger.error(f"Error: {e}", exc_info=args.verbose)
        sys.exit(1)


if __name__ == "__main__":
    main()