#!/usr/bin/env python3
"""Debug script to check constraint generation"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from dsl_test_generator import DSLParser

# Parse the insurance DSL
parser = DSLParser()
model = parser.parse_file("demo/insurance_claim_system.yaml")

print(f"Domain: {model.domain}")
print(f"\nNumber of constraints: {len(model.constraints)}")
print("\nConstraints:")
for i, constraint in enumerate(model.constraints):
    print(f"\n{i+1}. {constraint.description}")
    print(f"   Expression: {constraint.expression}")