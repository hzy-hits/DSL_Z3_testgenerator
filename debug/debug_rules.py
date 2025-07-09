#!/usr/bin/env python3
"""Debug script to check rule generation"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from dsl_test_generator import DSLParser

# Parse the insurance DSL
parser = DSLParser()
model = parser.parse_file("demo/insurance_claim_system.yaml")

print(f"Domain: {model.domain}")
print(f"Number of rules: {len(model.rules)}")

# Also print attributes to see variable names
print("\nAttributes (with full names):")
for entity in model.entities:
    print(f"\n{entity.name}:")
    for attr in entity.attributes:
        full_name = f"{entity.name.lower()}_{attr.name}"
        print(f"  - {attr.name} -> {full_name}")

print("\nRules:")
for i, rule in enumerate(model.rules):
    print(f"\n{i+1}. {rule.name}")
    print(f"   Condition: {rule.condition}")
    print(f"   Action: {rule.action}")
    print(f"   Description: {rule.description}")