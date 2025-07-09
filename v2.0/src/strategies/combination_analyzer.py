"""
Combination Analysis for V2.0

Analyzes rule combinations to detect conflicts and suggest critical test scenarios.
"""

from typing import List, Dict, Set, Tuple, Optional
from dataclasses import dataclass
import logging
import re

from ..core.models import DSLModel, Rule


logger = logging.getLogger(__name__)


@dataclass
class RuleRelation:
    """Relationship between two rules"""
    rule1: Rule
    rule2: Rule
    relation_type: str  # 'conflicting', 'complementary', 'independent'
    shared_attributes: Set[str]
    conflict_reason: Optional[str] = None


@dataclass 
class CombinationScenario:
    """A scenario combining multiple rules"""
    name: str
    rules: List[Rule]
    description: str
    priority: int  # Higher = more important to test


class CombinationAnalyzer:
    """Analyzes rule combinations for conflicts and important scenarios"""
    
    def __init__(self, model: DSLModel):
        self.model = model
        self.rule_relations = {}  # Cache for analyzed relations
        
    def analyze_rule_relationships(self) -> List[RuleRelation]:
        """Analyze all pairs of rules to find relationships"""
        relations = []
        rules = list(self.model.rules.values())
        
        for i in range(len(rules)):
            for j in range(i + 1, len(rules)):
                relation = self._analyze_pair(rules[i], rules[j])
                relations.append(relation)
                self.rule_relations[(rules[i].name, rules[j].name)] = relation
                
        return relations
    
    def _analyze_pair(self, rule1: Rule, rule2: Rule) -> RuleRelation:
        """Analyze relationship between two rules"""
        # Extract attributes used in each rule
        attrs1 = self._extract_attributes(rule1)
        attrs2 = self._extract_attributes(rule2)
        shared = attrs1.intersection(attrs2)
        
        # Check for conflicts
        conflict = self._check_conflict(rule1, rule2, shared)
        
        if conflict:
            return RuleRelation(
                rule1=rule1,
                rule2=rule2,
                relation_type='conflicting',
                shared_attributes=shared,
                conflict_reason=conflict
            )
        elif shared:
            return RuleRelation(
                rule1=rule1,
                rule2=rule2,
                relation_type='complementary',
                shared_attributes=shared
            )
        else:
            return RuleRelation(
                rule1=rule1,
                rule2=rule2,
                relation_type='independent',
                shared_attributes=set()
            )
    
    def _extract_attributes(self, rule: Rule) -> Set[str]:
        """Extract all attributes referenced in a rule"""
        attributes = set()
        
        # Extract from condition
        attributes.update(self._extract_from_expression(rule.condition))
        
        # Extract from consequence
        attributes.update(self._extract_from_expression(rule.consequence))
        
        return attributes
    
    def _extract_from_expression(self, expr: str) -> Set[str]:
        """Extract attribute names from an expression"""
        # Pattern to match attribute names (entity_attribute format)
        pattern = r'\b(\w+_\w+)\b'
        matches = re.findall(pattern, expr)
        
        # Filter to only include valid attributes
        valid_attrs = set()
        for match in matches:
            if self.model.get_attribute_by_full_name(match):
                valid_attrs.add(match)
                
        return valid_attrs
    
    def _check_conflict(self, rule1: Rule, rule2: Rule, 
                       shared_attrs: Set[str]) -> Optional[str]:
        """Check if two rules conflict"""
        if not shared_attrs:
            return None
            
        # Check for conflicting consequences on shared attributes
        for attr in shared_attrs:
            conflict = self._check_attribute_conflict(
                rule1.consequence, rule2.consequence, attr
            )
            if conflict:
                return f"Conflicting consequences for {attr}"
                
        # Check for conflicting conditions
        if self._are_conditions_opposite(rule1.condition, rule2.condition):
            return "Opposite conditions"
            
        return None
    
    def _check_attribute_conflict(self, cons1: str, cons2: str, 
                                 attr: str) -> bool:
        """Check if two consequences conflict for an attribute"""
        # Extract constraints on the attribute from both consequences
        pattern1 = rf'{attr}\s*([><=]+)\s*(\d+(?:\.\d+)?)'
        
        matches1 = re.findall(pattern1, cons1)
        matches2 = re.findall(pattern1, cons2)
        
        if not matches1 or not matches2:
            return False
            
        # Check if constraints are conflicting
        for op1, val1 in matches1:
            for op2, val2 in matches2:
                if self._are_constraints_conflicting(
                    op1, float(val1), op2, float(val2)
                ):
                    return True
                    
        return False
    
    def _are_constraints_conflicting(self, op1: str, val1: float,
                                   op2: str, val2: float) -> bool:
        """Check if two constraints conflict"""
        # Examples of conflicts:
        # x >= 20 and x <= 10
        # x > 15 and x < 10
        
        if '>=' in op1 and '<=' in op2:
            return val1 > val2
        elif '<=' in op1 and '>=' in op2:
            return val1 < val2
        elif '>' in op1 and '<' in op2:
            return val1 >= val2
        elif '<' in op1 and '>' in op2:
            return val1 <= val2
            
        return False
    
    def _are_conditions_opposite(self, cond1: str, cond2: str) -> bool:
        """Check if two conditions are opposite"""
        # Simple check for boolean opposites
        if 'true' in cond1 and 'false' in cond2:
            # Check if they refer to the same variable
            var1 = re.search(r'(\w+)\s*==\s*true', cond1)
            var2 = re.search(r'(\w+)\s*==\s*false', cond2)
            if var1 and var2 and var1.group(1) == var2.group(1):
                return True
                
        return False
    
    def generate_combination_scenarios(self) -> List[CombinationScenario]:
        """Generate important combination scenarios to test"""
        scenarios = []
        
        # Ensure relationships are analyzed
        if not self.rule_relations:
            self.analyze_rule_relationships()
        
        # 1. Conflicting rules (highest priority)
        for relation in self.rule_relations.values():
            if relation.relation_type == 'conflicting':
                scenarios.append(CombinationScenario(
                    name=f"Conflict_{relation.rule1.name}_{relation.rule2.name}",
                    rules=[relation.rule1, relation.rule2],
                    description=f"Test conflict: {relation.conflict_reason}",
                    priority=10
                ))
        
        # 2. Rules affecting same attributes
        attr_rules = self._group_rules_by_attribute()
        for attr, rules in attr_rules.items():
            if len(rules) > 2:
                scenarios.append(CombinationScenario(
                    name=f"Multiple_rules_for_{attr}",
                    rules=rules[:3],  # Limit to 3 rules
                    description=f"Multiple rules affecting {attr}",
                    priority=7
                ))
        
        # 3. High priority rule combinations
        high_priority_rules = [r for r in self.model.rules.values() 
                              if r.priority >= 7]
        if len(high_priority_rules) >= 2:
            scenarios.append(CombinationScenario(
                name="High_priority_combination",
                rules=high_priority_rules[:2],
                description="Combination of high priority rules",
                priority=8
            ))
        
        return sorted(scenarios, key=lambda s: s.priority, reverse=True)
    
    def _group_rules_by_attribute(self) -> Dict[str, List[Rule]]:
        """Group rules by the attributes they affect"""
        attr_rules = {}
        
        for rule in self.model.rules.values():
            attrs = self._extract_attributes(rule)
            for attr in attrs:
                if attr not in attr_rules:
                    attr_rules[attr] = []
                attr_rules[attr].append(rule)
                
        return attr_rules
    
    def suggest_critical_combinations(self) -> List[Dict]:
        """Suggest critical rule combinations to test"""
        suggestions = []
        scenarios = self.generate_combination_scenarios()
        
        for scenario in scenarios[:5]:  # Top 5 scenarios
            suggestions.append({
                'rules': [r.name for r in scenario.rules],
                'description': scenario.description,
                'priority': scenario.priority,
                'type': 'conflict_resolution' if 'Conflict' in scenario.name 
                       else 'interaction_test'
            })
            
        return suggestions