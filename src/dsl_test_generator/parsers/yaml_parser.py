"""YAML-specific parser utilities."""

import yaml
from typing import Any, Dict


class YAMLParser:
    """YAML parsing utilities with custom tags support."""
    
    @staticmethod
    def load_with_tags(file_path: str) -> Dict[str, Any]:
        """Load YAML file with custom tag support."""
        
        def array_constructor(loader, node):
            """Handle !array tag."""
            return {"type": "array", "elements": loader.construct_sequence(node)}
        
        def set_constructor(loader, node):
            """Handle !set tag."""
            return {"type": "set", "elements": loader.construct_sequence(node)}
        
        yaml.SafeLoader.add_constructor('!array', array_constructor)
        yaml.SafeLoader.add_constructor('!set', set_constructor)
        
        with open(file_path, 'r', encoding='utf-8') as f:
            return yaml.safe_load(f)