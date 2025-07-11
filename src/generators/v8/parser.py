"""
YAML Parser Module
解析DSL YAML文件
"""

import yaml
from typing import List, Dict, Any
from .models import Entity, Attribute


class YAMLParser:
    """YAML解析器"""
    
    def parse_file(self, file_path: str) -> List[Entity]:
        """解析YAML文件"""
        with open(file_path, 'r', encoding='utf-8') as f:
            data = yaml.safe_load(f)
        
        entities = []
        
        # 解析entities部分
        entities_data = data.get('entities', [])
        if isinstance(entities_data, list):
            # 处理列表格式
            for entity_data in entities_data:
                if isinstance(entity_data, dict) and 'name' in entity_data:
                    entity_name = entity_data['name']
                    entity = self._parse_entity(entity_name, entity_data)
                    entities.append(entity)
        elif isinstance(entities_data, dict):
            # 处理字典格式
            for entity_name, entity_data in entities_data.items():
                entity = self._parse_entity(entity_name, entity_data)
                entities.append(entity)
        
        return entities
    
    def _parse_entity(self, entity_name: str, entity_data: Dict[str, Any]) -> Entity:
        """解析单个实体"""
        entity = Entity(name=entity_name)
        
        # 解析属性
        attributes_data = entity_data.get('attributes', [])
        if isinstance(attributes_data, list):
            # 处理列表格式的属性
            for attr_data in attributes_data:
                if isinstance(attr_data, dict) and 'name' in attr_data:
                    attr = self._parse_attribute(attr_data)
                    entity.attributes.append(attr)
        elif isinstance(attributes_data, dict):
            # 处理字典格式的属性
            for attr_name, attr_data in attributes_data.items():
                if isinstance(attr_data, dict):
                    attr_data['name'] = attr_name
                    attr = self._parse_attribute(attr_data)
                else:
                    # 简单类型定义
                    attr = Attribute(name=attr_name, type=attr_data)
                entity.attributes.append(attr)
        
        # 解析约束
        for constraint in entity_data.get('constraints', []):
            if isinstance(constraint, dict):
                entity.constraints.append(constraint.get('expression', ''))
            else:
                entity.constraints.append(str(constraint))
        
        # 解析规则
        entity.rules = entity_data.get('rules', [])
        
        return entity
    
    def _parse_attribute(self, attr_data: Dict[str, Any]) -> Attribute:
        """解析单个属性"""
        attr_type = attr_data.get('type', 'string')
        
        # 处理集合类型
        is_collection = False
        if attr_type.startswith('array[') or attr_type.startswith('set['):
            is_collection = True
            # 提取基本类型
            base_type = attr_type[attr_type.index('[')+1:attr_type.index(']')]
            attr_type = base_type
        elif attr_type in ['array', 'list', 'set']:
            is_collection = True
        
        # 处理real类型
        if attr_type == 'real':
            attr_type = 'float'
        
        return Attribute(
            name=attr_data.get('name', 'unnamed'),
            type=attr_type,
            required=attr_data.get('required', True),
            enum=attr_data.get('enum'),
            is_collection=is_collection,
            is_temporal=attr_type in ['date', 'datetime', 'timestamp'],
            min_size=attr_data.get('min_size'),
            max_size=attr_data.get('max_size')
        )