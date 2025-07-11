"""
Business Rules Engine Module - V8
可扩展的业务规则引擎，支持外部配置和插件系统
"""

import json
import yaml
import random
from typing import Any, Dict, List, Optional, Type, Callable
from pathlib import Path
from abc import ABC, abstractmethod
from datetime import datetime, timedelta
import logging

logger = logging.getLogger(__name__)


class BusinessRulePlugin(ABC):
    """业务规则插件基类"""
    
    @abstractmethod
    def domain(self) -> str:
        """返回插件支持的领域"""
        pass
    
    @abstractmethod
    def can_handle(self, entity: str, attribute: str) -> bool:
        """检查是否能处理特定的实体属性"""
        pass
    
    @abstractmethod
    def generate_value(self, entity: str, attribute: str, 
                      context: Dict[str, Any]) -> Any:
        """生成符合业务规则的值"""
        pass
    
    @abstractmethod
    def validate(self, entity: str, data: Dict[str, Any]) -> List[str]:
        """验证数据是否符合业务规则，返回错误列表"""
        pass


class BusinessRuleEngine:
    """
    业务规则引擎
    支持从外部配置加载规则，并提供插件扩展机制
    """
    
    def __init__(self, config_dir: Optional[Path] = None):
        self.config_dir = config_dir or Path("configs/business_rules")
        self.rules = {}
        self.plugins = {}
        self.patterns = {}
        self.id_counters = {}
        
        # 加载配置
        self._load_configurations()
        
        # 注册内置插件
        self._register_builtin_plugins()
    
    def register_plugin(self, plugin: BusinessRulePlugin):
        """注册业务规则插件"""
        domain = plugin.domain()
        if domain not in self.plugins:
            self.plugins[domain] = []
        self.plugins[domain].append(plugin)
        logger.info(f"Registered business rule plugin for domain: {domain}")
    
    def generate_value(self, domain: str, entity: str, attribute: str,
                      metadata: Dict[str, Any] = None, 
                      constraints: Dict[str, Any] = None) -> Any:
        """
        生成符合业务规则的值
        
        Args:
            domain: 业务领域
            entity: 实体名称
            attribute: 属性名称
            metadata: 属性元数据
            constraints: 约束条件
            
        Returns:
            生成的值
        """
        context = {
            'domain': domain,
            'entity': entity,
            'attribute': attribute,
            'metadata': metadata or {},
            'constraints': constraints or {}
        }
        
        # 尝试使用插件
        if domain in self.plugins:
            for plugin in self.plugins[domain]:
                if plugin.can_handle(entity, attribute):
                    try:
                        return plugin.generate_value(entity, attribute, context)
                    except Exception as e:
                        logger.warning(f"Plugin failed for {entity}.{attribute}: {e}")
        
        # 使用配置规则
        if domain in self.rules:
            return self._generate_from_rules(domain, entity, attribute, context)
        
        # 使用默认生成器
        return self._generate_default_value(entity, attribute, metadata)
    
    def validate_data(self, domain: str, entity: str, data: Dict[str, Any]) -> List[str]:
        """
        验证数据是否符合业务规则
        
        Args:
            domain: 业务领域
            entity: 实体名称
            data: 要验证的数据
            
        Returns:
            错误消息列表
        """
        errors = []
        
        # 使用插件验证
        if domain in self.plugins:
            for plugin in self.plugins[domain]:
                errors.extend(plugin.validate(entity, data))
        
        # 使用配置规则验证
        if domain in self.rules:
            errors.extend(self._validate_with_rules(domain, entity, data))
        
        return errors
    
    def get_domain_patterns(self, domain: str) -> Dict[str, Any]:
        """获取领域特定的模式和规则"""
        return self.patterns.get(domain, {})
    
    def learn_patterns(self, domain: str, examples: List[Dict[str, Any]]):
        """从示例数据学习业务模式"""
        # 简单的模式学习实现
        learned_patterns = {
            'value_distributions': {},
            'correlations': {},
            'sequences': {}
        }
        
        # 分析值分布
        for example in examples:
            for key, value in example.items():
                if key not in learned_patterns['value_distributions']:
                    learned_patterns['value_distributions'][key] = []
                learned_patterns['value_distributions'][key].append(value)
        
        # 保存学习到的模式
        if domain not in self.patterns:
            self.patterns[domain] = {}
        self.patterns[domain].update(learned_patterns)
        
        logger.info(f"Learned patterns for domain {domain} from {len(examples)} examples")
    
    # Private methods
    def _load_configurations(self):
        """加载业务规则配置文件"""
        if not self.config_dir.exists():
            self._create_default_configs()
            return
        
        for config_file in self.config_dir.glob("*.yaml"):
            try:
                with open(config_file, 'r', encoding='utf-8') as f:
                    config = yaml.safe_load(f)
                    domain = config.get('domain')
                    if domain:
                        self.rules[domain] = config
                        logger.info(f"Loaded business rules for domain: {domain}")
            except Exception as e:
                logger.error(f"Failed to load config {config_file}: {e}")
    
    def _create_default_configs(self):
        """创建默认配置"""
        default_rules = {
            'E-commerce': {
                'domain': 'E-commerce',
                'patterns': {
                    'price': {
                        'ranges': [
                            {'name': 'budget', 'min': 0.99, 'max': 49.99, 'weight': 0.4},
                            {'name': 'standard', 'min': 50.00, 'max': 199.99, 'weight': 0.4},
                            {'name': 'premium', 'min': 200.00, 'max': 999.99, 'weight': 0.2}
                        ],
                        'common_values': [9.99, 19.99, 29.99, 49.99, 99.99]
                    },
                    'status': {
                        'values': ['pending', 'processing', 'shipped', 'delivered', 'cancelled'],
                        'transitions': {
                            'pending': ['processing', 'cancelled'],
                            'processing': ['shipped', 'cancelled'],
                            'shipped': ['delivered'],
                            'delivered': [],
                            'cancelled': []
                        }
                    }
                },
                'rules': [
                    {'type': 'correlation', 'rule': 'Product.price > Product.cost * 1.2'},
                    {'type': 'business', 'rule': 'Order.status == "cancelled" => Order.refund_amount == Order.total'}
                ],
                'id_sequences': {
                    'product': {'start': 1001, 'increment': 1},
                    'order': {'start': 10001, 'increment': 1},
                    'customer': {'start': 1, 'increment': 1}
                }
            },
            'Education': {
                'domain': 'Education',
                'patterns': {
                    'score': {
                        'range': [0, 100],
                        'distribution': 'normal',
                        'mean': 75,
                        'std': 15
                    },
                    'grade': {
                        'mapping': {
                            'A': [90, 100],
                            'B': [80, 89],
                            'C': [70, 79],
                            'D': [60, 69],
                            'F': [0, 59]
                        }
                    }
                }
            }
        }
        
        # 内存中保存默认规则
        self.rules = default_rules
    
    def _register_builtin_plugins(self):
        """注册内置插件"""
        # 注册电商插件
        self.register_plugin(EcommercePlugin())
        # 注册教育插件
        self.register_plugin(EducationPlugin())
    
    def _generate_from_rules(self, domain: str, entity: str, attribute: str,
                            context: Dict[str, Any]) -> Any:
        """基于配置规则生成值"""
        domain_rules = self.rules.get(domain, {})
        patterns = domain_rules.get('patterns', {})
        
        # 处理ID生成
        if 'id' in attribute.lower():
            return self._generate_id(domain, entity, domain_rules.get('id_sequences', {}))
        
        # 查找属性特定的模式
        attr_pattern = patterns.get(attribute)
        if attr_pattern:
            return self._apply_pattern(attr_pattern, context)
        
        # 查找实体特定的模式
        entity_patterns = patterns.get(entity.lower(), {})
        if attribute in entity_patterns:
            return self._apply_pattern(entity_patterns[attribute], context)
        
        # 使用默认生成器
        return self._generate_default_value(entity, attribute, context.get('metadata'))
    
    def _apply_pattern(self, pattern: Dict[str, Any], context: Dict[str, Any]) -> Any:
        """应用模式生成值"""
        # 范围模式
        if 'ranges' in pattern:
            # 根据权重选择范围
            ranges = pattern['ranges']
            weights = [r.get('weight', 1.0) for r in ranges]
            selected_range = random.choices(ranges, weights=weights)[0]
            return round(random.uniform(selected_range['min'], selected_range['max']), 2)
        
        # 固定值模式
        if 'values' in pattern:
            return random.choice(pattern['values'])
        
        # 常见值模式
        if 'common_values' in pattern:
            if random.random() < 0.7:  # 70%概率使用常见值
                return random.choice(pattern['common_values'])
            elif 'range' in pattern:
                return round(random.uniform(pattern['range'][0], pattern['range'][1]), 2)
        
        # 分布模式
        if 'distribution' in pattern:
            if pattern['distribution'] == 'normal':
                mean = pattern.get('mean', 50)
                std = pattern.get('std', 10)
                value = random.normalvariate(mean, std)
                if 'range' in pattern:
                    value = max(pattern['range'][0], min(pattern['range'][1], value))
                return round(value, 2)
        
        # 映射模式
        if 'mapping' in pattern:
            # 反向映射：从范围生成值
            mapping = pattern['mapping']
            key = random.choice(list(mapping.keys()))
            range_val = mapping[key]
            if isinstance(range_val, list) and len(range_val) == 2:
                return random.randint(range_val[0], range_val[1])
        
        return None
    
    def _generate_id(self, domain: str, entity: str, id_sequences: Dict[str, Any]) -> int:
        """生成ID"""
        key = f"{domain}_{entity}"
        
        if entity.lower() in id_sequences:
            seq_config = id_sequences[entity.lower()]
            if key not in self.id_counters:
                self.id_counters[key] = seq_config.get('start', 1)
            
            current = self.id_counters[key]
            self.id_counters[key] += seq_config.get('increment', 1)
            return current
        
        # 默认ID生成
        if key not in self.id_counters:
            self.id_counters[key] = 1
        
        current = self.id_counters[key]
        self.id_counters[key] += 1
        return current
    
    def _generate_default_value(self, entity: str, attribute: str, 
                               metadata: Optional[Dict[str, Any]]) -> Any:
        """生成默认值"""
        if not metadata:
            return f"{entity}_{attribute}_value"
        
        attr_type = metadata.get('type', 'string')
        
        if attr_type == 'int':
            return random.randint(1, 100)
        elif attr_type == 'float':
            return round(random.uniform(0, 100), 2)
        elif attr_type == 'bool':
            return random.choice([True, False])
        elif attr_type == 'date':
            base = datetime.now()
            offset = timedelta(days=random.randint(-365, 365))
            return (base + offset).strftime('%Y-%m-%d')
        elif attr_type == 'array':
            return [f"item_{i}" for i in range(random.randint(1, 3))]
        else:
            return f"{entity}_{attribute}_value"
    
    def _validate_with_rules(self, domain: str, entity: str, 
                            data: Dict[str, Any]) -> List[str]:
        """使用规则验证数据"""
        errors = []
        domain_rules = self.rules.get(domain, {})
        
        # 验证业务规则
        for rule in domain_rules.get('rules', []):
            if rule.get('type') == 'business':
                # 简化的规则验证
                rule_text = rule.get('rule', '')
                # 这里应该使用表达式解析器验证规则
                # 暂时跳过复杂实现
        
        return errors


class EcommercePlugin(BusinessRulePlugin):
    """电商领域业务规则插件"""
    
    def domain(self) -> str:
        return "E-commerce"
    
    def can_handle(self, entity: str, attribute: str) -> bool:
        handled_patterns = {
            'Product': ['price', 'cost', 'discount', 'stock'],
            'Order': ['total', 'tax', 'shipping_fee', 'status'],
            'Customer': ['loyalty_points', 'tier', 'credit_limit']
        }
        return entity in handled_patterns and attribute in handled_patterns[entity]
    
    def generate_value(self, entity: str, attribute: str, context: Dict[str, Any]) -> Any:
        if entity == 'Product':
            if attribute == 'price':
                # 智能定价
                base_prices = [9.99, 19.99, 29.99, 49.99, 99.99, 199.99]
                price = random.choice(base_prices)
                # 可能的折扣
                if random.random() < 0.3:
                    price *= random.choice([0.9, 0.8, 0.7])
                return round(price, 2)
            elif attribute == 'cost':
                # 成本通常是价格的60-80%
                price = context.get('price', 50)
                return round(price * random.uniform(0.6, 0.8), 2)
            elif attribute == 'stock':
                # 库存遵循长尾分布
                if random.random() < 0.7:
                    return random.randint(10, 100)
                else:
                    return random.randint(0, 10)
        
        elif entity == 'Order':
            if attribute == 'total':
                # 订单总额
                return round(random.uniform(10, 500), 2)
            elif attribute == 'tax':
                total = context.get('total', 100)
                tax_rate = random.choice([0.05, 0.08, 0.1])  # 5%, 8%, 10%
                return round(total * tax_rate, 2)
            elif attribute == 'status':
                # 状态分布
                statuses = ['pending', 'processing', 'shipped', 'delivered', 'cancelled']
                weights = [0.1, 0.15, 0.2, 0.45, 0.1]
                return random.choices(statuses, weights=weights)[0]
        
        return f"{entity}_{attribute}_value"
    
    def validate(self, entity: str, data: Dict[str, Any]) -> List[str]:
        errors = []
        
        if entity == 'Product':
            price = data.get('price', 0)
            cost = data.get('cost', 0)
            if price <= cost:
                errors.append("Product price must be greater than cost")
            if price <= 0:
                errors.append("Product price must be positive")
        
        elif entity == 'Order':
            total = data.get('total', 0)
            if total < 0:
                errors.append("Order total cannot be negative")
            
            status = data.get('status')
            valid_statuses = ['pending', 'processing', 'shipped', 'delivered', 'cancelled']
            if status and status not in valid_statuses:
                errors.append(f"Invalid order status: {status}")
        
        return errors


class EducationPlugin(BusinessRulePlugin):
    """教育领域业务规则插件"""
    
    def domain(self) -> str:
        return "Education"
    
    def can_handle(self, entity: str, attribute: str) -> bool:
        handled_patterns = {
            'Student': ['score', 'grade', 'gpa', 'attendance'],
            'Course': ['credits', 'difficulty', 'capacity'],
            'Exam': ['passing_score', 'max_score', 'duration']
        }
        return entity in handled_patterns and attribute in handled_patterns[entity]
    
    def generate_value(self, entity: str, attribute: str, context: Dict[str, Any]) -> Any:
        if entity == 'Student':
            if attribute == 'score':
                # 正态分布的分数
                score = random.normalvariate(75, 15)
                return max(0, min(100, round(score)))
            elif attribute == 'grade':
                score = context.get('score', 75)
                if score >= 90:
                    return 'A'
                elif score >= 80:
                    return 'B'
                elif score >= 70:
                    return 'C'
                elif score >= 60:
                    return 'D'
                else:
                    return 'F'
            elif attribute == 'gpa':
                return round(random.uniform(2.0, 4.0), 2)
            elif attribute == 'attendance':
                # 出勤率通常较高
                return round(random.betavariate(8, 2) * 100)
        
        return f"{entity}_{attribute}_value"
    
    def validate(self, entity: str, data: Dict[str, Any]) -> List[str]:
        errors = []
        
        if entity == 'Student':
            score = data.get('score')
            if score is not None and (score < 0 or score > 100):
                errors.append("Student score must be between 0 and 100")
            
            gpa = data.get('gpa')
            if gpa is not None and (gpa < 0 or gpa > 4.0):
                errors.append("GPA must be between 0.0 and 4.0")
        
        return errors