"""
Value Generator Module - V8
智能值生成器，支持多种生成策略和领域感知
"""

from abc import ABC, abstractmethod
from typing import Any, Dict, List, Optional, Set, Type, Union
import random
import string
from datetime import datetime, timedelta
from faker import Faker
import logging

logger = logging.getLogger(__name__)


class ValueGenerator(ABC):
    """值生成器基类"""
    
    @abstractmethod
    def generate(self, metadata: Dict[str, Any], constraints: List[str] = None) -> Any:
        """生成值"""
        pass
    
    @abstractmethod
    def can_handle(self, metadata: Dict[str, Any]) -> bool:
        """检查是否能处理给定的元数据"""
        pass


class IntegerGenerator(ValueGenerator):
    """整数生成器"""
    
    def generate(self, metadata: Dict[str, Any], constraints: List[str] = None) -> int:
        min_val = metadata.get('min', 0)
        max_val = metadata.get('max', 100)
        
        # 处理特殊模式
        if metadata.get('pattern') == 'id':
            return self._generate_id(metadata)
        elif metadata.get('pattern') == 'age':
            return random.randint(18, 80)
        elif metadata.get('pattern') == 'year':
            current_year = datetime.now().year
            return random.randint(current_year - 10, current_year + 2)
        
        # 处理分布
        distribution = metadata.get('distribution', 'uniform')
        if distribution == 'normal':
            mean = metadata.get('mean', (min_val + max_val) / 2)
            std = metadata.get('std', (max_val - min_val) / 6)
            value = int(random.normalvariate(mean, std))
            return max(min_val, min(max_val, value))
        elif distribution == 'exponential':
            rate = metadata.get('rate', 1.0)
            value = int(random.expovariate(rate))
            return max(min_val, min(max_val, value))
        
        # 默认均匀分布
        return random.randint(min_val, max_val)
    
    def can_handle(self, metadata: Dict[str, Any]) -> bool:
        return metadata.get('type') in ['int', 'integer', 'number'] and not metadata.get('is_float')
    
    def _generate_id(self, metadata: Dict[str, Any]) -> int:
        """生成ID"""
        start = metadata.get('id_start', 1)
        increment = metadata.get('id_increment', 1)
        # 使用简单的递增逻辑
        return start + random.randint(0, 1000) * increment


class FloatGenerator(ValueGenerator):
    """浮点数生成器"""
    
    def generate(self, metadata: Dict[str, Any], constraints: List[str] = None) -> float:
        min_val = metadata.get('min', 0.0)
        max_val = metadata.get('max', 100.0)
        precision = metadata.get('precision', 2)
        
        # 处理特殊模式
        if metadata.get('pattern') == 'price':
            return self._generate_price(min_val, max_val)
        elif metadata.get('pattern') == 'percentage':
            return round(random.uniform(0, 100), precision)
        elif metadata.get('pattern') == 'ratio':
            return round(random.uniform(0, 1), precision)
        
        # 生成值
        value = random.uniform(min_val, max_val)
        return round(value, precision)
    
    def can_handle(self, metadata: Dict[str, Any]) -> bool:
        return metadata.get('type') in ['float', 'double', 'decimal'] or metadata.get('is_float')
    
    def _generate_price(self, min_val: float, max_val: float) -> float:
        """生成价格"""
        common_endings = [0.00, 0.49, 0.50, 0.95, 0.99]
        base = random.randint(int(min_val), int(max_val) - 1)
        ending = random.choice(common_endings)
        return base + ending


class StringGenerator(ValueGenerator):
    """字符串生成器"""
    
    def __init__(self):
        self.faker = Faker()
    
    def generate(self, metadata: Dict[str, Any], constraints: List[str] = None) -> str:
        # 处理枚举
        if metadata.get('enum'):
            return random.choice(metadata['enum'])
        
        # 处理模式
        pattern = metadata.get('pattern', '').lower()
        
        if pattern == 'email':
            return self.faker.email()
        elif pattern == 'name':
            return self.faker.name()
        elif pattern == 'first_name':
            return self.faker.first_name()
        elif pattern == 'last_name':
            return self.faker.last_name()
        elif pattern == 'phone':
            return self.faker.phone_number()
        elif pattern == 'address':
            return self.faker.address()
        elif pattern == 'url':
            return self.faker.url()
        elif pattern == 'uuid':
            return self.faker.uuid4()
        elif pattern == 'company':
            return self.faker.company()
        elif pattern == 'job':
            return self.faker.job()
        elif pattern == 'text':
            max_length = metadata.get('max_length', 100)
            return self.faker.text(max_nb_chars=max_length)
        elif pattern == 'word':
            return self.faker.word()
        elif pattern == 'sentence':
            return self.faker.sentence()
        elif pattern == 'paragraph':
            return self.faker.paragraph()
        elif pattern == 'color':
            return self.faker.color_name()
        elif pattern == 'country':
            return self.faker.country()
        elif pattern == 'city':
            return self.faker.city()
        elif pattern == 'state':
            return self.faker.state()
        elif pattern == 'zipcode':
            return self.faker.zipcode()
        
        # 处理正则表达式
        if metadata.get('regex'):
            return self._generate_from_regex(metadata['regex'])
        
        # 处理长度约束
        min_length = metadata.get('min_length', 1)
        max_length = metadata.get('max_length', 50)
        length = random.randint(min_length, max_length)
        
        # 处理字符集
        charset = metadata.get('charset', 'alphanumeric')
        if charset == 'alpha':
            chars = string.ascii_letters
        elif charset == 'numeric':
            chars = string.digits
        elif charset == 'alphanumeric':
            chars = string.ascii_letters + string.digits
        elif charset == 'ascii':
            chars = string.printable.strip()
        else:
            chars = string.ascii_letters + string.digits
        
        # 生成随机字符串
        prefix = metadata.get('prefix', '')
        suffix = metadata.get('suffix', '')
        
        random_part_length = max(0, length - len(prefix) - len(suffix))
        random_part = ''.join(random.choice(chars) for _ in range(random_part_length))
        
        return prefix + random_part + suffix
    
    def can_handle(self, metadata: Dict[str, Any]) -> bool:
        return metadata.get('type') in ['string', 'text', 'varchar', 'char']
    
    def _generate_from_regex(self, regex: str) -> str:
        """从正则表达式生成字符串（简化实现）"""
        # 这里应该使用更复杂的正则表达式反向生成器
        # 暂时返回符合简单模式的字符串
        if regex == r'\d{3}-\d{3}-\d{4}':  # 电话号码
            return f"{random.randint(100, 999)}-{random.randint(100, 999)}-{random.randint(1000, 9999)}"
        elif regex == r'[A-Z]{2}\d{4}':  # 车牌号
            letters = ''.join(random.choices(string.ascii_uppercase, k=2))
            numbers = ''.join(random.choices(string.digits, k=4))
            return letters + numbers
        else:
            return "generated_string"


class BooleanGenerator(ValueGenerator):
    """布尔值生成器"""
    
    def generate(self, metadata: Dict[str, Any], constraints: List[str] = None) -> bool:
        # 处理概率
        true_probability = metadata.get('true_probability', 0.5)
        return random.random() < true_probability
    
    def can_handle(self, metadata: Dict[str, Any]) -> bool:
        return metadata.get('type') in ['bool', 'boolean']


class DateTimeGenerator(ValueGenerator):
    """日期时间生成器"""
    
    def generate(self, metadata: Dict[str, Any], constraints: List[str] = None) -> Union[str, datetime]:
        # 获取范围
        now = datetime.now()
        
        if metadata.get('min'):
            min_date = self._parse_date(metadata['min'])
        else:
            min_date = now - timedelta(days=365)
        
        if metadata.get('max'):
            max_date = self._parse_date(metadata['max'])
        else:
            max_date = now + timedelta(days=365)
        
        # 处理特殊模式
        pattern = metadata.get('pattern', '').lower()
        
        if pattern == 'past':
            max_date = min(max_date, now)
        elif pattern == 'future':
            min_date = max(min_date, now)
        elif pattern == 'recent':
            min_date = now - timedelta(days=30)
            max_date = now
        elif pattern == 'today':
            return now.strftime(self._get_format(metadata))
        elif pattern == 'yesterday':
            return (now - timedelta(days=1)).strftime(self._get_format(metadata))
        elif pattern == 'tomorrow':
            return (now + timedelta(days=1)).strftime(self._get_format(metadata))
        
        # 生成随机日期
        time_between = max_date - min_date
        days_between = time_between.days
        random_days = random.randrange(days_between + 1)
        random_date = min_date + timedelta(days=random_days)
        
        # 处理时间部分
        if metadata.get('include_time', False):
            random_date = random_date.replace(
                hour=random.randint(0, 23),
                minute=random.randint(0, 59),
                second=random.randint(0, 59)
            )
        
        # 返回格式化的字符串
        return random_date.strftime(self._get_format(metadata))
    
    def can_handle(self, metadata: Dict[str, Any]) -> bool:
        return metadata.get('type') in ['date', 'datetime', 'timestamp'] or metadata.get('is_temporal')
    
    def _parse_date(self, date_str: str) -> datetime:
        """解析日期字符串"""
        formats = [
            '%Y-%m-%d',
            '%Y-%m-%d %H:%M:%S',
            '%Y/%m/%d',
            '%d/%m/%Y',
            '%m/%d/%Y'
        ]
        
        for fmt in formats:
            try:
                return datetime.strptime(date_str, fmt)
            except ValueError:
                continue
        
        # 如果都失败，返回当前时间
        return datetime.now()
    
    def _get_format(self, metadata: Dict[str, Any]) -> str:
        """获取日期格式"""
        format_str = metadata.get('format')
        if format_str:
            return format_str
        
        if metadata.get('include_time'):
            return '%Y-%m-%d %H:%M:%S'
        else:
            return '%Y-%m-%d'


class ArrayGenerator(ValueGenerator):
    """数组生成器"""
    
    def __init__(self, element_generator_factory):
        self.element_generator_factory = element_generator_factory
    
    def generate(self, metadata: Dict[str, Any], constraints: List[str] = None) -> List[Any]:
        # 获取数组大小
        min_size = metadata.get('min_size', 0)
        max_size = metadata.get('max_size', 10)
        size = random.randint(min_size, max_size)
        
        # 获取元素类型
        element_type = metadata.get('element_type', 'string')
        element_metadata = {
            'type': element_type,
            **metadata.get('element_metadata', {})
        }
        
        # 生成元素
        element_generator = self.element_generator_factory.get_generator(element_metadata)
        
        # 处理唯一性约束
        if metadata.get('unique_elements', False):
            elements = set()
            attempts = 0
            while len(elements) < size and attempts < size * 10:
                element = element_generator.generate(element_metadata, constraints)
                if hasattr(element, '__hash__'):
                    elements.add(element)
                attempts += 1
            return list(elements)
        else:
            return [element_generator.generate(element_metadata, constraints) 
                   for _ in range(size)]
    
    def can_handle(self, metadata: Dict[str, Any]) -> bool:
        return metadata.get('type') in ['array', 'list'] or metadata.get('is_collection')


class ObjectGenerator(ValueGenerator):
    """对象生成器"""
    
    def __init__(self, generator_factory):
        self.generator_factory = generator_factory
    
    def generate(self, metadata: Dict[str, Any], constraints: List[str] = None) -> Dict[str, Any]:
        obj = {}
        
        # 获取属性定义
        properties = metadata.get('properties', {})
        
        for prop_name, prop_metadata in properties.items():
            # 检查是否必需
            if prop_metadata.get('required', True) or random.random() < 0.8:
                generator = self.generator_factory.get_generator(prop_metadata)
                obj[prop_name] = generator.generate(prop_metadata, constraints)
        
        return obj
    
    def can_handle(self, metadata: Dict[str, Any]) -> bool:
        return metadata.get('type') in ['object', 'dict', 'map']


class ValueGeneratorFactory:
    """
    值生成器工厂
    管理和创建各种类型的值生成器
    """
    
    def __init__(self):
        self.generators = []
        self._register_default_generators()
    
    def register_generator(self, generator: ValueGenerator):
        """注册值生成器"""
        self.generators.append(generator)
    
    def get_generator(self, metadata: Dict[str, Any]) -> ValueGenerator:
        """获取适合的生成器"""
        for generator in self.generators:
            if generator.can_handle(metadata):
                return generator
        
        # 返回默认字符串生成器
        return StringGenerator()
    
    def generate_value(self, metadata: Dict[str, Any], 
                      constraints: List[str] = None) -> Any:
        """生成值的便捷方法"""
        generator = self.get_generator(metadata)
        return generator.generate(metadata, constraints)
    
    def _register_default_generators(self):
        """注册默认生成器"""
        self.register_generator(IntegerGenerator())
        self.register_generator(FloatGenerator())
        self.register_generator(StringGenerator())
        self.register_generator(BooleanGenerator())
        self.register_generator(DateTimeGenerator())
        self.register_generator(ArrayGenerator(self))
        self.register_generator(ObjectGenerator(self))


class SmartValueGenerator:
    """
    智能值生成器
    结合约束求解和业务规则生成高质量测试数据
    """
    
    def __init__(self, constraint_solver, business_engine, value_factory):
        self.constraint_solver = constraint_solver
        self.business_engine = business_engine
        self.value_factory = value_factory
    
    def generate(self, entity: str, attribute: str, 
                metadata: Dict[str, Any],
                constraints: List[str] = None,
                context: Dict[str, Any] = None) -> Any:
        """
        智能生成值
        
        优先级：
        1. 约束求解器生成的值
        2. 业务规则生成的值
        3. 基础生成器生成的值
        """
        domain = context.get('domain', 'default') if context else 'default'
        
        # 尝试使用约束求解器
        if constraints:
            try:
                variables = {attribute: metadata}
                solutions = self.constraint_solver.solve(constraints, variables, num_solutions=1)
                if solutions and attribute in solutions[0]:
                    return solutions[0][attribute]
            except Exception as e:
                logger.debug(f"Constraint solver failed for {attribute}: {e}")
        
        # 尝试使用业务规则
        try:
            value = self.business_engine.generate_value(
                domain, entity, attribute, metadata, constraints
            )
            if value is not None:
                return value
        except Exception as e:
            logger.debug(f"Business engine failed for {attribute}: {e}")
        
        # 使用基础生成器
        return self.value_factory.generate_value(metadata, constraints)