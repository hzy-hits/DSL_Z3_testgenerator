"""
Value Generator Module
智能值生成器
"""

import random
import string
from typing import Any, Dict, List, Optional
from datetime import datetime, timedelta
from .models import Attribute


class ValueGenerator:
    """智能值生成器"""
    
    def __init__(self):
        self.id_counters = {}
        self.generation_count = {}  # 跟踪生成次数以增加多样性
    
    def generate(self, entity_name: str, attr: Attribute, context: Dict[str, Any] = None) -> Any:
        """生成属性值"""
        # 处理枚举
        if attr.enum:
            return random.choice(attr.enum)
        
        # 处理ID
        if 'id' in attr.name.lower():
            return self._generate_id(entity_name, attr.name)
        
        # 先检查是否是集合类型
        if attr.is_collection:
            return self._generate_collection(entity_name, attr)
        
        # 根据类型生成
        if attr.type == 'int' or attr.type == 'integer':
            return self._generate_int(attr.name, context)
        elif attr.type == 'float' or attr.type == 'double':
            return self._generate_float(attr.name, context)
        elif attr.type == 'string':
            return self._generate_string(attr.name, context)
        elif attr.type == 'boolean' or attr.type == 'bool':
            return random.choice([True, False])
        elif attr.is_temporal:
            return self._generate_date(attr.name)
        else:
            return f"{attr.name}_value"
    
    def _generate_id(self, entity_name: str, attr_name: str) -> int:
        """生成ID"""
        key = f"{entity_name}_{attr_name}"
        if key not in self.id_counters:
            # 设置起始值
            if 'product' in entity_name.lower():
                self.id_counters[key] = 1001
            elif 'order' in entity_name.lower():
                self.id_counters[key] = 10001
            elif 'student' in entity_name.lower():
                self.id_counters[key] = 2024001
            elif 'user' in entity_name.lower() or 'customer' in entity_name.lower():
                self.id_counters[key] = 1
            else:
                self.id_counters[key] = 1
        
        current = self.id_counters[key]
        self.id_counters[key] += 1
        return current
    
    def _generate_int(self, attr_name: str, context: Dict[str, Any] = None) -> int:
        """生成整数"""
        attr_lower = attr_name.lower()
        
        # 跟踪生成次数以增加多样性
        gen_key = f"int_{attr_name}"
        self.generation_count[gen_key] = self.generation_count.get(gen_key, 0) + 1
        count = self.generation_count[gen_key]
        
        # 基于属性名的智能生成
        if 'age' in attr_lower:
            # 不同年龄段
            age_ranges = [(18, 25), (26, 35), (36, 50), (51, 65), (66, 80)]
            age_range = age_ranges[(count - 1) % len(age_ranges)]
            return random.randint(age_range[0], age_range[1])
        elif 'score' in attr_lower:
            # 不同分数段
            score_ranges = [(0, 20), (21, 40), (41, 60), (61, 80), (81, 100)]
            score_range = score_ranges[(count - 1) % len(score_ranges)]
            return random.randint(score_range[0], score_range[1])
        elif 'grade' in attr_lower or 'level' in attr_lower:
            # 循环使用不同级别
            return ((count - 1) % 12) + 1
        elif 'quantity' in attr_lower or 'count' in attr_lower:
            # 不同数量级别
            quantities = [1, 5, 10, 20, 50]
            base = quantities[(count - 1) % len(quantities)]
            return base + random.randint(-2, 2)
        elif 'stock' in attr_lower:
            # 不同库存水平
            stock_levels = [0, 10, 50, 100, 500, 1000]
            return stock_levels[(count - 1) % len(stock_levels)] + random.randint(0, 10)
        elif 'price' in attr_lower or 'cost' in attr_lower or 'amount' in attr_lower:
            # 不同价格区间
            price_ranges = [(10, 50), (51, 100), (101, 500), (501, 1000)]
            price_range = price_ranges[(count - 1) % len(price_ranges)]
            return random.randint(price_range[0], price_range[1])
        elif 'year' in attr_lower:
            return 2020 + ((count - 1) % 6)
        elif 'month' in attr_lower:
            return ((count - 1) % 12) + 1
        elif 'day' in attr_lower:
            return ((count - 1) % 28) + 1
        
        # 默认范围 - 也要多样化
        ranges = [(1, 20), (21, 50), (51, 80), (81, 100)]
        range_idx = (count - 1) % len(ranges)
        return random.randint(ranges[range_idx][0], ranges[range_idx][1])
    
    def _generate_float(self, attr_name: str, context: Dict[str, Any] = None) -> float:
        """生成浮点数"""
        attr_lower = attr_name.lower()
        
        if 'price' in attr_lower or 'cost' in attr_lower:
            # 生成真实的价格
            prices = [9.99, 19.99, 29.99, 49.99, 99.99, 149.99, 199.99]
            base_price = random.choice(prices)
            # 可能的折扣
            if random.random() < 0.3:
                base_price *= random.choice([0.9, 0.8, 0.7])
            return round(base_price, 2)
        elif 'rate' in attr_lower or 'percentage' in attr_lower:
            return round(random.uniform(0, 1), 2)
        elif 'weight' in attr_lower:
            return round(random.uniform(0.1, 50), 2)
        elif 'amount' in attr_lower:
            return round(random.uniform(10, 500), 2)
        elif 'score' in attr_lower:
            return round(random.uniform(0, 100), 1)
        
        return round(random.uniform(0, 100), 2)
    
    def _generate_string(self, attr_name: str, context: Dict[str, Any] = None) -> str:
        """生成字符串"""
        attr_lower = attr_name.lower()
        
        # 跟踪生成次数
        gen_key = f"string_{attr_name}"
        self.generation_count[gen_key] = self.generation_count.get(gen_key, 0) + 1
        count = self.generation_count[gen_key]
        
        # 常见模式
        if 'name' in attr_lower:
            if 'first' in attr_lower:
                names = ['Alice', 'Bob', 'Charlie', 'David', 'Emma', 'Frank', 'Grace', 'Henry', 'Iris', 'Jack']
                return names[(count - 1) % len(names)]
            elif 'last' in attr_lower:
                names = ['Smith', 'Johnson', 'Brown', 'Davis', 'Wilson', 'Miller', 'Taylor', 'Anderson']
                return names[(count - 1) % len(names)]
            else:
                first_names = ['Alice', 'Bob', 'Charlie', 'David', 'Emma']
                last_names = ['Smith', 'Johnson', 'Brown', 'Davis', 'Wilson']
                return f"{first_names[(count - 1) % len(first_names)]} {last_names[(count - 1) % len(last_names)]}"
        elif 'email' in attr_lower:
            domains = ['example.com', 'test.com', 'demo.org', 'sample.net']
            return f"user{count}@{domains[(count - 1) % len(domains)]}"
        elif 'phone' in attr_lower:
            return f"{100 + count % 900}-{555}-{1000 + count % 9000}"
        elif 'address' in attr_lower:
            streets = ['Main St', 'Oak Ave', 'Elm Dr', 'Park Blvd', 'First St']
            return f"{count} {streets[(count - 1) % len(streets)]}, City, State {10000 + count}"
        elif 'status' in attr_lower:
            statuses = ['active', 'inactive', 'pending', 'completed', 'processing', 'cancelled']
            return statuses[(count - 1) % len(statuses)]
        elif 'code' in attr_lower:
            if 'discount' in attr_lower:
                codes = ['SAVE10', 'WELCOME20', 'VIP15', 'SUMMER25', 'WINTER30', 'SPRING15']
                return codes[(count - 1) % len(codes)]
            else:
                return f"CODE{1000 + count}"
        elif 'description' in attr_lower:
            variations = ['Basic', 'Standard', 'Premium', 'Special', 'Limited']
            return f"{variations[(count - 1) % len(variations)]} description for {attr_name}"
        elif 'category' in attr_lower:
            categories = ['electronics', 'clothing', 'books', 'home', 'sports', 'toys', 'food', 'beauty']
            return categories[(count - 1) % len(categories)]
        elif 'type' in attr_lower:
            types = ['standard', 'premium', 'basic', 'advanced', 'professional']
            return types[(count - 1) % len(types)]
        elif 'color' in attr_lower:
            colors = ['red', 'blue', 'green', 'black', 'white', 'yellow', 'purple', 'orange']
            return colors[(count - 1) % len(colors)]
        
        # 默认值
        return f"{attr_name}_value_{count}"
    
    def _generate_date(self, attr_name: str) -> str:
        """生成日期"""
        base = datetime.now()
        
        if 'birth' in attr_name.lower():
            # 生日：18-80年前
            days_ago = random.randint(18*365, 80*365)
            date = base - timedelta(days=days_ago)
        elif 'start' in attr_name.lower():
            # 开始日期：过去30天到未来30天
            offset = random.randint(-30, 30)
            date = base + timedelta(days=offset)
        elif 'end' in attr_name.lower():
            # 结束日期：未来1-90天
            offset = random.randint(1, 90)
            date = base + timedelta(days=offset)
        elif 'created' in attr_name.lower() or 'registration' in attr_name.lower():
            # 创建日期：过去365天内
            offset = random.randint(0, 365)
            date = base - timedelta(days=offset)
        else:
            # 默认：前后30天
            offset = random.randint(-30, 30)
            date = base + timedelta(days=offset)
        
        return date.strftime('%Y-%m-%d')
    
    def _generate_collection(self, entity_name: str, attr: Attribute) -> List[Any]:
        """生成集合"""
        attr_name = attr.name
        attr_lower = attr_name.lower()
        
        # 确定集合大小
        if attr.min_size is not None and attr.max_size is not None:
            size = random.randint(attr.min_size, attr.max_size)
        else:
            size = random.randint(1, 5)
        
        if 'permissions' in attr_lower or 'roles' in attr_lower:
            all_items = ['read', 'write', 'delete', 'admin', 'execute']
            size = min(size, len(all_items))
            return random.sample(all_items, size)
        elif 'tags' in attr_lower:
            all_tags = ['important', 'urgent', 'review', 'approved', 'pending', 'new']
            size = min(size, len(all_tags))
            return random.sample(all_tags, size)
        elif 'items' in attr_lower:
            # 购物车items - 产品ID数组
            return [random.randint(1001, 1020) for _ in range(size)]
        elif 'products' in attr_lower:
            return [f"product_{i+1}" for i in range(size)]
        elif 'discount_codes' in attr_lower:
            # 折扣码集合
            all_codes = ['SAVE10', 'WELCOME20', 'VIP15', 'SUMMER25', 'BULK15']
            size = min(size, len(all_codes))
            return random.sample(all_codes, size)
        elif 'categories' in attr_lower:
            all_cats = ['electronics', 'clothing', 'books', 'home', 'sports', 'toys']
            size = min(size, len(all_cats))
            return random.sample(all_cats, size)
        
        # 默认集合
        return [f"{attr_name}_{i+1}" for i in range(size)]