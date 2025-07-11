"""
Expression Parser Module - V8
完整的表达式解析器，支持所有DSL约束类型
"""

import re
from typing import Any, Dict, List, Optional, Union, Tuple
from enum import Enum
import logging

logger = logging.getLogger(__name__)


class TokenType(Enum):
    """Token类型枚举"""
    NUMBER = "NUMBER"
    STRING = "STRING"
    BOOLEAN = "BOOLEAN"
    IDENTIFIER = "IDENTIFIER"
    OPERATOR = "OPERATOR"
    COMPARISON = "COMPARISON"
    LOGICAL = "LOGICAL"
    IMPLICATION = "IMPLICATION"
    FUNCTION = "FUNCTION"
    LPAREN = "LPAREN"
    RPAREN = "RPAREN"
    COMMA = "COMMA"
    DOT = "DOT"
    NULL = "NULL"
    EOF = "EOF"


class Token:
    """词法单元"""
    def __init__(self, type_: TokenType, value: Any, position: int = 0):
        self.type = type_
        self.value = value
        self.position = position
    
    def __repr__(self):
        return f"Token({self.type}, {self.value})"


class Lexer:
    """词法分析器"""
    
    # Token模式定义
    TOKEN_PATTERNS = [
        (r'\s+', None),  # 空白字符
        (r'#.*', None),  # 注释
        (r'\d+\.\d+', TokenType.NUMBER),  # 浮点数
        (r'\d+', TokenType.NUMBER),  # 整数
        (r'"[^"]*"', TokenType.STRING),  # 双引号字符串
        (r"'[^']*'", TokenType.STRING),  # 单引号字符串
        (r'true|false|True|False', TokenType.BOOLEAN),
        (r'null|NULL|None', TokenType.NULL),
        (r'=>', TokenType.IMPLICATION),
        (r'>=|<=|!=|==|>|<', TokenType.COMPARISON),
        (r'and|AND|&&', TokenType.LOGICAL),
        (r'or|OR|\|\|', TokenType.LOGICAL),
        (r'not|NOT|!', TokenType.LOGICAL),
        (r'[a-zA-Z_][\w_]*(?=\s*\()', TokenType.FUNCTION),  # 函数名
        (r'[a-zA-Z_][\w_]*', TokenType.IDENTIFIER),
        (r'\+|-|\*|/', TokenType.OPERATOR),
        (r'\(', TokenType.LPAREN),
        (r'\)', TokenType.RPAREN),
        (r',', TokenType.COMMA),
        (r'\.', TokenType.DOT),
    ]
    
    def __init__(self, text: str):
        self.text = text
        self.position = 0
        self.tokens = []
        self._tokenize()
    
    def _tokenize(self):
        """执行词法分析"""
        patterns = [(re.compile(p), t) for p, t in self.TOKEN_PATTERNS]
        
        while self.position < len(self.text):
            matched = False
            
            for pattern, token_type in patterns:
                match = pattern.match(self.text, self.position)
                if match:
                    value = match.group(0)
                    if token_type:  # 非空白和注释
                        token = self._create_token(token_type, value, self.position)
                        self.tokens.append(token)
                    self.position = match.end()
                    matched = True
                    break
            
            if not matched:
                raise ValueError(f"Unexpected character at position {self.position}: {self.text[self.position]}")
        
        self.tokens.append(Token(TokenType.EOF, None, self.position))
    
    def _create_token(self, token_type: TokenType, value: str, position: int) -> Token:
        """创建Token"""
        if token_type == TokenType.NUMBER:
            return Token(token_type, float(value) if '.' in value else int(value), position)
        elif token_type == TokenType.STRING:
            return Token(token_type, value[1:-1], position)  # 去除引号
        elif token_type == TokenType.BOOLEAN:
            return Token(token_type, value.lower() == 'true', position)
        elif token_type == TokenType.LOGICAL:
            normalized = {'and': 'and', 'AND': 'and', '&&': 'and',
                         'or': 'or', 'OR': 'or', '||': 'or',
                         'not': 'not', 'NOT': 'not', '!': 'not'}
            return Token(token_type, normalized.get(value, value), position)
        else:
            return Token(token_type, value, position)


class ExpressionParser:
    """
    递归下降表达式解析器
    
    语法规则:
    expression := implication
    implication := logical_or ( '=>' logical_or )*
    logical_or := logical_and ( 'or' logical_and )*
    logical_and := comparison ( 'and' comparison )*
    comparison := additive ( comparison_op additive )?
    additive := multiplicative ( ('+' | '-') multiplicative )*
    multiplicative := unary ( ('*' | '/') unary )*
    unary := 'not'? primary
    primary := number | string | boolean | null | identifier | function_call | '(' expression ')'
    function_call := identifier '(' argument_list? ')'
    argument_list := expression ( ',' expression )*
    identifier := field_reference | simple_identifier
    field_reference := simple_identifier ( '.' simple_identifier )*
    """
    
    def __init__(self):
        self.tokens = []
        self.current = 0
        
    def parse(self, expression: str, context: Dict[str, Any] = None) -> Dict[str, Any]:
        """解析表达式并返回AST"""
        try:
            if not expression or not expression.strip():
                return {'type': 'empty', 'value': None}
            
            # 词法分析
            lexer = Lexer(expression)
            self.tokens = lexer.tokens
            self.current = 0
            self.context = context or {}
            
            # 语法分析
            ast = self._parse_expression()
            
            # 确保所有token都被消费
            if not self._is_at_end():
                raise ValueError(f"Unexpected tokens after expression: {self._peek()}")
            
            return ast
            
        except Exception as e:
            logger.warning(f"Failed to parse expression '{expression}': {e}")
            return {'type': 'error', 'value': str(e), 'expression': expression}
    
    def evaluate(self, ast: Dict[str, Any], context: Dict[str, Any] = None) -> Any:
        """求值AST"""
        if not ast:
            return None
            
        node_type = ast.get('type')
        ctx = {**(self.context or {}), **(context or {})}
        
        try:
            if node_type == 'number':
                return ast['value']
            elif node_type == 'string':
                return ast['value']
            elif node_type == 'boolean':
                return ast['value']
            elif node_type == 'null':
                return None
            elif node_type == 'identifier':
                return self._resolve_identifier(ast['value'], ctx)
            elif node_type == 'field_reference':
                return self._resolve_field_reference(ast['entity'], ast['field'], ctx)
            elif node_type == 'binary':
                return self._evaluate_binary(ast, ctx)
            elif node_type == 'unary':
                return self._evaluate_unary(ast, ctx)
            elif node_type == 'function_call':
                return self._evaluate_function(ast, ctx)
            elif node_type == 'empty':
                return True
            else:
                return None
                
        except Exception as e:
            logger.warning(f"Evaluation error for {ast}: {e}")
            return None
    
    # Parser methods
    def _parse_expression(self) -> Dict[str, Any]:
        """解析表达式"""
        return self._parse_implication()
    
    def _parse_implication(self) -> Dict[str, Any]:
        """解析蕴含表达式: A => B"""
        left = self._parse_logical_or()
        
        while self._match(TokenType.IMPLICATION):
            op = self._previous().value
            right = self._parse_logical_or()
            left = {
                'type': 'binary',
                'operator': op,
                'left': left,
                'right': right
            }
        
        return left
    
    def _parse_logical_or(self) -> Dict[str, Any]:
        """解析逻辑或表达式"""
        left = self._parse_logical_and()
        
        while self._check(TokenType.LOGICAL) and self._peek().value == 'or':
            self._advance()
            op = self._previous().value
            right = self._parse_logical_and()
            left = {
                'type': 'binary',
                'operator': op,
                'left': left,
                'right': right
            }
        
        return left
    
    def _parse_logical_and(self) -> Dict[str, Any]:
        """解析逻辑与表达式"""
        left = self._parse_comparison()
        
        while self._check(TokenType.LOGICAL) and self._peek().value == 'and':
            self._advance()
            op = self._previous().value
            right = self._parse_comparison()
            left = {
                'type': 'binary',
                'operator': op,
                'left': left,
                'right': right
            }
        
        return left
    
    def _parse_comparison(self) -> Dict[str, Any]:
        """解析比较表达式"""
        left = self._parse_additive()
        
        if self._match(TokenType.COMPARISON):
            op = self._previous().value
            right = self._parse_additive()
            return {
                'type': 'binary',
                'operator': op,
                'left': left,
                'right': right
            }
        
        return left
    
    def _parse_additive(self) -> Dict[str, Any]:
        """解析加减表达式"""
        left = self._parse_multiplicative()
        
        while self._check(TokenType.OPERATOR) and self._peek().value in ['+', '-']:
            self._advance()
            op = self._previous().value
            right = self._parse_multiplicative()
            left = {
                'type': 'binary',
                'operator': op,
                'left': left,
                'right': right
            }
        
        return left
    
    def _parse_multiplicative(self) -> Dict[str, Any]:
        """解析乘除表达式"""
        left = self._parse_unary()
        
        while self._check(TokenType.OPERATOR) and self._peek().value in ['*', '/']:
            self._advance()
            op = self._previous().value
            right = self._parse_unary()
            left = {
                'type': 'binary',
                'operator': op,
                'left': left,
                'right': right
            }
        
        return left
    
    def _parse_unary(self) -> Dict[str, Any]:
        """解析一元表达式"""
        if self._check(TokenType.LOGICAL) and self._peek().value == 'not':
            self._advance()
            op = self._previous().value
            expr = self._parse_unary()
            return {
                'type': 'unary',
                'operator': op,
                'operand': expr
            }
        
        return self._parse_primary()
    
    def _parse_primary(self) -> Dict[str, Any]:
        """解析基本表达式"""
        # 数字
        if self._match(TokenType.NUMBER):
            return {'type': 'number', 'value': self._previous().value}
        
        # 字符串
        if self._match(TokenType.STRING):
            return {'type': 'string', 'value': self._previous().value}
        
        # 布尔值
        if self._match(TokenType.BOOLEAN):
            return {'type': 'boolean', 'value': self._previous().value}
        
        # NULL
        if self._match(TokenType.NULL):
            return {'type': 'null', 'value': None}
        
        # 函数调用
        if self._match(TokenType.FUNCTION):
            return self._parse_function_call()
        
        # 标识符或字段引用
        if self._match(TokenType.IDENTIFIER):
            return self._parse_identifier_or_field()
        
        # 括号表达式
        if self._match(TokenType.LPAREN):
            expr = self._parse_expression()
            self._consume(TokenType.RPAREN, "Expected ')' after expression")
            return expr
        
        raise ValueError(f"Unexpected token: {self._peek()}")
    
    def _parse_function_call(self) -> Dict[str, Any]:
        """解析函数调用"""
        func_name = self._previous().value
        self._consume(TokenType.LPAREN, f"Expected '(' after function name '{func_name}'")
        
        args = []
        if not self._check(TokenType.RPAREN):
            args.append(self._parse_expression())
            while self._match(TokenType.COMMA):
                args.append(self._parse_expression())
        
        self._consume(TokenType.RPAREN, "Expected ')' after arguments")
        
        return {
            'type': 'function_call',
            'function': func_name,
            'arguments': args
        }
    
    def _parse_identifier_or_field(self) -> Dict[str, Any]:
        """解析标识符或字段引用"""
        name = self._previous().value
        
        # 检查是否是字段引用 (Entity.field)
        if self._match(TokenType.DOT):
            field = self._consume(TokenType.IDENTIFIER, "Expected field name after '.'").value
            return {
                'type': 'field_reference',
                'entity': name,
                'field': field
            }
        
        # 检查是否后跟函数调用
        if self._check(TokenType.LPAREN):
            self._advance()
            args = []
            if not self._check(TokenType.RPAREN):
                args.append(self._parse_expression())
                while self._match(TokenType.COMMA):
                    args.append(self._parse_expression())
            self._consume(TokenType.RPAREN, "Expected ')' after arguments")
            
            return {
                'type': 'function_call',
                'function': name,
                'arguments': args
            }
        
        return {'type': 'identifier', 'value': name}
    
    # Helper methods
    def _match(self, *types: TokenType) -> bool:
        """检查并消费匹配的token"""
        for token_type in types:
            if self._check(token_type):
                self._advance()
                return True
        return False
    
    def _check(self, token_type: TokenType) -> bool:
        """检查当前token类型"""
        if self._is_at_end():
            return False
        return self._peek().type == token_type
    
    def _advance(self) -> Token:
        """前进到下一个token"""
        if not self._is_at_end():
            self.current += 1
        return self._previous()
    
    def _is_at_end(self) -> bool:
        """检查是否到达结尾"""
        return self._peek().type == TokenType.EOF
    
    def _peek(self) -> Token:
        """查看当前token"""
        return self.tokens[self.current]
    
    def _previous(self) -> Token:
        """获取前一个token"""
        return self.tokens[self.current - 1]
    
    def _consume(self, token_type: TokenType, message: str) -> Token:
        """消费期望的token类型"""
        if self._check(token_type):
            return self._advance()
        
        current = self._peek()
        raise ValueError(f"{message} at position {current.position}, got {current}")
    
    # Evaluation methods
    def _evaluate_binary(self, ast: Dict[str, Any], context: Dict[str, Any]) -> Any:
        """求值二元表达式"""
        left = self.evaluate(ast['left'], context)
        op = ast['operator']
        
        # 短路求值
        if op == 'and' and not left:
            return False
        if op == 'or' and left:
            return True
        if op == '=>' and not left:
            return True  # 前件为假，蕴含为真
        
        right = self.evaluate(ast['right'], context)
        
        # 比较运算
        if op == '>':
            return left > right if left is not None and right is not None else False
        elif op == '<':
            return left < right if left is not None and right is not None else False
        elif op == '>=':
            return left >= right if left is not None and right is not None else False
        elif op == '<=':
            return left <= right if left is not None and right is not None else False
        elif op == '==':
            return left == right
        elif op == '!=':
            return left != right
        
        # 逻辑运算
        elif op == 'and':
            return bool(left) and bool(right)
        elif op == 'or':
            return bool(left) or bool(right)
        elif op == '=>':
            return not bool(left) or bool(right)
        
        # 算术运算
        elif op == '+':
            return left + right if left is not None and right is not None else None
        elif op == '-':
            return left - right if left is not None and right is not None else None
        elif op == '*':
            return left * right if left is not None and right is not None else None
        elif op == '/':
            return left / right if left is not None and right is not None and right != 0 else None
        
        return None
    
    def _evaluate_unary(self, ast: Dict[str, Any], context: Dict[str, Any]) -> Any:
        """求值一元表达式"""
        op = ast['operator']
        operand = self.evaluate(ast['operand'], context)
        
        if op == 'not':
            return not bool(operand)
        
        return None
    
    def _evaluate_function(self, ast: Dict[str, Any], context: Dict[str, Any]) -> Any:
        """求值函数调用"""
        func_name = ast['function'].lower()
        args = [self.evaluate(arg, context) for arg in ast['arguments']]
        
        if func_name == 'size' or func_name == 'len':
            if args and hasattr(args[0], '__len__'):
                return len(args[0])
            return 0
        
        elif func_name == 'min':
            return min(args) if args else None
        
        elif func_name == 'max':
            return max(args) if args else None
        
        elif func_name == 'sum':
            return sum(args) if args else 0
        
        elif func_name == 'avg':
            return sum(args) / len(args) if args else 0
        
        return None
    
    def _resolve_identifier(self, name: str, context: Dict[str, Any]) -> Any:
        """解析标识符"""
        # 查找上下文中的值
        if name in context:
            return context[name]
        
        # 尝试解析为属性路径
        parts = name.split('_')
        if len(parts) > 1:
            entity = parts[0]
            attr = '_'.join(parts[1:])
            if entity in context and isinstance(context[entity], dict):
                return context[entity].get(attr)
        
        return None
    
    def _resolve_field_reference(self, entity: str, field: str, context: Dict[str, Any]) -> Any:
        """解析字段引用"""
        if entity in context:
            if isinstance(context[entity], dict):
                return context[entity].get(field)
        return None