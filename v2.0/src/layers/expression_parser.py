"""
Expression Parser for V2.0

Robust expression parser that converts DSL expressions to AST.
"""

from typing import Any, Dict, List, Optional, Union
from dataclasses import dataclass
from enum import Enum
import re


class TokenType(Enum):
    """Token types for lexer"""
    # Literals
    NUMBER = "NUMBER"
    STRING = "STRING"
    BOOLEAN = "BOOLEAN"
    IDENTIFIER = "IDENTIFIER"
    
    # Operators
    PLUS = "PLUS"
    MINUS = "MINUS"
    MULTIPLY = "MULTIPLY"
    DIVIDE = "DIVIDE"
    MODULO = "MODULO"
    
    # Comparison
    EQ = "EQ"
    NEQ = "NEQ"
    LT = "LT"
    LE = "LE"
    GT = "GT"
    GE = "GE"
    
    # Logical
    AND = "AND"
    OR = "OR"
    NOT = "NOT"
    IMPLIES = "IMPLIES"
    
    # Delimiters
    LPAREN = "LPAREN"
    RPAREN = "RPAREN"
    COMMA = "COMMA"
    
    # Special
    EOF = "EOF"


@dataclass
class Token:
    """Lexer token"""
    type: TokenType
    value: Any
    position: int


class Lexer:
    """Tokenize expressions"""
    
    def __init__(self, text: str):
        self.text = text
        self.position = 0
        self.tokens = []
        
    def tokenize(self) -> List[Token]:
        """Convert text to tokens"""
        while self.position < len(self.text):
            self._skip_whitespace()
            
            if self.position >= len(self.text):
                break
                
            # Numbers
            if self._current_char().isdigit():
                self._read_number()
            # Identifiers and keywords
            elif self._current_char().isalpha() or self._current_char() == '_':
                self._read_identifier()
            # String literals
            elif self._current_char() in ['"', "'"]:
                self._read_string()
            # Operators
            else:
                self._read_operator()
        
        self.tokens.append(Token(TokenType.EOF, None, self.position))
        return self.tokens
    
    def _current_char(self) -> str:
        """Get current character"""
        if self.position < len(self.text):
            return self.text[self.position]
        return ''
    
    def _peek_char(self) -> str:
        """Peek next character"""
        if self.position + 1 < len(self.text):
            return self.text[self.position + 1]
        return ''
    
    def _skip_whitespace(self):
        """Skip whitespace characters"""
        while self.position < len(self.text) and self.text[self.position].isspace():
            self.position += 1
    
    def _read_number(self):
        """Read numeric literal"""
        start = self.position
        has_dot = False
        
        while self.position < len(self.text):
            char = self._current_char()
            if char.isdigit():
                self.position += 1
            elif char == '.' and not has_dot:
                has_dot = True
                self.position += 1
            else:
                break
        
        value = self.text[start:self.position]
        if has_dot:
            self.tokens.append(Token(TokenType.NUMBER, float(value), start))
        else:
            self.tokens.append(Token(TokenType.NUMBER, int(value), start))
    
    def _read_identifier(self):
        """Read identifier or keyword"""
        start = self.position
        
        while self.position < len(self.text):
            char = self._current_char()
            if char.isalnum() or char == '_':
                self.position += 1
            else:
                break
        
        value = self.text[start:self.position]
        
        # Check for keywords
        keywords = {
            'and': TokenType.AND,
            'or': TokenType.OR,
            'not': TokenType.NOT,
            'true': TokenType.BOOLEAN,
            'false': TokenType.BOOLEAN,
            'True': TokenType.BOOLEAN,
            'False': TokenType.BOOLEAN
        }
        
        if value in keywords:
            token_type = keywords[value]
            if token_type == TokenType.BOOLEAN:
                bool_value = value.lower() == 'true'
                self.tokens.append(Token(token_type, bool_value, start))
            else:
                self.tokens.append(Token(token_type, value, start))
        else:
            self.tokens.append(Token(TokenType.IDENTIFIER, value, start))
    
    def _read_string(self):
        """Read string literal"""
        start = self.position
        quote_char = self._current_char()
        self.position += 1  # Skip opening quote
        
        value = ''
        while self.position < len(self.text) and self._current_char() != quote_char:
            if self._current_char() == '\\':
                self.position += 1
                if self.position < len(self.text):
                    # Simple escape handling
                    escape_char = self._current_char()
                    if escape_char == 'n':
                        value += '\n'
                    elif escape_char == 't':
                        value += '\t'
                    else:
                        value += escape_char
                    self.position += 1
            else:
                value += self._current_char()
                self.position += 1
        
        if self.position < len(self.text):
            self.position += 1  # Skip closing quote
        
        self.tokens.append(Token(TokenType.STRING, value, start))
    
    def _read_operator(self):
        """Read operator"""
        start = self.position
        char = self._current_char()
        next_char = self._peek_char()
        
        # Two-character operators
        two_char = char + next_char
        if two_char == '==':
            self.tokens.append(Token(TokenType.EQ, '==', start))
            self.position += 2
        elif two_char == '!=':
            self.tokens.append(Token(TokenType.NEQ, '!=', start))
            self.position += 2
        elif two_char == '<=':
            self.tokens.append(Token(TokenType.LE, '<=', start))
            self.position += 2
        elif two_char == '>=':
            self.tokens.append(Token(TokenType.GE, '>=', start))
            self.position += 2
        elif two_char == '->':
            self.tokens.append(Token(TokenType.IMPLIES, '->', start))
            self.position += 2
        # Single-character operators
        elif char == '+':
            self.tokens.append(Token(TokenType.PLUS, '+', start))
            self.position += 1
        elif char == '-':
            self.tokens.append(Token(TokenType.MINUS, '-', start))
            self.position += 1
        elif char == '*':
            self.tokens.append(Token(TokenType.MULTIPLY, '*', start))
            self.position += 1
        elif char == '/':
            self.tokens.append(Token(TokenType.DIVIDE, '/', start))
            self.position += 1
        elif char == '%':
            self.tokens.append(Token(TokenType.MODULO, '%', start))
            self.position += 1
        elif char == '<':
            self.tokens.append(Token(TokenType.LT, '<', start))
            self.position += 1
        elif char == '>':
            self.tokens.append(Token(TokenType.GT, '>', start))
            self.position += 1
        elif char == '(':
            self.tokens.append(Token(TokenType.LPAREN, '(', start))
            self.position += 1
        elif char == ')':
            self.tokens.append(Token(TokenType.RPAREN, ')', start))
            self.position += 1
        elif char == ',':
            self.tokens.append(Token(TokenType.COMMA, ',', start))
            self.position += 1
        else:
            # Unknown character - skip
            self.position += 1


# AST Node Types

@dataclass
class ASTNode:
    """Base class for AST nodes"""
    pass


@dataclass
class NumberNode(ASTNode):
    """Numeric literal"""
    value: Union[int, float]


@dataclass
class StringNode(ASTNode):
    """String literal"""
    value: str


@dataclass
class BooleanNode(ASTNode):
    """Boolean literal"""
    value: bool


@dataclass
class IdentifierNode(ASTNode):
    """Variable/identifier reference"""
    name: str


@dataclass
class BinaryOpNode(ASTNode):
    """Binary operation"""
    operator: TokenType
    left: ASTNode
    right: ASTNode


@dataclass
class UnaryOpNode(ASTNode):
    """Unary operation"""
    operator: TokenType
    operand: ASTNode


@dataclass
class FunctionCallNode(ASTNode):
    """Function call"""
    name: str
    arguments: List[ASTNode]


class Parser:
    """Parse tokens into AST"""
    
    def __init__(self, tokens: List[Token]):
        self.tokens = tokens
        self.position = 0
    
    def parse(self) -> ASTNode:
        """Parse tokens into AST"""
        return self._parse_expression()
    
    def _current_token(self) -> Token:
        """Get current token"""
        if self.position < len(self.tokens):
            return self.tokens[self.position]
        return self.tokens[-1]  # EOF
    
    def _consume(self, expected_type: Optional[TokenType] = None) -> Token:
        """Consume and return current token"""
        token = self._current_token()
        if expected_type and token.type != expected_type:
            raise SyntaxError(f"Expected {expected_type}, got {token.type}")
        self.position += 1
        return token
    
    def _parse_expression(self) -> ASTNode:
        """Parse expression (lowest precedence)"""
        return self._parse_implies()
    
    def _parse_implies(self) -> ASTNode:
        """Parse implication (->)"""
        left = self._parse_or()
        
        while self._current_token().type == TokenType.IMPLIES:
            op = self._consume()
            right = self._parse_or()
            left = BinaryOpNode(op.type, left, right)
        
        return left
    
    def _parse_or(self) -> ASTNode:
        """Parse OR expression"""
        left = self._parse_and()
        
        while self._current_token().type == TokenType.OR:
            op = self._consume()
            right = self._parse_and()
            left = BinaryOpNode(op.type, left, right)
        
        return left
    
    def _parse_and(self) -> ASTNode:
        """Parse AND expression"""
        left = self._parse_not()
        
        while self._current_token().type == TokenType.AND:
            op = self._consume()
            right = self._parse_not()
            left = BinaryOpNode(op.type, left, right)
        
        return left
    
    def _parse_not(self) -> ASTNode:
        """Parse NOT expression"""
        if self._current_token().type == TokenType.NOT:
            op = self._consume()
            operand = self._parse_not()
            return UnaryOpNode(op.type, operand)
        
        return self._parse_comparison()
    
    def _parse_comparison(self) -> ASTNode:
        """Parse comparison operators"""
        left = self._parse_addition()
        
        comp_ops = {TokenType.EQ, TokenType.NEQ, TokenType.LT, 
                   TokenType.LE, TokenType.GT, TokenType.GE}
        
        if self._current_token().type in comp_ops:
            op = self._consume()
            right = self._parse_addition()
            left = BinaryOpNode(op.type, left, right)
        
        return left
    
    def _parse_addition(self) -> ASTNode:
        """Parse addition and subtraction"""
        left = self._parse_multiplication()
        
        while self._current_token().type in {TokenType.PLUS, TokenType.MINUS}:
            op = self._consume()
            right = self._parse_multiplication()
            left = BinaryOpNode(op.type, left, right)
        
        return left
    
    def _parse_multiplication(self) -> ASTNode:
        """Parse multiplication, division, modulo"""
        left = self._parse_unary()
        
        while self._current_token().type in {TokenType.MULTIPLY, TokenType.DIVIDE, TokenType.MODULO}:
            op = self._consume()
            right = self._parse_unary()
            left = BinaryOpNode(op.type, left, right)
        
        return left
    
    def _parse_unary(self) -> ASTNode:
        """Parse unary operators"""
        if self._current_token().type in {TokenType.PLUS, TokenType.MINUS}:
            op = self._consume()
            operand = self._parse_unary()
            return UnaryOpNode(op.type, operand)
        
        return self._parse_primary()
    
    def _parse_primary(self) -> ASTNode:
        """Parse primary expressions"""
        token = self._current_token()
        
        # Numbers
        if token.type == TokenType.NUMBER:
            self._consume()
            return NumberNode(token.value)
        
        # Strings
        elif token.type == TokenType.STRING:
            self._consume()
            return StringNode(token.value)
        
        # Booleans
        elif token.type == TokenType.BOOLEAN:
            self._consume()
            return BooleanNode(token.value)
        
        # Identifiers (could be variable or function call)
        elif token.type == TokenType.IDENTIFIER:
            name = token.value
            self._consume()
            
            # Check for function call
            if self._current_token().type == TokenType.LPAREN:
                self._consume()  # (
                args = []
                
                while self._current_token().type != TokenType.RPAREN:
                    args.append(self._parse_expression())
                    if self._current_token().type == TokenType.COMMA:
                        self._consume()
                
                self._consume(TokenType.RPAREN)  # )
                return FunctionCallNode(name, args)
            else:
                return IdentifierNode(name)
        
        # Parentheses
        elif token.type == TokenType.LPAREN:
            self._consume()  # (
            expr = self._parse_expression()
            self._consume(TokenType.RPAREN)  # )
            return expr
        
        else:
            raise SyntaxError(f"Unexpected token: {token.type}")


class ExpressionParser:
    """High-level expression parser"""
    
    def parse(self, expression: str) -> ASTNode:
        """Parse expression string to AST"""
        lexer = Lexer(expression)
        tokens = lexer.tokenize()
        parser = Parser(tokens)
        return parser.parse()
    
    def extract_variables(self, expression: str) -> List[str]:
        """Extract all variable names from expression"""
        ast = self.parse(expression)
        variables = []
        self._extract_variables_from_ast(ast, variables)
        return list(set(variables))
    
    def _extract_variables_from_ast(self, node: ASTNode, variables: List[str]):
        """Recursively extract variables from AST"""
        if isinstance(node, IdentifierNode):
            variables.append(node.name)
        elif isinstance(node, BinaryOpNode):
            self._extract_variables_from_ast(node.left, variables)
            self._extract_variables_from_ast(node.right, variables)
        elif isinstance(node, UnaryOpNode):
            self._extract_variables_from_ast(node.operand, variables)
        elif isinstance(node, FunctionCallNode):
            for arg in node.arguments:
                self._extract_variables_from_ast(arg, variables)