# Changelog

All notable changes to the DSL Test Generator project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [9.0.0] - 2025-07-16 - Domain-Agnostic Revolution

### Revolutionary Changes
- **Complete Domain Independence**: Removed ALL domain-specific code
- **Semantic Intelligence**: Automatic understanding of attribute meanings from naming patterns
- **Universal Constraint Handling**: Generic processing of any constraint expression
- **Cross-Entity Business Rules**: Support for complex rules spanning multiple entities

### Added
- `GenericConstraintTestStrategy`: Universal constraint test generation
- `SemanticValueGenerator`: Context-aware value generation based on semantics
- Automatic constraint extraction and testing
- Business rule parsing and test generation
- Cross-entity relationship handling
- Quick Start Guide for rapid onboarding

### Improved
- Zero code changes needed between different domains
- 100% constraint coverage achieved automatically
- Intelligent value generation respecting all constraints
- Better test organization and categorization
- Enhanced documentation with semantic naming guide

### Removed
- All hardcoded domain-specific strategies
- Manual constraint handling requirements
- Domain-specific value generators
- Legacy v2.0 experimental version

### Proven Results
- Cleaning Dispatch: 47 tests with full coverage
- Banking System: 37 tests without any modifications
- E-commerce: Complete workflow testing

## [8.0.0] - 2025-07-14 - Extended Edition

### Added
- Extended test generator with state machine support
- Scenario-based test generation
- Timed constraint testing
- Enhanced YAML parser for complex DSL structures
- Comprehensive test coverage reporting
- `generate_extended.py` script for advanced testing

### Improved
- Test generation stability (91.4% pass rate)
- Z3 constraint solving performance
- Error handling and logging
- Documentation and examples

### Fixed
- Edge case handling in boundary tests
- State transition validation
- Constraint solver timeout issues

## [0.3.0] - 2024-01-09

### Added
- **Configuration System**: New `DSLEngineConfig` class for customizing engine behavior
  - Configurable test types and scenarios
  - Adjustable numeric precision and limits
  - Customizable operator mappings
  - Z3 solver settings (timeout, random seed)
- **Business Logic Validation**: New `BusinessLogicValidator` for ensuring realistic test data
  - Enforces cross-entity constraints (e.g., claim_type == policy_type)
  - Fixes dependent attribute relationships
  - Applies domain-specific business rules
  - Optional validation (can be disabled for performance)
- **API Documentation**: Comprehensive API reference in `docs/API_REFERENCE.md`
  - Complete class and method documentation
  - Usage examples for all major features
  - Configuration guide
  - Error handling best practices

### Changed
- Removed hardcoded values throughout the codebase
  - Test types now configurable (previously hardcoded as ["boundary", "equivalence", etc.])
  - Numeric precision configurable (previously fixed at 6 decimal places)
  - Collection size limits configurable (previously fixed at 10/100 elements)
  - String hash modulo configurable (previously fixed at 1000000)
- Enhanced test generation to use configuration values
- Improved cross-entity constraint handling

### Fixed
- Fixed issue where constraints without descriptions caused crashes
- Fixed business logic violations in generated test data
- Improved handling of simple constraint patterns (e.g., `claim_type == policy_type`)

## [0.2.0] - 2024-01-01

### Added
- Enhanced type system with array and set support
- Collection testing capabilities
- Smart test generator with business logic understanding
- CLI tool `dsl2test.py`

### Changed
- Restructured project to use modern Python packaging
- Improved test deduplication

## [0.1.0] - 2023-12-15

### Added
- Initial release
- Basic DSL parsing
- Z3 solver integration
- Boundary and equivalence test generation