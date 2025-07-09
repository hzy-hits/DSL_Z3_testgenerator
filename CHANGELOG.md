# Changelog

All notable changes to the DSL Test Generator project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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