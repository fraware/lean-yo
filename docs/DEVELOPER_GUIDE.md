# Developer Guide

This document provides comprehensive guidance for developers working on the lean-yo library.

## Architecture Overview

The `lean-yo` library is built around a modular architecture with the following key components:

### Core Modules

1. **`LeanYo.Tactics`**: Main tactic implementations (`yo`, `naturality!`, debug variants)
2. **`LeanYo.RewriteKernel`**: Core rewriting logic for Yoneda and naturality transformations
3. **`LeanYo.Attributes`**: Attribute system for lemma registration (`@[naturality]`, `@[yo.fuse]`)
4. **`LeanYo.Options`**: Configuration management and state handling
5. **`LeanYo.Utils`**: Utility functions and performance measurement
6. **`LeanYo.SimpSets`**: Local simp sets tuned for category theory operations

### Test Modules

- **`LeanYo.Tests.P0`**: Basic functoriality and simple naturality tests
- **`LeanYo.Tests.P1`**: Whiskering, composition, and bifunctor tests  
- **`LeanYo.Tests.P2`**: Yoneda/Coyoneda and advanced category theory tests
- **`LeanYo.Tests.Benchmarks`**: Performance benchmarking and SLA validation
- **`LeanYo.Examples`**: Working examples demonstrating tactic usage

### Rewrite Kernel

The rewrite kernel operates in two main phases:

1. **Yoneda Step**: Applies `Hom(-,X)` or `Hom(X,-)` equivalence
2. **Naturality Step**: Consults the lemma database to rewrite naturality squares

### Detection System

The library automatically detects candidates for rewriting by looking for:
- `Category.comp` chains with functor maps
- Natural transformation applications
- Goals mentioning `Hom` functors

## Adding New Features

### Adding New Tactics

1. Define the tactic in `LeanYo/Tactics.lean`
2. Add corresponding tests in the appropriate test suite
3. Update documentation

### Adding New Attributes

1. Register the attribute in `LeanYo/Attributes.lean`
2. Add validation logic
3. Update the rewrite kernel to use the new attribute

### Adding New Options

1. Add the option to `LeanYo/Options.lean`
2. Add getter/setter functions
3. Update tactic implementations to use the option

## Testing

### Test Suites

- **P0**: Basic functoriality and simple naturality squares
- **P1**: Whiskering, composition of natural transformations, bifunctors
- **P2**: Coyoneda reductions, dinaturality on ends/coends

### Running Tests

```bash
# Run all tests
lake test

# Run specific test suite
lake build LeanYo.Tests.P0
lake build LeanYo.Tests.P1
lake build LeanYo.Tests.P2
```

### Adding Tests

1. Add test cases to the appropriate test suite
2. Ensure tests are deterministic and fast
3. Add performance benchmarks for new features

## Performance Considerations

### Performance SLAs

- P50 ≤ 80ms per call on P0/P1 suites
- P95 ≤ 400ms per call on P0/P1 suites
- ≥60% reduction in manual steps on large diagrams

### Optimization Guidelines

1. Use timeouts to prevent infinite loops
2. Implement efficient lemma lookup
3. Cache frequently used computations
4. Minimize memory allocations

### Profiling

Use the built-in telemetry system to monitor performance:

```lean
-- Get telemetry data
#eval LeanYo.getTelemetry

-- Reset telemetry
#eval LeanYo.resetTelemetry
```

## Debugging

### Debug Tactics

Use `yo?` and `naturality?` to see what rewrites are being applied:

```lean
example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X : C) :
  F.map (𝟙 X) = 𝟙 (F.obj X) := by
  yo?  -- Shows the exact rewrites used
```

### Common Issues

1. **Tactic not applying**: Check if the goal is a candidate for rewriting
2. **Infinite loops**: Use timeouts and direction settings
3. **Performance issues**: Profile with telemetry and optimize hot paths

## Contributing Guidelines

### Code Style

- Follow Lean 4 style guidelines
- Use descriptive names
- Add comprehensive documentation
- Include type annotations where helpful

### Pull Request Process

1. Create a feature branch
2. Add tests for new functionality
3. Ensure all tests pass
4. Update documentation
5. Submit PR with clear description

### Review Process

- All PRs require review
- Tests must pass
- Performance regressions are not allowed
- Documentation must be updated

## Maintenance

### Dependency Management

- Keep Mathlib4 compatibility matrix updated
- Pin specific SHA for stability
- Regular dependency updates

### Release Process

1. Update version in `lakefile.lean`
2. Update changelog
3. Create release tag
4. Publish to package registry

## Troubleshooting

### Common Build Issues

1. **Mathlib version conflicts**: Check compatibility matrix
2. **Lean version issues**: Ensure correct toolchain
3. **Cache issues**: Run `lake exe cache get`

### Runtime Issues

1. **Tactic failures**: Check goal structure and options
2. **Performance issues**: Profile and optimize
3. **Memory issues**: Check for infinite loops

## Development Workflow

### 1. Setup

```bash
# Clone the repository
git clone https://github.com/your-username/lean-yo.git
cd lean-yo

# Install dependencies
lake update

# Build the library
lake build
```

### 2. Making Changes

1. **Create a feature branch**:
   ```bash
   git checkout -b feature/your-feature-name
   ```

2. **Make your changes** following the coding standards:
   - Use state-of-the-art software engineering practices
   - Triple-check all code
   - Follow Lean 4 naming conventions
   - Add comprehensive documentation

3. **Add tests** for new functionality:
   - Add to appropriate test suite (P0, P1, P2)
   - Include both positive and negative test cases
   - Ensure tests are deterministic and non-flaky

4. **Run the test suite**:
   ```bash
   lake test
   ```

5. **Run performance benchmarks**:
   ```bash
   lake run LeanYo.Tests.Benchmarks.runComprehensiveBenchmarks
   ```

6. **Check for linting errors**:
   ```bash
   lake build --warn
   ```

### 3. Code Review Process

1. **Submit a pull request** with:
   - Clear description of changes
   - Reference to related issues
   - Performance impact analysis
   - Updated documentation

2. **Address review feedback**:
   - Respond to all comments
   - Make requested changes
   - Update tests if needed

3. **Ensure CI passes**:
   - All tests must pass
   - Performance SLAs must be met
   - No linting errors

## Code Standards

### Naming Conventions

- **Modules**: PascalCase (`LeanYo.Tactics`)
- **Functions**: camelCase (`yoTactic`)
- **Types**: PascalCase (`YoDirection`)
- **Constants**: snake_case (`global_options`)

### Documentation

- **Module headers**: Include purpose and usage examples
- **Function documentation**: Include parameter descriptions and return values
- **Inline comments**: Explain complex logic and algorithms
- **Examples**: Provide working examples for all public APIs

### Error Handling

- **Graceful degradation**: Tactics should fail gracefully
- **Clear error messages**: Provide helpful error messages
- **Timeout handling**: Implement proper timeout mechanisms
- **Validation**: Validate inputs and configurations

## Architecture Guidelines

### Module Design

- **Single responsibility**: Each module should have a clear, single purpose
- **Loose coupling**: Minimize dependencies between modules
- **High cohesion**: Related functionality should be grouped together
- **Clear interfaces**: Define clear APIs between modules

### Performance Considerations

- **Efficient algorithms**: Use efficient algorithms and data structures
- **Memory management**: Minimize memory allocations
- **Caching**: Cache expensive computations when appropriate
- **Lazy evaluation**: Use lazy evaluation where beneficial

### Safety Features

- **Timeout mechanisms**: Implement hard timeouts to prevent infinite loops
- **Direction control**: Provide explicit direction control to avoid flip-flops
- **Validation**: Validate all inputs and configurations
- **Error recovery**: Implement proper error recovery mechanisms

## Contributing Guidelines

### Pull Request Process

1. **Fork and branch**: Create a feature branch from `main`
2. **Implement changes**: Follow coding standards and architecture guidelines
3. **Add tests**: Include comprehensive tests for all new functionality
4. **Update documentation**: Update relevant documentation
5. **Run CI**: Ensure all CI checks pass
6. **Submit PR**: Create a pull request with clear description

### Review Process

1. **Automated checks**: CI runs tests, benchmarks, and linting
2. **Code review**: At least one maintainer reviews the code
3. **Performance review**: Performance impact is assessed
4. **Documentation review**: Documentation is reviewed for clarity
5. **Approval**: Changes are approved and merged

### Release Process

1. **Version bump**: Update version in `lakefile.lean`
2. **Changelog**: Update `CHANGELOG.md` with changes
3. **Tag release**: Create a git tag for the release
4. **Publish**: Publish to the package registry

## Troubleshooting

### Common Issues

1. **Build failures**: Check Lean version compatibility
2. **Test failures**: Ensure all dependencies are installed
3. **Performance issues**: Run benchmarks to identify bottlenecks
4. **Memory issues**: Check for memory leaks in long-running processes

### Debugging

1. **Use debug tactics**: `yo?` and `naturality?` provide detailed information
2. **Enable logging**: Use appropriate logging levels
3. **Profile performance**: Use profiling tools to identify bottlenecks
4. **Check telemetry**: Review telemetry data for patterns

### Getting Help

1. **Documentation**: Check this guide and inline documentation
2. **Issues**: Search existing issues on GitHub
3. **Discussions**: Use GitHub Discussions for questions
4. **Maintainers**: Contact maintainers for urgent issues

## Future Development

### Planned Features

1. **Enhanced Yoneda support**: More sophisticated Yoneda isomorphism handling
2. **Advanced naturality**: Support for more complex naturality patterns
3. **Performance optimizations**: Further performance improvements
4. **Extended test coverage**: More comprehensive test suites
5. **Better error messages**: More helpful error messages and suggestions

### Contributing to Future Development

1. **Propose features**: Use GitHub Issues to propose new features
2. **Discuss design**: Use GitHub Discussions for design discussions
3. **Implement features**: Follow the development workflow
4. **Share feedback**: Provide feedback on existing features

## Resources

### Documentation

- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
- [Mathlib4 Documentation](https://leanprover-community.github.io/)
- [Category Theory in Lean](https://leanprover-community.github.io/mathlib_docs/category_theory/)

### Tools

- [Lean 4 VS Code Extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
- [Lake Package Manager](https://github.com/leanprover/lake)
- [Mathlib4 Tools](https://github.com/leanprover-community/mathlib4)

### Community

- [Lean Zulip](https://leanprover.zulipchat.com/)
- [GitHub Discussions](https://github.com/fraware/lean-yo/discussions)
- [Mathlib4 Zulip](https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4)
