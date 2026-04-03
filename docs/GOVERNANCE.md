# LeanYo governance

## Lemma database management

### Ownership and responsibility

User-registered lemmas (`@[naturality]`, `@[yo.fuse]`) and the built-in rewrite sets should stay **sound**, **scoped**, and **easy to review**. This document describes how the project thinks about quality; it is not a literal description of every automated check (see **Automated checks** below).

### Core Principles

1. **Quality over Quantity**: Every lemma must provide clear value
2. **No Loops**: All lemmas must pass loop-checking validation
3. **Minimal Examples**: Every lemma must include a minimal reproducible example
4. **Performance Impact**: Lemmas must not significantly degrade tactic performance
5. **Community Review**: All lemma additions require community review

## Lemma Addition Process

### 1. Proposal Phase

Before adding a new lemma to the database:

1. **Create Issue**: Open a GitHub issue describing the proposed lemma
2. **Provide Justification**: Explain why the lemma is needed
3. **Include Example**: Provide a minimal reproducible example
4. **Performance Analysis**: Analyze potential performance impact

### 2. Review phase

The review process includes:

1. **Technical review**: Maintainer / reviewer reads the lemma and its use cases
2. **Regression tests**: Add or extend `example` proofs in `LeanYo.Tests.P0` / `P1` / `P2` when behavior changes
3. **Script checks**: the test pipeline runs `scripts/validate_lemmas.py` and `scripts/production_test.py` (heuristic checks, not a proof of termination for every rewrite path)
4. **Community input**: Discussion on the PR or in GitHub Discussions / Zulip as appropriate

### 3. Implementation Phase

After approval:

1. **Implementation**: Add the lemma with proper attributes
2. **Testing**: Include in test suites
3. **Documentation**: Update documentation
4. **Monitoring**: Monitor performance impact

## Loop prevention

### Automatic checks (today)

Automated builds on each change compile the library and tests, run a quick timing check, and run the Python helper scripts in `scripts/`. Nothing here proves “no infinite rewrite chains” for every possible user lemma.

### Design goal (review)

Reviewers should still watch for lemmas that could cause **rewrite loops** or **explosive simp search** in interaction with `naturality!` / `yo`.

### Manual review checklist

Before approving any lemma:

- [ ] Does the lemma have a clear, single purpose?
- [ ] Is the lemma necessary (not redundant with existing lemmas)?
- [ ] Does the PR include a minimal `example` (or test-module proof) that exercises it?
- [ ] Could this lemma interact badly with existing simp / rewrite sets (loops, blow-ups)?
- [ ] Is the lemma documented (docstring or linked usage guide section)?
- [ ] Have the automated checks on the pull request passed?

## Quality gates

### Performance (review guidelines)

These are **guidelines for human review**, not automatic numeric gates:

- Prefer lemmas that simplify typical goals without huge simp sets
- Avoid registering lemmas that match too broadly on every goal
- If a change slows interactive proofs noticeably, discuss on the PR and consider opt-in registration or narrower patterns

### Validation Rules

All lemmas must satisfy:

1. **Type Safety**: Correct typing and well-formed expressions
2. **Soundness**: Mathematically correct statements
3. **Completeness**: Covers intended use cases
4. **Efficiency**: Optimal implementation
5. **Maintainability**: Clear, readable code

## Lemma Categories

### Naturality Lemmas (`@[naturality]`)

**Purpose**: Register natural transformation naturality lemmas

**Requirements**:
- Must express naturality conditions: `η.app X ≫ G.map f = F.map f ≫ η.app Y`
- Must be about natural transformations
- Must include proper type annotations
- Must pass naturality pattern validation

**Examples**:
```lean
@[naturality]
theorem functor_map_naturality {C D : Type} [Category C] [Category D] 
  (F : C ⥤ D) (X Y : C) (f : X ⟶ Y) :
  F.map f ≫ F.map (𝟙 Y) = F.map (𝟙 X) ≫ F.map f := by
  simp [Functor.map_comp, Functor.map_id]
```

### Fusion Lemmas (`@[yo.fuse]`)

**Purpose**: Register lemmas that fuse map_comp, whisker laws, functoriality

**Requirements**:
- Must express fusion rules for category theory operations
- Must be about functoriality, composition, or whiskering
- Must include proper type annotations
- Must pass fusion pattern validation

**Examples**:
```lean
@[yo.fuse]
theorem functor_comp_fusion {C D E : Type} [Category C] [Category D] [Category E]
  (F : C ⥤ D) (G : D ⥤ E) (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z) :
  (F ⋙ G).map (f ≫ g) = G.map (F.map f) ≫ G.map (F.map g) := by
  simp [Functor.comp_map]
```

## Maintenance Procedures

### Regular Audits

Monthly audits of the lemma database:

1. **Performance Review**: Check for performance regressions
2. **Usage Analysis**: Identify unused or redundant lemmas
3. **Quality Assessment**: Review lemma quality and documentation
4. **Community Feedback**: Gather user feedback on lemma effectiveness

### Cleanup Process

Quarterly cleanup of the lemma database:

1. **Remove Unused Lemmas**: Delete lemmas with no usage
2. **Consolidate Redundant Lemmas**: Merge similar lemmas
3. **Optimize Performance**: Improve slow lemmas
4. **Update Documentation**: Ensure all lemmas are documented

### Deprecation Policy

When deprecating lemmas:

1. **Notice Period**: 3-month notice before removal
2. **Migration Guide**: Provide migration path for users
3. **Gradual Removal**: Phase out deprecated lemmas
4. **Community Communication**: Clear communication about changes

## Review Process

### Maintainer Responsibilities

- **Technical Review**: Ensure technical correctness
- **Performance Analysis**: Verify performance impact
- **Quality Assurance**: Maintain high standards
- **Community Liaison**: Represent community interests

### Community Involvement

- **Proposal Submission**: Anyone can propose new lemmas
- **Feedback Provision**: Community provides feedback on proposals
- **Usage Reporting**: Report issues with existing lemmas
- **Performance Monitoring**: Help monitor performance impact

## Decision Making

### Approval Process

1. **Proposal**: Community member submits proposal
2. **Initial Review**: Maintainer performs initial technical review
3. **Community Discussion**: Open discussion period (1 week)
4. **Final Review**: Maintainer makes final decision
5. **Implementation**: Approved proposals are implemented

### Appeals Process

If a proposal is rejected:

1. **Appeal Request**: Request appeal within 1 week
2. **Additional Review**: Independent maintainer reviews
3. **Community Vote**: Community vote on controversial decisions
4. **Final Decision**: Binding decision by project maintainers

## Performance monitoring

### What maintainers can do

- Watch build times after Mathlib bumps
- Use local profiling (`measurePerformance`, telemetry) when investigating tactic cost
- Gather qualitative feedback via issues and community channels

There is no dedicated production metrics stack in this repository.

## Documentation Requirements

### For Each Lemma

Required documentation:

1. **Purpose**: Clear statement of what the lemma does
2. **Use Cases**: When and why to use the lemma
3. **Examples**: Minimal reproducible examples
4. **Performance Notes**: Any performance considerations
5. **Related Lemmas**: Links to related lemmas

### Example Documentation

```lean
/--
Naturality lemma for functor composition.

This lemma expresses the naturality condition for the composition
of two functors. It is used by the `naturality!` tactic to solve
goals involving functor composition and natural transformations.

## Use Cases
- Proving naturality squares involving functor composition
- Simplifying goals with complex functor chains
- Establishing coherence conditions for composed functors

## Examples
```lean
example {C D E : Type} [Category C] [Category D] [Category E]
  (F : C ⥤ D) (G : D ⥤ E) (η : F ⟶ F) (X Y : C) (f : X ⟶ Y) :
  (G ⋙ F).map f ≫ (G ⋙ η).app Y = (G ⋙ η).app X ≫ (G ⋙ F).map f := by
  naturality!
```

## Performance
- Keep this lemma narrow enough that `naturality!` does not try it on unrelated goals.
-/
@[naturality]
theorem functor_comp_naturality {C D E : Type} [Category C] [Category D] [Category E]
  (F : C ⥤ D) (G : D ⥤ E) (η : F ⟶ F) (X Y : C) (f : X ⟶ Y) :
  (G ⋙ F).map f ≫ (G ⋙ η).app Y = (G ⋙ η).app X ≫ (G ⋙ F).map f := by
  naturality!
```

## Enforcement

### Automated checks

On each push and pull request, the project runs a standard build and test pipeline (Lean library, examples, test modules, helper scripts, and a Docker image build). Maintainers may also run scheduled dependency updates that open a pull request when the tree still builds.

### Manual enforcement

- **Code review** for lemma and tactic changes
- **Community oversight** via issues and discussions
- **Docs updates** when user-visible behavior changes

## Contact and Support

### For Lemma Proposals

- **GitHub Issues**: Submit proposals via GitHub issues
- **Discussion Forum**: Use GitHub Discussions for questions
- **Email**: Contact maintainers for private discussions

### For Issues and Feedback

- **Bug Reports**: Use GitHub Issues for bug reports
- **Feature Requests**: Use GitHub Issues for feature requests
- **Performance Issues**: Use GitHub Issues for performance problems
- **Documentation Issues**: Use GitHub Issues for documentation problems

This framework is meant to keep LeanYo’s lemma story **reviewable** and **aligned with what automated checks verify**. Propose changes via pull requests; see [Contributing](../CONTRIBUTING.md).
