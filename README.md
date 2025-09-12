# lean-yo

A Lean 4 tactic library that simplifies proofs involving categories, functors, and natural transformations by leveraging (co)Yoneda isomorphisms.

## Overview

`lean-yo` provides two main tactics:

- **`yo`**: Transforms morphism goals into pointwise goals using (co)Yoneda isomorphisms
- **`naturality!`**: Closes standard naturality squares and whiskering equations

The library emphasizes minimal configuration, safe defaults, robustness on large diagrams, and provides readable explanations.

## Installation

Add to your `lakefile.lean`:

```lean
require lean-yo from git "https://github.com/fraware/lean-yo.git"
```

## Usage

### Basic Tactics

```lean
import LeanYo

-- Transform morphism goals using Yoneda isomorphisms
example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X : C) :
  F.map (𝟙 X) = 𝟙 (F.obj X) := by
  yo

-- Solve naturality squares
example {C D : Type} [Category C] [Category D] (F G : C ⥤ D) (η : F ⟶ G) (X Y : C) (f : X ⟶ Y) :
  η.app X ≫ G.map f = F.map f ≫ η.app Y := by
  naturality!
```

### Debug Tactics

```lean
-- Print the exact rewrites used by yo
yo?

-- Print the exact rewrites used by naturality!
naturality?
```

### Working with Hypotheses

```lean
-- Apply yo to a hypothesis
yo at h

-- Apply naturality! to a hypothesis
naturality! at h
```

### Configuration

```lean
-- Set Yoneda direction
yo.direction := covariant
yo.direction := contravariant
yo.direction := auto  -- default

-- Set naturality! options
naturality.maxSteps := 64  -- default
naturality.timeout := 1500ms  -- default
```

## Attributes

### @[naturality]

Register natural transformation naturality lemmas:

```lean
@[naturality]
theorem my_naturality_lemma {C D : Type} [Category C] [Category D] 
  (F G : C ⥤ D) (η : F ⟶ G) (X Y : C) (f : X ⟶ Y) :
  η.app X ≫ G.map f = F.map f ≫ η.app Y := by
  -- proof
```

### @[yo.fuse]

Register lemmas that fuse `map_comp`, whisker laws, and functoriality:

```lean
@[yo.fuse]
theorem my_fusion_lemma {C D : Type} [Category C] [Category D] 
  (F : C ⥤ D) (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z) :
  F.map (f ≫ g) = F.map f ≫ F.map g := by
  -- proof
```

## When to Use Which Tactic

### Use `yo` when:
- You have morphism goals involving functor maps
- You want to transform goals using Yoneda isomorphisms
- You're working with `Category.comp` chains with functor maps

### Use `naturality!` when:
- You have naturality square goals
- You're working with natural transformations
- You have goals of the form `η.app _ ≫ _ = _ ≫ η.app _`

## Common Pitfalls

1. **Over-rewriting**: The tactics are designed to be safe, but be aware of potential infinite loops
2. **Direction confusion**: Use `yo.direction := auto` to let the tactic decide the direction
3. **Timeout issues**: Increase `naturality.timeout` for complex diagrams

## Performance

The library is designed to meet the following performance SLAs:
- P50 ≤ 80ms per call on P0/P1 test suites
- P95 ≤ 400ms per call on P0/P1 test suites
- ≥60% reduction in manual steps on large diagrams

## Contributing

1. Fork the repository
2. Create a feature branch
3. Add tests for new functionality
4. Ensure all tests pass
5. Submit a pull request

## License

This project is licensed under the MIT License - see the LICENSE file for details.

## Compatibility

- Lean 4: v4.8.0+
- Mathlib4: compatible with main and stable branches
