# LeanYo usage guide

## Overview

**LeanYo** provides tactics for category-theoretic proofs in Lean 4. This guide explains when and how to use each tactic effectively.

### Related documentation

- [README.md](../README.md) — install, Docker, quickstart
- [API reference](API_REFERENCE.md) — syntax and options
- [Developer guide](DEVELOPER_GUIDE.md) — building, tests, Mathlib pins
- [Contributing](../CONTRIBUTING.md) — how to contribute

## When to Use `yo` vs `naturality!`

### Use `yo` for:
- **Functoriality proofs**: `F.map (𝟙 X) = 𝟙 (F.obj X)`
- **Composition proofs**: `F.map (f ≫ g) = F.map f ≫ F.map g`
- **Yoneda reductions**: Converting morphism goals to pointwise form
- **General morphism equalities**: When you need to reason about functor maps

### Use `naturality!` for:
- **Naturality squares**: `η.app X ≫ G.map f = F.map f ≫ η.app Y`
- **Whiskering equations**: `(η ◫ θ).app X ≫ H.map f = F.map f ≫ (η ◫ θ).app Y`
- **Coherence conditions**: When natural transformations are involved
- **Composition of natural transformations**: Both horizontal and vertical

### Decision Tree

```
Is your goal about natural transformations?
├─ Yes → Use `naturality!`
│   ├─ Naturality squares → `naturality!`
│   ├─ Whiskering → `naturality!`
│   └─ NT composition → `naturality!`
└─ No → Use `yo`
    ├─ Functoriality → `yo`
    ├─ Yoneda reduction → `yo`
    └─ General morphism equality → `yo`
```

## Common Patterns and Recipes

### 1. Functoriality Proofs

```lean
-- Basic functoriality
example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X : C) :
  F.map (𝟙 X) = 𝟙 (F.obj X) := by
  yo

-- Composition functoriality  
example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z) :
  F.map (f ≫ g) = F.map f ≫ F.map g := by
  yo
```

### 2. Naturality Squares

```lean
-- Simple naturality
example {C D : Type} [Category C] [Category D] (F G : C ⥤ D) (η : F ⟶ G) (X Y : C) (f : X ⟶ Y) :
  η.app X ≫ G.map f = F.map f ≫ η.app Y := by
  naturality!

-- Complex naturality with whiskering
example {C D E : Type} [Category C] [Category D] [Category E]
  (F G : C ⥤ D) (H I : D ⥤ E) (η : F ⟶ G) (θ : H ⟶ I) (X Y : C) (f : X ⟶ Y) :
  (η ◫ θ).app X ≫ (I ⋙ G).map f = (H ⋙ F).map f ≫ (η ◫ θ).app Y := by
  naturality!
```

### 3. Algebra Objects

```lean
-- Monoid object associativity
example {C : Type} [MonoidalCategory C] (A : MonoidObject C) (X Y Z : C) :
  (A.μ.app (X ⊗ Y)) ≫ A.μ.app Z = A.μ.app X ≫ (A.μ.app (Y ⊗ Z)) := by
  naturality!
```

### 4. Monoidal Functors

```lean
-- Monoidal functor compatibility
example {C D : Type} [MonoidalCategory C] [MonoidalCategory D] 
  (F : MonoidalFunctor C D) (X Y : C) :
  F.map (X ⊗ Y) ≫ F.μ.app (X, Y) = F.μ.app (X, Y) ≫ (F.map X ⊗ F.map Y) := by
  naturality!
```

### 5. Adjunction Unit/Counit Naturality

```lean
-- Adjunction unit naturality
example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (G : D ⥤ C) 
  (adj : F ⊣ G) (X Y : C) (f : X ⟶ Y) :
  adj.unit.app X ≫ G.map (F.map f) = f ≫ adj.unit.app Y := by
  naturality!
```

## Configuration Options

### Yo Direction

```lean
-- Set direction explicitly
yo.direction := covariant    -- Force covariant Yoneda
yo.direction := contravariant -- Force contravariant Coyoneda  
yo.direction := auto         -- Let the tactic decide (default)
```

### Naturality Settings

```lean
-- Increase max steps for complex proofs
naturality.maxSteps := 128

-- Set timeout for long-running proofs
naturality.timeout := 3000ms
```

## Debug Mode

Use `yo?` and `naturality?` to see exactly what rewrites are applied:

```lean
example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X : C) :
  F.map (𝟙 X) = 𝟙 (F.obj X) := by
  yo?  -- Shows: "Applied smart simp", "Applied Yoneda isomorphism"
```

## Common Pitfalls

### 1. Over-rewriting

**Problem**: Tactics apply too many rewrites, making goals more complex.

**Solution**: Use debug mode to see what's happening, then apply more specific tactics.

```lean
-- Instead of just:
naturality!

-- Try:
naturality!
simp only [some_specific_lemma]
```

### 2. Infinite Loops

**Problem**: Tactics get stuck in rewrite loops.

**Solution**: Set explicit direction or use timeout:

```lean
yo.direction := covariant  -- Prevents co/contra flip-flops
naturality.timeout := 1000ms  -- Prevents infinite loops
```

### 3. Wrong Tactic Choice

**Problem**: Using `yo` when you need `naturality!` or vice versa.

**Solution**: Follow the decision tree above, or try both:

```lean
-- If unsure, try both:
naturality!
-- If that fails:
yo
```

## Performance tips

Tactics use bounded search (`naturality.maxSteps`, `naturality.timeout`). Tune these for large goals; measure impact in your own project rather than relying on repository-wide latency guarantees.

### 1. Use specific lemmas

Instead of relying on automatic detection, use specific lemmas when possible:

```lean
-- More efficient:
simp only [Functor.map_comp]

-- Less efficient:
yo
```

### 2. Combine with other tactics

```lean
-- Efficient combination:
naturality!
simp only [whiskerLeft_app]
```

### 3. Set appropriate limits

For large diagrams, adjust limits:

```lean
naturality.maxSteps := 256  -- For very large diagrams
naturality.timeout := 5000ms  -- For complex proofs
```

## Troubleshooting

### Tactic Fails

1. **Check goal structure**: Ensure the goal matches expected patterns
2. **Use debug mode**: See what the tactic is trying to do
3. **Try manual approach**: Break down into smaller steps
4. **Check attributes**: Ensure required lemmas are registered with `@[naturality]` or `@[yo.fuse]`

### Performance issues

1. **Reduce max steps**: Lower `naturality.maxSteps`
2. **Set timeout**: Use `naturality.timeout`
3. **Use explicit direction**: Set `yo.direction`
4. **Profile locally**: Use [`measurePerformance`](API_REFERENCE.md#performance-measurement) or telemetry helpers in your own project

### Build failures

1. **Check imports**: Ensure required modules are imported (`import LeanYo`, Mathlib category theory as needed)
2. **Sync toolchain**: Match the Lean version in [`lean-toolchain`](../lean-toolchain) and run `lake update`
3. **Rebuild the project**: from the repository root run `make test`, or `lake update` followed by `lake build` if you only need a compile check

## Best practices

1. **Start simple**: Use basic tactics first, then add complexity
2. **Use debug mode**: When tactics fail, use `yo?` / `naturality?` to see rewrites
3. **Set limits**: Use timeouts and step limits on heavy goals
4. **Register lemmas**: Use `@[naturality]` and `@[yo.fuse]` for lemmas the automation should see
5. **Profile when needed**: Use telemetry / `measurePerformance` locally for hot paths
6. **Document patterns**: Share successful proof patterns (issues, Zulip, or PRs to examples)
