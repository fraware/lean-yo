# Lean-Yo API Reference

## Tactics

### `yo`

**Purpose**: Transforms morphism goals into pointwise goals via (co)Yoneda isomorphisms.

**Syntax**:
- `by yo` - Rewrite the main goal
- `yo at h` - Rewrite hypothesis `h`

**Use Cases**:
- Functoriality proofs (`F.map (𝟙 X) = 𝟙 (F.obj X)`)
- Composition proofs (`F.map (f ≫ g) = F.map f ≫ F.map g`)
- Yoneda reductions
- General morphism equalities

**Example**:
```lean
example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X : C) :
  F.map (𝟙 X) = 𝟙 (F.obj X) := by
  yo
```

### `yo?`

**Purpose**: Debug version of `yo` that prints the exact rewrites used.

**Syntax**: `by yo?`

**Output**: Logs the sequence of rewrites applied to the goal.

**Example**:
```lean
example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X : C) :
  F.map (𝟙 X) = 𝟙 (F.obj X) := by
  yo?  -- Shows: "Applied smart simp", "Applied Yoneda isomorphism"
```

### `naturality!`

**Purpose**: Closes standard naturality squares and whiskering equations.

**Syntax**: `by naturality!`

**Use Cases**:
- Naturality squares (`η.app X ≫ G.map f = F.map f ≫ η.app Y`)
- Whiskering equations
- Coherence conditions
- Composition of natural transformations

**Example**:
```lean
example {C D : Type} [Category C] [Category D] (F G : C ⥤ D) (η : F ⟶ G) (X Y : C) (f : X ⟶ Y) :
  η.app X ≫ G.map f = F.map f ≫ η.app Y := by
  naturality!
```

### `naturality?`

**Purpose**: Debug version of `naturality!` that prints the exact rewrites used.

**Syntax**: `by naturality?`

**Output**: Logs the sequence of rewrites applied to solve the naturality square.

**Example**:
```lean
example {C D : Type} [Category C] [Category D] (F G : C ⥤ D) (η : F ⟶ G) (X Y : C) (f : X ⟶ Y) :
  η.app X ≫ G.map f = F.map f ≫ η.app Y := by
  naturality?  -- Shows: "Applied naturality simp", "Applied naturality square rewrite"
```

## Attributes

### `@[naturality]`

**Purpose**: Register natural transformation naturality lemmas for use by `naturality!` tactic.

**Usage**: Apply to theorems that express naturality conditions.

**Example**:
```lean
@[naturality]
theorem my_naturality_lemma {C D : Type} [Category C] [Category D] 
  (F G : C ⥤ D) (η : F ⟶ G) (X Y : C) (f : X ⟶ Y) :
  η.app X ≫ G.map f = F.map f ≫ η.app Y := by
  naturality!
```

**Validation**: The attribute validates that the lemma is about naturality patterns.

### `@[yo.fuse]`

**Purpose**: Register lemmas that fuse map_comp, whisker laws, and functoriality for use by `yo` tactic.

**Usage**: Apply to theorems that express fusion rules for category theory operations.

**Example**:
```lean
@[yo.fuse]
theorem my_fusion_lemma {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z) :
  F.map (f ≫ g) = F.map f ≫ F.map g := by
  rfl
```

**Validation**: The attribute validates that the lemma is about fusion patterns.

## Options

### `yo.direction`

**Purpose**: Control the direction of Yoneda isomorphisms.

**Type**: `YoDirection`

**Values**:
- `covariant` - Force covariant Yoneda isomorphism
- `contravariant` - Force contravariant Coyoneda isomorphism  
- `auto` - Let the tactic decide automatically (default)

**Usage**:
```lean
yo.direction := covariant
```

### `naturality.maxSteps`

**Purpose**: Set the maximum number of rewrite steps for `naturality!` tactic.

**Type**: `Nat`

**Default**: `64`

**Usage**:
```lean
naturality.maxSteps := 128
```

### `naturality.timeout`

**Purpose**: Set the timeout for `naturality!` tactic execution.

**Type**: `Nat` (milliseconds)

**Default**: `1500`

**Usage**:
```lean
naturality.timeout := 3000ms
```

## Configuration Functions

### `setYoDirection`

**Purpose**: Update the yo direction setting programmatically.

**Signature**: `setYoDirection (dir : YoDirection) : IO Unit`

**Example**:
```lean
setYoDirection YoDirection.covariant
```

### `setNaturalityMaxSteps`

**Purpose**: Update the naturality max steps setting programmatically.

**Signature**: `setNaturalityMaxSteps (steps : Nat) : IO Unit`

**Example**:
```lean
setNaturalityMaxSteps 128
```

### `setNaturalityTimeout`

**Purpose**: Update the naturality timeout setting programmatically.

**Signature**: `setNaturalityTimeout (timeout : Nat) : IO Unit`

**Example**:
```lean
setNaturalityTimeout 3000
```

## Telemetry Functions

### `getTelemetry`

**Purpose**: Retrieve current telemetry data.

**Signature**: `getTelemetry : IO TelemetryData`

**Returns**: `TelemetryData` containing:
- `tacticInvocations : Nat` - Total number of tactic calls
- `totalTime : Nat` - Total execution time in milliseconds
- `totalRewrites : Nat` - Total number of rewrites applied
- `failureCount : Nat` - Number of failed tactic calls
- `failureReasons : List String` - List of failure reasons

**Example**:
```lean
let metrics ← getTelemetry
IO.println s!"Total yo calls: {metrics.tacticInvocations}"
```

### `resetTelemetry`

**Purpose**: Reset telemetry data to initial state.

**Signature**: `resetTelemetry : IO Unit`

**Example**:
```lean
resetTelemetry
```

## Helper Functions

### `isNaturalityLemma`

**Purpose**: Check if a lemma is registered with the naturality attribute.

**Signature**: `isNaturalityLemma (env : Environment) (name : Name) : Bool`

**Example**:
```lean
let env ← getEnv
let isNaturality := isNaturalityLemma env `my_naturality_lemma
```

### `isYoFuseLemma`

**Purpose**: Check if a lemma is registered with the yo.fuse attribute.

**Signature**: `isYoFuseLemma (env : Environment) (name : Name) : Bool`

**Example**:
```lean
let env ← getEnv
let isFuse := isYoFuseLemma env `my_fusion_lemma
```

### `getNaturalityLemmas`

**Purpose**: Get all lemmas registered with the naturality attribute.

**Signature**: `getNaturalityLemmas (env : Environment) : Array Name`

**Example**:
```lean
let env ← getEnv
let naturalityLemmas := getNaturalityLemmas env
```

### `getYoFuseLemmas`

**Purpose**: Get all lemmas registered with the yo.fuse attribute.

**Signature**: `getYoFuseLemmas (env : Environment) : Array Name`

**Example**:
```lean
let env ← getEnv
let fuseLemmas := getYoFuseLemmas env
```

## Performance Measurement

### `measurePerformance`

**Purpose**: Measure the performance of a tactic execution.

**Signature**: `measurePerformance [Monad m] [MonadLiftT IO m] (tacticName : String) (action : m α) : m (α × PerformanceMetrics)`

**Returns**: A tuple of the action result and performance metrics.

**Metrics Include**:
- `tacticName : String` - Name of the tactic
- `startTime : Nat` - Start time in milliseconds
- `endTime : Nat` - End time in milliseconds  
- `rewriteCount : Nat` - Number of rewrites applied
- `success : Bool` - Whether the tactic succeeded
- `failureReason : Option String` - Reason for failure if applicable

**Example**:
```lean
let (result, metrics) ← measurePerformance "yo" do
  yoTactic goal
IO.println s!"yo tactic took {metrics.endTime - metrics.startTime}ms"
```

## Error Handling

All tactics include comprehensive error handling:

- **Timeout errors**: When tactics exceed their timeout limits
- **Step limit errors**: When tactics exceed their maximum step count
- **Pattern matching errors**: When goals don't match expected patterns
- **Validation errors**: When attributes are applied to invalid declarations

Error messages are designed to be informative and help users understand what went wrong and how to fix it.
