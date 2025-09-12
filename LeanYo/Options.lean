import Lean

namespace LeanYo

-- Direction for Yoneda isomorphisms
inductive YoDirection where
  | covariant
  | contravariant
  | auto

instance : ToString YoDirection where
  toString := fun
    | .covariant => "covariant"
    | .contravariant => "contravariant"
    | .auto => "auto"

-- Options for the yo tactic
structure YoOptions where
  direction : YoDirection := YoDirection.auto

-- Options for the naturality! tactic
structure NaturalityOptions where
  maxSteps : Nat := 64
  timeout : Nat := 1500 -- milliseconds

-- Global options state
structure Options where
  yo : YoOptions := {}
  naturality : NaturalityOptions := {}

-- Default options instances
instance : Inhabited YoOptions := ⟨{}⟩
instance : Inhabited NaturalityOptions := ⟨{}⟩
instance : Inhabited Options := ⟨{}⟩

-- Option accessors
def getYoDirection (opts : Options) : YoDirection := opts.yo.direction
def getNaturalityMaxSteps (opts : Options) : Nat := opts.naturality.maxSteps
def getNaturalityTimeout (opts : Options) : Nat := opts.naturality.timeout

-- Option setters
def setYoDirection (opts : Options) (dir : YoDirection) : Options :=
  { opts with yo := { opts.yo with direction := dir } }

def setNaturalityMaxSteps (opts : Options) (steps : Nat) : Options :=
  { opts with naturality := { opts.naturality with maxSteps := steps } }

def setNaturalityTimeout (opts : Options) (timeout : Nat) : Options :=
  { opts with naturality := { opts.naturality with timeout := timeout } }

end LeanYo
