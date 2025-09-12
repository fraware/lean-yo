import Lean
import LeanYo.Options

namespace LeanYo

-- Attribute for registering natural transformation naturality lemmas
initialize naturalityAttr : AttributeImpl where
  name := `naturality
  descr := "Register natural transformation naturality lemmas for use by naturality! tactic"
  add decl := do
    -- Validation: check that the lemma is about naturality
    let env ← getEnv
    let declInfo := env.getDecl decl
    match declInfo with
    | .thmInfo thmInfo =>
      -- Basic validation that this looks like a naturality lemma
      let type := thmInfo.type
      -- TODO: Add more sophisticated validation
      pure ()
    | _ => throwError "naturality attribute can only be applied to theorems"

-- Attribute for registering lemmas that fuse map_comp, whisker laws, functoriality
initialize yoFuseAttr : AttributeImpl where
  name := `yo.fuse
  descr := "Register lemmas that fuse map_comp, whisker laws, and functoriality for use by yo tactic"
  add decl := do
    -- Validation: check that the lemma is about functoriality/whiskering
    let env ← getEnv
    let declInfo := env.getDecl decl
    match declInfo with
    | .thmInfo thmInfo =>
      -- Basic validation that this looks like a fusion lemma
      let type := thmInfo.type
      -- TODO: Add more sophisticated validation
      pure ()
    | _ => throwError "yo.fuse attribute can only be applied to theorems"

-- Helper functions to query registered lemmas
def getNaturalityLemmas (env : Environment) : Array Name :=
  env.getDeclsOfAttribute `naturality

def getYoFuseLemmas (env : Environment) : Array Name :=
  env.getDeclsOfAttribute `yo.fuse

-- Check if a lemma is registered with naturality attribute
def isNaturalityLemma (env : Environment) (name : Name) : Bool :=
  env.getDeclsOfAttribute `naturality |>.contains name

-- Check if a lemma is registered with yo.fuse attribute
def isYoFuseLemma (env : Environment) (name : Name) : Bool :=
  env.getDeclsOfAttribute `yo.fuse |>.contains name

end LeanYo
