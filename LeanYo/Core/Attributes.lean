import Lean
import LeanYo.Core.Options

namespace LeanYo

initialize naturalityExt : Lean.LabelExtension ←
  Lean.registerLabelAttr `naturality
    "Register natural transformation naturality lemmas for use by naturality! tactic"

initialize yoFuseExt : Lean.LabelExtension ←
  Lean.registerLabelAttr `yo.fuse
    "Register lemmas that fuse map_comp, whisker laws, and functoriality for use by yo tactic"

def getNaturalityLemmas (env : Lean.Environment) : Array Lean.Name :=
  naturalityExt.getState env

def getYoFuseLemmas (env : Lean.Environment) : Array Lean.Name :=
  yoFuseExt.getState env

def isNaturalityLemma (env : Lean.Environment) (name : Lean.Name) : Bool :=
  naturalityExt.getState env |>.contains name

def isYoFuseLemma (env : Lean.Environment) (name : Lean.Name) : Bool :=
  yoFuseExt.getState env |>.contains name

end LeanYo
