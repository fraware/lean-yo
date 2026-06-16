import Lean
import LeanYo.Core.Options

namespace LeanYo

initialize globalOptionsRef : IO.Ref Options ← IO.mkRef {}

def getOptions : IO Options := globalOptionsRef.get

def setOptions (opts : Options) : IO Unit := globalOptionsRef.set opts

def setYoDirectionIO (dir : YoDirection) : IO Unit := do
  let opts ← getOptions
  setOptions (setYoDirection opts dir)

def setNaturalityMaxStepsIO (steps : Nat) : IO Unit := do
  let opts ← getOptions
  setOptions (setNaturalityMaxSteps opts steps)

def setNaturalityTimeoutIO (timeout : Nat) : IO Unit := do
  let opts ← getOptions
  setOptions (setNaturalityTimeout opts timeout)

end LeanYo
