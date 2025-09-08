import Canonical.Destruct
import Canonical.TranslationUtil
import Lean

open Lean

namespace Canonical

def preprocess (goal : MVarId) (config : CanonicalConfig) (structs : Array Name) : MetaM (MVarId × (Expr → MetaM Expr)) := do
  if config.destruct then
    if let some destruct ← Destruct.destructCanonical goal structs then
      return destruct
  return (goal, fun x => pure x)

end Canonical
