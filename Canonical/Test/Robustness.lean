import Lean
import Canonical.Test.Common

open Lean Meta SubExpr

structure Failure where
  pos: Pos
  premises: NameSet

instance : ToString Failure where
  toString f := s!"⟨{f.pos}, {f.premises.toArray}⟩"

structure Accumulate where
  failures: Array Failure := #[]
  total: Nat := 0
  success: Nat := 0
  premises: NameSet

instance : ToString Accumulate where
  toString a := s!"⟨{a.failures}, {a.total}, {a.success}, {a.premises.toArray}⟩"

instance : Add Accumulate where
  add x y := {
    failures := x.failures ++ y.failures
    total := x.total + y.total
    success := x.success + y.success
    premises := x.premises.append y.premises
  }

abbrev TraverseM := StateT Accumulate MetaM

def test (pos : Pos) (type : Expr) (premises : NameSet) : MetaM (Except Failure NameSet) := do
  try
    let proofs ← canonicalSimple type premises
    if proofs.isEmpty then
      return .error { pos, premises }
    else
      return .ok premises -- TODO
  catch _ => return .error { pos, premises }

/-- The command that reproduces `failure` of `const`, parsed by `lake exe debug`. -/
def debugCommand (const : Name) (failure : Failure) : String :=
  let args := #[toString const, toString failure.pos] ++ failure.premises.toArray.map toString
  args.foldl (fun acc x => s!"{acc} {shellQuote x}") "lake exe debug"

partial def traverse (const : Name) (e : Expr) (f : Pos → Expr → NameSet → MetaM (Except Failure NameSet)) (p : Pos := .root) : MetaM Accumulate := do
  if ← isProof e then
    let start := { premises := NameSet.ofArray e.constName?.toArray }
    let (_, children) ← traverseChildrenWithPos (M := TraverseM) (fun p c => do
      let child ← traverse const c f p
      modify (· + child)
      pure c
    ) p e start

    if !e.isLambda then
      let children := { children with total := children.total + 1 }
      if children.failures.isEmpty then
        match ← f p (← inferType e) children.premises with
        | .ok premises => return { children with success := children.success + 1, premises }
        | .error failure =>
          IO.println (debugCommand const failure)
          (← IO.getStdout).flush
          return { children with failures := children.failures.push failure }
    return children
  else return { premises := {} }

def findFailures (const : Name) : MetaM Accumulate := do
  let value := (← getConstInfo const).value! (allowOpaque := true)
  traverse const value test .root

/-- Theorems defined in modules whose name has one of `roots` as a prefix. -/
def sweepTargets (roots : Array Name) : MetaM (Array Name) := do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc name info =>
    if !info.isTheorem || name.isInternalDetail then acc else
    match env.getModuleIdxFor? name with
    | some idx =>
      let mod := env.header.moduleNames[idx.toNat]!
      if roots.any (·.isPrefixOf mod) then acc.push name else acc
    | none => acc
  return names.qsort (·.cmp · == .lt)

/-- `lake exe robustness [module prefix...]` (default: `Init Std`). -/
unsafe def main (args : List String) : IO UInt32 := do
  let roots := if args.isEmpty then #[`Init, `Std] else args.toArray.map parseName
  runMetaWith #[`Std] do
    let targets ← sweepTargets roots
    let stderr ← IO.getStderr
    stderr.putStrLn s!"Sweeping {targets.size} theorems from {roots}"
    let mut total := 0
    let mut success := 0
    let mut failures := 0
    let mut errors := 0
    let mut i := 0
    for const in targets do
      i := i + 1
      try
        let acc ← findFailures const
        total := total + acc.total
        success := success + acc.success
        failures := failures + acc.failures.size
        stderr.putStrLn s!"[{i}/{targets.size}] {const}: {acc.success}/{acc.total}"
      catch e =>
        errors := errors + 1
        stderr.putStrLn s!"[{i}/{targets.size}] {const}: error: {← e.toMessageData.toString}"
    stderr.putStrLn s!"Done: {success}/{total} subterms succeeded, {failures} failures, {errors} theorems errored"
  return 0
