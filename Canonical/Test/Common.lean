import Lean
import Canonical

open Lean Meta

/-- The head symbols in `e` that `e` does not bind. -/
partial def freeHeads (e : Canonical.Expr) (bound : Std.HashSet String := {}) : Std.HashSet String :=
  let bound := (e.params ++ e.lets).foldl (·.insert ·.name) bound
  let heads : Std.HashSet String := if bound.contains e.spine.head then {} else {e.spine.head}
  e.spine.args.foldl (fun heads arg => (freeHeads arg bound).fold (·.insert ·) heads) heads

/-- If `witness`, a proof of `type`, is given, also prints (when `verbose`) its translation into the problem. -/
def canonicalSimple (type : Expr) (names : NameSet) (verbose := false) (witness : Option Expr := none) :
    MetaM (Array Expr) := do
  IO.setNumHeartbeats 0
  tryCatchRuntimeEx (handler := fun e => do IO.throwServerError (← e.toMessageData.toString); pure #[]) do
    let premises := names.toArray
    let env ← getEnv
    let structs ← premises.filterMapM Destruct.getStruct
    let structs := structs ++ (premises.filter (isStructure env))
    let premises ← premises.filterM fun name => do pure (← Destruct.getStruct name).isNone
    let config := { }
    let goal ← mkFreshExprMVar type
    let (goal', reconstruct, forward) ← Canonical.withArityUnfold config.monomorphize do
      Canonical.preprocess goal.mvarId! config structs
    let witness ← witness.mapM forward
    let (decl, witness) ← Canonical.withArityUnfold config.monomorphize do goal'.withContext do
      Canonical.toCanonical "proof" (← goal'.getType) premises (structs.push ``Canonical.Pi) config witness
    if verbose then
      IO.println s!"\n{decl.type.get!}\n"
      if let some witness := witness then
        IO.println s!"Witness:\n{witness}\n"
        let problem := decl.type.get!
        let declared := (problem.params ++ problem.lets).map (·.name)
        IO.println s!"Undeclared in the problem: {(freeHeads witness).toList.filter (!declared.contains ·)}\n"
    let result ← Canonical.runCanonical decl 1 config
    Canonical.postprocess result goal' config reconstruct

/-- Quote `s` for the shell if it contains anything beyond a conservative set of safe characters. -/
def shellQuote (s : String) : String :=
  if !s.isEmpty && s.all (fun (c : Char) => c.isAlphanum || "._/-".contains c) then s
  else "'" ++ s.replace "'" "'\\''" ++ "'"

/-- Parse a name as printed by `Name.toString`, handling `«»` escapes and numeric components. -/
def parseName (s : String) : Name := Id.run do
  let mut n := Name.anonymous
  let mut cur := ""
  let mut escaped := false
  let push (n : Name) (c : String) (wasEscaped : Bool) : Name :=
    if !wasEscaped && !c.isEmpty && c.all Char.isDigit then .num n c.toNat! else .str n c
  let mut wasEscaped := false
  for c in s.toList do
    if escaped then
      if c == '»' then escaped := false else cur := cur.push c
    else if c == '«' then
      escaped := true; wasEscaped := true
    else if c == '.' then
      n := push n cur wasEscaped; cur := ""; wasEscaped := false
    else
      cur := cur.push c
  return push n cur wasEscaped

/-- Import `Canonical` together with `extra` and run `x`. -/
unsafe def runMetaWith (extra : Array Name) (x : MetaM α) : IO α := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let imports := (#[`Canonical] ++ extra).map ({ module := · })
  let env ← importModules imports {} (loadExts := true)
  let ctx : Core.Context := { fileName := "<canonical-test>", fileMap := default, maxHeartbeats := 100000 }
  (·.1) <$> x.toIO ctx { env }
