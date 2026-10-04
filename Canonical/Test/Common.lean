import Lean
import Canonical

open Lean Meta

def canonicalSimple (type : Expr) (names : NameSet) (verbose := false) : MetaM (Array Expr) := do
  IO.setNumHeartbeats 0
  tryCatchRuntimeEx (handler := fun e => do IO.throwServerError (← e.toMessageData.toString); pure #[]) do
    let premises := names.toArray
    let env ← getEnv
    let structs ← premises.filterMapM Destruct.getStruct
    let structs := structs ++ (premises.filter (isStructure env))
    let premises ← premises.filterM fun name => do pure (← Destruct.getStruct name).isNone
    let config := { }
    let goal ← mkFreshExprMVar type
    let (goal', reconstruct) ← Canonical.withArityUnfold config.monomorphize do
      Canonical.preprocess goal.mvarId! config structs
    let decl ← Canonical.withArityUnfold config.monomorphize do goal'.withContext do
      Canonical.toCanonical "proof" (← goal'.getType) premises (structs.push ``Canonical.Pi) config
    if verbose then
      IO.println s!"\n{decl.type}\n"
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
  let ctx : Core.Context := { fileName := "<canonical-test>", fileMap := default, maxHeartbeats := 0 }
  (·.1) <$> x.toIO ctx { env }
