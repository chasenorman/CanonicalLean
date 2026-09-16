module

public import Lean.Expr
public import Lean.Meta.Basic
public import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.TryThis

open Lean Meta Expr Elab Tactic Term

public section

namespace Canonical2

structure CancelableTask (α : Type) where
  task : Task α
  cancelPost : IO Unit := pure ()

def CancelableTask.cancel {α : Type} (t : CancelableTask α) : IO Unit := do
  IO.cancel t.task
  t.cancelPost

def CancelableTask.map {α β} (f : α → β) (x : CancelableTask α) : CancelableTask β :=
  let mapped := x.task.map (sync := true) f
  ⟨mapped, do x.cancel; if !(← IO.hasFinished mapped) then IO.cancel mapped⟩

def CancelableTask.race {α} [Nonempty α] (tasks : List (CancelableTask (Except IO.Error α))) : IO (CancelableTask (Except IO.Error α)) := do
  let cancelPost := tasks.forM fun x => do
    if !(← IO.hasFinished x.task) then x.cancel
  return { cancelPost, task := ← IO.asTask do
    let mut tasks := tasks
    while h : 0 < tasks.length do
      let (i, a) ← IO.waitAny
        (tasks.mapIdx fun i t => t.task.map (sync := true) fun a => (i, a))
        (by rwa [List.length_mapIdx])
      tasks := tasks.eraseIdx i
      if let .ok a := a then cancelPost; return a
    throw (IO.userError "All tasks failed.")
  }

abbrev MetaTask α := CancelableTask (Except IO.Error (α × Core.State × Meta.State))

def MetaTask.map (f : α → β) (task : MetaTask α) : MetaTask β :=
  CancelableTask.map (·.map fun (a, state) => (f a, state)) task

end Canonical2

namespace Lean

def Meta.MetaM.toTask (x : MetaM α) (cancel : IO Unit := pure ()) : MetaM (Canonical2.MetaTask α) :=
  fun metaCtx metaState coreCtx coreState => do
    return ⟨← IO.asTask do MetaM.toIO x coreCtx (← coreState.get) metaCtx (← metaState.get), cancel⟩

def MVarId.clone (mvarId : MVarId) : MetaM MVarId := do
  return (← mvarId.withContext do mkFreshExprMVar (← mvarId.getType)).mvarId!

def MVarId.run (mvar : MVarId) (f : TacticM α) : MetaM α := TermElabM.run' do
  (f { elaborator := .anonymous }).run' { goals := [mvar] }

end Lean

namespace Canonical2

/-- Excludes binder types. -/
partial def explicitConstants : Expr → MetaM (NameSet)
| .const name _ => do return { name }
| .app fn arg => do
  if (← whnf (← inferType fn)).binderInfo.isExplicit then
    return (← explicitConstants fn) ++ (← explicitConstants arg)
  else explicitConstants fn
| .lam name type body info => do
  withLocalDecl name info type fun x => do explicitConstants (body.instantiate1 x)
| .letE name type value body _nondep => do
  let forValue ← explicitConstants value
  withLetDecl name type value fun x => do
    return forValue ++ (← explicitConstants (body.instantiate1 x))
| .mdata _ e => explicitConstants e
| .proj typeName idx e => do
  return (← explicitConstants e).insertMany ((getStructureInfo (← getEnv) typeName).getProjFn? idx).toArray
| _ => return {}

def collectConstants (s : Syntax) (goal : MVarId) : MetaM NameSet := goal.withContext do
  match s with
  | .ident _ _ _ _ => do return NameSet.ofArray (← realizeGlobalConst s).head?.toArray
  | .node _ k args => do
    if (`Lean.Parser.Term).isPrefixOf k then try
        let e ← TermElabM.run' (ctx := { errToSorry := false }) do elabTerm s none
        withTransparency .all do explicitConstants e
      catch _ => return {}
    else
      args.foldlM (init := {}) fun acc arg => do pure (acc ++ (← collectConstants arg goal))
  | _ => return {}

def roundtrip (opts : Options) : Options := opts |>
  (pp.proofs.set · false) |> (pp.analyze.trustSubtypeMk.set · false) |>
  (pp.analyze.set · true) |> (pp.analyze.trustOfScientific.set · false) |>
  (pp.analyze.trustOfNat.set · false) |> (pp.motives.all.set · true) |>
  (pp.coercions.types.set · true) |> (pp.unicode.fun.set · true) |>
  (pp.funBinderTypes.set · true) |> (pp.piBinderNames.set · true) |>
  (pp.notation.set · false) |> (pp.fullNames.set · true)

def elabStringAsExpr (str : String) (type : Option Expr := none) : MetaM Expr := do
  let stx ← IO.ofExcept (Parser.runParserCategory (← getEnv) `term str)
  TermElabM.run' do withoutErrToSorry do elabTermAndSynthesize stx type

private def homeDir : IO System.FilePath := do
  let h := (← IO.getEnv "HOME").getD ""
  if !h.isEmpty then return ⟨h⟩
  match ← IO.getEnv "USERPROFILE" with
  | some h => return ⟨h⟩
  | none   => throw <| IO.userError "HOME is not set"

def cacheDir : IO System.FilePath := do
  if System.Platform.isWindows then
    match ← IO.getEnv "LOCALAPPDATA" with
    | some d => return (d : System.FilePath) / "Canonical"
    | none   => throw <| IO.userError "LOCALAPPDATA is not set"
  else if System.Platform.isOSX then
    return (← homeDir) / "Library" / "Caches" / "Canonical"
  else
    return (← homeDir) / ".cache" / "Canonical"
