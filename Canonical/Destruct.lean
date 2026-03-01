import Lean
import Canonical.Util

open Lean Meta Expr Elab Tactic Core

namespace Destruct

/-- The default structures that are unpacked by `destruct`. -/
def STRUCTURES := #[``Prod, ``PProd, ``And, ``Sigma, ``PSigma, ``Iff, ``MProd, ``Subtype, ``Fin, ``Array]

/-def False.intro (elim : (C : Prop) → C) : False := elim False

def Empty.intro (elim : (C : Type) → C) : Empty := elim Empty

def PEmpty.intro (elim : (C : Sort u) → C) : PEmpty := elim PEmpty-/

abbrev DestructM := ReaderT NameSet MetaM

/-- Use `isDefEq` to apply `e` to const `name` at index `i`. -/
def applyAtIndex (name : Name) (i : Nat) (e : Expr) : MetaM Expr := do
  let info ← getConstInfo name
  let levels ← info.levelParams.mapM (fun _ => mkFreshLevelMVar)
  let type := info.type.instantiateLevelParams info.levelParams levels
  let mvars := (← forallMetaTelescopeReducing type).1
  let result := mkAppN (.const name levels) mvars
  let success ← isDefEq mvars[i]! e
  assert! success
  return ← instantiateMVars result

/-- Add `pre` to the names of the first `n` lambdas in `e`. -/
def addPrefix (e : Expr) (pre : Name) (n : Nat) : Expr :=
  match n with
  | 0 => e
  | n + 1 => match e with
    | .lam name type body info =>
      .lam (pre.getRoot.toString ++ "_" ++ name.toString).toName type (addPrefix body pre n) info
    | _ => panic! s!"addPrefix: expected a lambda, got {e}"

/-- If `e` is a structure, returns the fields `e` and
    a lambda that takes the fields and reconstructs the structure. -/
def separateHead (e : Expr) (typ : Expr) : DestructM (Option (Expr × Array Expr)) := do
  let args := getAppArgs typ
  let fn := getAppFn typ
  let name := fn.constName?.getD .anonymous
  if (← read).contains name then
    let info := (Lean.getStructureInfo? (← getEnv) name).get!
    let mut fields := #[]
    for i in [0:info.fieldNames.size] do
      fields := fields.push (.proj name i e)
    let induct ← getConstInfoInduct name
    return some (← etaExpand (mkAppN (.const induct.ctors[0]! fn.constLevels!) args), fields)
  else if name == ``Exists then -- skolemize
    let fields := #[← applyAtIndex ``Exists.choose 2 e, ← applyAtIndex ``Exists.choose_spec 2 e]
    return some (← etaExpand (mkAppN (.const ``Exists.intro fn.constLevels!) args), fields)
  else if name == ``Unit then
    return some (.const ``Unit.unit [], #[])
  else if name == ``PUnit then
    return some (.const ``PUnit.unit fn.constLevels!, #[])
  else if name == ``True then
    return some (.const ``True.intro [], #[])
  /-else if name == ``False then
    let false_intro := ((← getEnv).find? ``False.intro).get!.value!
    let false_elim ← applyAtIndex ``False.elim 1 e (levels := pure Level.zero)
    return some (false_intro, #[(← abstractMVars false_elim).expr])
  else if name == ``Empty then
    let empty_intro := ((← getEnv).find? ``Empty.intro).get!.value!
    let empty_elim ← applyAtIndex ``Empty.elim 1 e (levels := pure (Level.succ Level.zero))
    return some (empty_intro, #[(← abstractMVars empty_elim).expr])
  else if name == ``PEmpty then
    let level := fn.constLevels![0]!
    let pempty_intro := ((← getEnv).find? ``PEmpty.intro).get!
    let pempty_elim ← applyAtIndex ``PEmpty.elim 1 e (levels := pure level)
    return some (pempty_intro.value!.instantiateLevelParams pempty_intro.levelParams [level, level],
      #[(← abstractMVars pempty_elim).expr])-/
  else return none

def constructApp (separations : List (Expr × Array Expr)) (reconstruct : Expr) (fvars : Array Expr) (fields : Array Expr := #[]) : MetaM Expr := do
  match separations with
  | [] => return Canonical.apply reconstruct fields.toList
  | (construct, destruct) :: rest => do
    lambdaBoundedTelescope (construct.replaceFVars (fvars.take fields.size) fields) destruct.size fun xs construct => do
      return ← mkLambdaFVars xs (← constructApp rest reconstruct fvars (fields.push construct))

def destructApp (e : Expr) (field : Expr) (fvar : Expr) : MetaM Expr := do
  match e with
  | .lam _name _type body _info =>
    return ← mkLambdaFVars #[fvar] (body.instantiate1 field)
  | _ => throwError "destructApp: expected a lambda, got {e}"

def constructPi (e : Expr) (xs : Array Expr) (n : Nat) (xs' : Array Expr) (replacements : Array Expr) (separations : Array (Expr × Array Expr)) : MetaM Expr := do
  match n, e with
  | 0, _ => return ← mkLambdaFVars xs (e.replaceFVars xs' replacements)
  | n + 1, .lam name type body info =>
    withLocalDecl name info (← mkForallFVars xs' (type.replaceFVars xs (separations.map (·.1)))) fun fvar => do
      return ← mkLambdaFVars #[fvar] (← constructPi (body.instantiate1 (mkAppN fvar replacements)) xs n xs' replacements separations)
  | _, _ => throwError "constructPi: expected a lambda, got {e}"

def destructPi (e : Expr) (xs : Array Expr) (xs' : Array Expr) (separations : Array (Expr × Array Expr)) : MetaM Expr := do
  match e with
  | .lam name type body info =>
    withLocalDecl name info (← mkForallFVars xs type) fun fvar => do
      return ← mkLambdaFVars (#[fvar] ++ xs') ((body.instantiate1 (mkAppN fvar xs)).replaceFVars xs (separations.map (·.1)))
  | _ => throwError "destructPi: expected a lambda, got {e}"

mutual
  partial def forallTelescopeReducingSeparate (e : Expr) (e' : Expr := e) (k : Array Expr → Expr → Array Expr → Array (Bool × Expr × Array Expr) → Expr → DestructM α)
    (xs : Array Expr := #[]) (xs' : Array Expr := #[]) (separations : Array (Bool × Expr × Array Expr) := #[]) : DestructM α := do
    match ← whnf e, ← whnf e' with
    | .forallE name type body info, forallE name' type' body' info' =>
      withLocalDecl name info type fun fvar => do
        let separate := (← separatePi type' name' info').1
        let (construct, destruct) := separate.getD (Canonical.identity name' type', #[Canonical.identity name' type'])
        lambdaBoundedTelescope construct destruct.size fun fvars construct => do
          forallTelescopeReducingSeparate (body.instantiate1 fvar) (body'.instantiate1 construct) k (xs.push fvar) (xs' ++ fvars) (separations.push (separate.isSome, construct, destruct))
    | _, _ => k xs e xs' separations e'

  partial def separateApp (e : Expr) (name : Name) (binfo : BinderInfo) : DestructM (Option (Expr × Array Expr)) := do
    withLocalDecl name binfo e fun fvar => do
      (← separateHead fvar e).mapM fun (construct, fields) => do
        let construct := addPrefix construct name fields.size
        lambdaBoundedTelescope construct fields.size fun fvars _construct_body => do
          let lctx ← getLCtx
          let ids := fvars.map (fun x => x.fvarId!)
          let types := ids.map (fun x => (lctx.get! x).type)
          let names := ids.map (fun x => (lctx.get! x).userName)
          let separations ← (names.zip types).mapM (fun (name, type) => do pure ((← separatePi type name binfo).1.getD (Canonical.identity name type, #[Canonical.identity name type]))) -- eta...
          let destructs := (separations.zip fields).flatMap (fun ((_, destruct), field) => destruct.map (fun d => (d, field)))
          return (← constructApp separations.toList construct fvars, ← destructs.mapM (fun (d, f) => destructApp (d.replaceFVars fvars fields) f fvar))

  partial def separatePi (e : Expr) (name : Name) (binfo : BinderInfo) : DestructM (Option (Expr × Array Expr) × Array Nat) := do
    forallTelescopeReducingSeparate e e fun xs e xs' separations _e' => do
      let separateApp ← separateApp e name binfo
      let count := (separations).map fun (_, _, c) => c.size
      if separations.all (!·.1) && separateApp.isNone then
        return (none, count)
      let separations := separations.map (·.2)
      let (construct, destruct) := separateApp.getD (Canonical.identity name e, #[Canonical.identity name e])
      return (some (← constructPi construct xs destruct.size xs' ((xs.zip separations).flatMap (fun (x, (_, l)) => l.map (fun i => Canonical.apply i [x]))) separations, ← destruct.mapM fun d => destructPi d xs xs' separations), count)
end

def destructTactic (goal : MVarId) (premises : Array Name) : MetaM (Bool × List (Array FVarId × MVarId)) := do
  let toRevert ← goal.withContext do
    let mut toRevert := #[]
    for fvarId in (← getLCtx).getFVarIds do
      unless (← fvarId.getDecl).isAuxDecl do
        toRevert := toRevert.push fvarId
    pure toRevert
  let (_xs, reverted) ← goal.revert toRevert
  reverted.withContext do
    let separated ← ((separatePi (← reverted.getType) `destruct .default) : DestructM _).run (.ofList premises.toList)
    if let (some (construct, destruct), count) := separated then
      let (mvars, _, construct) ← lambdaMetaTelescope construct destruct.size
      reverted.assign construct
      return (true, (← mvars.mapM fun mvar => do pure (← mvar.mvarId!.introNP (count.take toRevert.size).sum)).toList)
    return (false, [← reverted.introNP toRevert.size])

def destructCanonical (goal : MVarId) (names : Array Name) : MetaM (Option (MVarId × (Expr → MetaM Expr))) := do
  let goal := (← mkFreshExprMVar (← goal.getType)).mvarId!
  goal.withContext do
    let typ ← goal.getType
    -- let level ← getLevel typ
    let dneg := ((← getEnv).find? ``Canonical.dneg).get!.value!
    let next := (← goal.apply (Canonical.apply dneg [typ]))[0]!
    let destruct ← destructTactic next (STRUCTURES ++ names)
    if !destruct.1 then
      return none
    let result := (destruct.2)[0]!
    let ⟨_, _, assignment⟩ := ← abstractMVars
      (← instantiateMVars (← getExprMVarAssignment? goal).get!)
    let assignment ← betaReduce assignment
    return (result.2, fun x => do
      betaReduce (Canonical.apply assignment [← mkLambdaFVars (result.1.map .fvar) x]))

syntax (name := destruct) "destruct " ("[" ident,* "]")? : tactic

/-- Eliminates structure types by unpacking them.  -/
@[tactic destruct] def evalDestruct : Tactic
| `(tactic| destruct [$ids:ident,*]) => do
  let names ← ids.getElems.mapM resolveGlobalConstNoOverload
  liftMetaTactic fun x => do
    let destruct ← destructTactic x (STRUCTURES ++ names)
    if !destruct.1 then
      logWarning "destruct made no progress."
    pure (destruct.2.map (·.2))
| `(tactic| destruct) => do
  liftMetaTactic fun x => do
    let destruct ← destructTactic x STRUCTURES
    if !destruct.1 then
      logWarning "destruct made no progress."
    pure (destruct.2.map (·.2))
| _ => throwUnsupportedSyntax

end Destruct
