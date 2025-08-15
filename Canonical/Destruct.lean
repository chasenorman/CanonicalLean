import Lean

open Lean Meta Expr Elab Tactic Core

def STRUCTURES : NameSet := .ofList [``Prod, ``PProd, ``And]

def applyAtIndex (name : Name) (i : Nat) (e : Expr) : MetaM Expr := do
  let info ← getConstInfo name
  let levels ← info.levelParams.mapM (fun _ => mkFreshLevelMVar)
  let type := info.type.instantiateLevelParams info.levelParams levels
  let mvars := (← forallMetaTelescopeReducing type).1
  let result := mkAppN (.const name levels) mvars
  let success ← isDefEq mvars[i]! e
  assert! success
  return ← instantiateMVars result

def isDefEqForce (u v : Expr) : MetaM Bool := do
  match u, v with
  | app f a, app f' a' => isDefEqForce f f' <&&> isDefEqForce a a'
  | _, _ => isDefEqGuarded u v

/-- If `e` is a structure, produces expressions for the projections.
    Returns a callback which takes expressions for the projections and returns a structure again. -/
def separateHead (e : Expr) (typ : Expr) : MetaM (Option (Expr × Array Expr)) := do
  let args := getAppArgs typ
  let fn := getAppFn typ
  let name := fn.constName?.getD .anonymous
  if STRUCTURES.contains name then
    let info := (Lean.getStructureInfo? (← getEnv) name).get!
    let mut fields := #[]
    for i in [0:info.fieldNames.size] do
      fields := fields.push (.proj name i e)
    let induct ← getConstInfoInduct name
    return some (← etaExpand (mkAppN (.const induct.ctors[0]! fn.constLevels!) args), fields)
  else if name == `Exists then -- skolemize
    let fields := #[← applyAtIndex ``Exists.choose 2 e, ← applyAtIndex ``Exists.choose_spec 2 e]
    return some (← etaExpand (mkAppN (.const ``Exists.intro fn.constLevels!) args), fields)
  else return none

def identity (e : Expr) : Expr := .lam `x e (.bvar 0) .default

def apply (e : Expr) (args : List Expr) : Expr :=
  match args with
  | [] => e
  | arg :: args => match e with
    | .lam name type body info =>
      apply (body.instantiate1 arg) args
    | _ => panic! "apply: expected a lambda, got {e}"

def constructApp (separations : List (Expr × Array Expr)) (reconstruct : Expr) (fvars : Array Expr) (fields : Array Expr := #[]) : MetaM Expr := do
  match separations with
  | [] => return apply reconstruct fields.toList
  | (construct, destruct) :: rest => do
    lambdaBoundedTelescope (construct.replaceFVars (fvars.take fields.size) fields) destruct.size fun xs construct => do
      return ← mkLambdaFVars xs (← constructApp rest reconstruct fvars (fields.push construct))

def destructApp (e : Expr) (field : Expr) (fvar : Expr) : MetaM Expr := do
  match e with
  | .lam name type body info =>
    return ← mkLambdaFVars #[fvar] (body.instantiate1 field)
  | _ => throwError "destructApp: expected a lambda, got {e}"

def constructPi (e : Expr) (xs : Array Expr) (n : Nat) (xs' : Array Expr) (separations : Array (Expr × Array Expr)) : MetaM Expr := do
  match n, e with
  | 0, _ => return ← mkLambdaFVars xs e
  | n + 1, .lam name type body info =>
    withLocalDecl name info (← mkForallFVars xs' (type.replaceFVars xs (separations.map (·.1)))) fun fvar => do
      return ← mkLambdaFVars #[fvar] (← constructPi (body.instantiate1 (mkAppN fvar ((xs.zip separations).flatMap (fun (x, (_, l)) => l.map (fun i => apply i [x]))))) xs n xs' separations)
  | _, _ => throwError "constructPi: expected a lambda, got {e}"

def destructPi (e : Expr) (xs : Array Expr) (xs' : Array Expr) (separations : Array (Expr × Array Expr)) : MetaM Expr := do
  match e with
  | .lam name type body info =>
    withLocalDecl name info (← mkForallFVars xs type) fun fvar => do
      return ← mkLambdaFVars (#[fvar] ++ xs') ((body.instantiate1 (mkAppN fvar xs)).replaceFVars xs (separations.map (·.1)))
  | _ => throwError "destructPi: expected a lambda, got {e}"

mutual
  partial def forallTelescopeReducingSeparate (e : Expr) (e' : Expr := e) (k : Array Expr → Expr → Array Expr → Array (Bool × Expr × Array Expr) → Expr → MetaM α)
    (xs : Array Expr := #[]) (xs' : Array Expr := #[]) (separations : Array (Bool × Expr × Array Expr) := #[]) : MetaM α := do
    match ← whnf e, ← whnf e' with
    | .forallE name type body info, forallE name' type' body' info' =>
      withLocalDecl name info type fun fvar => do
        let separate := (← separatePi type')
        let (construct, destruct) := separate.getD (identity type', #[identity type'])
        lambdaBoundedTelescope construct destruct.size fun fvars construct => do
          forallTelescopeReducingSeparate (body.instantiate1 fvar) (body'.instantiate1 construct) k (xs.push fvar) (xs' ++ fvars) (separations.push (separate.isSome, construct, destruct))
    | _, _ => k xs e xs' separations e'

  partial def separateApp (e : Expr) : MetaM (Option (Expr × Array Expr)) := do
    withLocalDecl `destruct .default e fun fvar => do -- it's this fvar
      (← separateHead fvar e).mapM fun (construct, fields) => do
        lambdaBoundedTelescope construct fields.size fun fvars construct_body => do
          let types ← fvars.mapM (fun x => do pure (← getFVarLocalDecl x).type)
          let separations ← types.mapM (fun type => do pure ((← separatePi type).getD (identity type, #[identity type]))) -- eta...
          let destructs := (separations.zip fields).flatMap (fun ((_, destruct), field) => destruct.map (fun d => (d, field)))
          return (← constructApp separations.toList construct fvars, ← destructs.mapM (fun (d, f) => destructApp (d.replaceFVars fvars fields) f fvar))

  partial def separatePi (e : Expr) : MetaM (Option (Expr × Array Expr)) := do
    forallTelescopeReducingSeparate e e fun xs e xs' separations e' => do
      let separateApp ← separateApp e
      if separations.all (!·.1) && separateApp.isNone then
        return none
      let separations := separations.map (·.2)
      let (construct, destruct) := separateApp.getD (identity e, #[identity e])
      return (← constructPi construct xs destruct.size xs' separations, ← destruct.mapM fun d => destructPi d xs xs' separations)
end

def replaceM (f? : Expr → MetaM (Option Expr)) (e : Expr) : MetaM Expr := do
  match ← f? e with
  | some eNew => return eNew
  | none      => match e with
    | .forallE _ d b _ => let d ← replaceM f? d; let b ← replaceM f? b; return e.updateForallE! d b
    | .lam _ d b _     => let d ← replaceM f? d; let b ← replaceM f? b; return e.updateLambdaE! d b
    | .mdata _ b       => let b ← replaceM f? b; return e.updateMData! b
    | .letE _ t v b _  => let t ← replaceM f? t; let v ← replaceM f? v; let b ← replaceM f? b; return e.updateLetE! t v b
    | .app f a         => let f ← replaceM f? f; let a ← replaceM f? a; return e.updateApp! f a
    | .proj _ _ b      => let b ← replaceM f? b; return e.updateProj! b
    | e                => return e

syntax (name := destruct) "destruct" : tactic

@[tactic destruct] def evalDestruct : Tactic
| `(tactic| destruct) => do
  liftMetaTactic1 fun goal =>
    goal.withContext do
      let mut build := goal
      for decl in (← getLCtx) do
        if !decl.isAuxDecl then
          if let some (reconstruct, arr) ← separatePi (decl.type) then
            -- dbg_trace arr
            let mut fvars : Array Expr := #[]
            for (e, idx) in arr.zipIdx do
              let e := apply e [.fvar decl.fvarId]
              let defined ← (← build.define (s!"{decl.userName.toString}_{idx}").toName (← inferType e) e).intro1P
              build := defined.2
              fvars := fvars.push (.fvar defined.1)

            build ← build.withContext do
              let mvar := ((← getMCtx).findDecl? build).get!
              let reconstructed := apply reconstruct fvars.toList
              let elimDecl := fun e : Expr => do
                let e ← Meta.transform (pre := fun e => do
                  withConfig (fun c => { c with proofIrrelevance := false }) do
                    for (replacement, idx) in arr.zipIdx do
                      let replacement := apply replacement [.fvar decl.fvarId]
                      let (mvars, _, replacement) ← lambdaMetaTelescope replacement
                        if ← isDefEqForce replacement e then
                          return .continue (← instantiateMVars (mkAppN fvars[idx]! mvars))
                    return .continue none
                ) e
                pure (e.replaceFVarId decl.fvarId reconstructed)
              let lctx ← mvar.lctx.foldrM (fun (decl : LocalDecl) (acc : LocalContext) => do
                let decl ← if !decl.isAuxDecl then do
                    let decl := decl.setType (← elimDecl decl.type)
                    if !fvars.contains (.fvar decl.fvarId) then
                      if let some value := decl.value? then
                        pure (decl.setValue (← elimDecl value))
                      else pure decl
                    else pure (LocalDecl.cdecl decl.index decl.fvarId decl.userName decl.type decl.binderInfo decl.kind)
                  else pure decl

                pure (acc.modifyLocalDecl decl.fvarId (fun _ => decl))
              ) mvar.lctx
              let _ ← build.modifyLCtx (fun _ => lctx)
              build.replaceTargetDefEq (← elimDecl mvar.type)

            build ← build.withContext do
              let mvar := ((← getMCtx).findDecl? build).get!
              let elimDecl := fun e : Expr => Meta.transform e (pre := fun e => do pure (TransformStep.continue
                (some (← withConfig (fun c => { c with zeta := false, zetaDelta := false }) (whnfR e)))))
              let lctx := { mvar.lctx with decls := ← mvar.lctx.decls.mapM fun decl' => do decl'.mapM fun decl' => do
                if !decl'.isAuxDecl then
                  let decl' := decl'.setType (← elimDecl decl'.type)
                  if let some value := decl'.value? then
                    pure (decl'.setValue (← elimDecl value))
                  else pure decl'
                else pure decl'
              }
              let _ ← build.modifyLCtx (fun _ => lctx)
              build.replaceTargetDefEq (← elimDecl mvar.type)

            let _ ← build.modifyLCtx (fun x => x.modifyLocalDecl decl.fvarId (fun x => x.setKind .auxDecl))
            -- build ← build.tryClear decl.fvarId
      pure (some build)
| _ => throwUnsupportedSyntax
