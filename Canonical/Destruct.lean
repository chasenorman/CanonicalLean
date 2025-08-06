import Lean

open Lean Meta Expr Elab Tactic Core

def STRUCTURES : NameSet := .ofList [``Prod, ``PProd, ``And]

def applyAtIndex (name : Name) (i : Nat) (e : Array Expr) : MetaM Expr := do
  let info ← getConstInfo name
  let levels ← info.levelParams.mapM (fun _ => mkFreshLevelMVar)
  let type := info.type.instantiateLevelParams info.levelParams levels
  let mvars := (← forallMetaTelescopeReducing type).1
  let result := mkAppN (.const name levels) mvars
  for j in [0:e.size] do
    let success ← isDefEq mvars[i + j]! e[j]!
    assert! success
  return ← instantiateMVars result

def isDefEqForce (u v : Expr) : MetaM Bool := do
  match u, v with
  | app f a, app f' a' => isDefEqForce f f' <&&> isDefEqForce a a'
  | _, _ => isDefEqGuarded u v

/-- If `e` is a structure, produces expressions for the projections.
    Returns a callback which takes expressions for the projections and returns a structure again. -/
def destruct1 (e : Expr) (typ : Expr) : MetaM (Option (Array Expr × (Array Expr → MetaM Expr))) := do
  let (fn, args) := getAppFnArgs (← whnf typ)
  if STRUCTURES.contains fn then
    let info := (Lean.getStructureInfo? (← getEnv) fn).get!
    let mut fields := #[]
    for i in [0:info.fieldNames.size] do
      fields := fields.push (.proj fn i e)
    let induct ← getConstInfoInduct fn
    return some (fields, fun x => applyAtIndex induct.ctors[0]! 0 (args ++ x))
  else if fn == `Exists then -- skolemize
    let fields := #[← applyAtIndex ``Exists.choose 2 #[e], ← applyAtIndex ``Exists.choose_spec 2 #[e]]
    return some (fields, fun x => applyAtIndex ``Exists.intro 0 (args ++ x))
  else return none

partial def destructN (e : Expr) (typ : Expr) : MetaM (Option (Array Expr × (Array Expr → Array Expr → MetaM Expr))) := do
  forallTelescopeReducing typ fun xs typ => do
    if let some (step, reconstruct) ← destruct1 (mkAppN e xs) typ then
      let mut flattened := #[]
      let mut fields : Array (Nat × (Array Expr → Array Expr → MetaM Expr)) := #[]
      for field in step do
        match (← destructN field (← inferType field)) with
        | some (arr, field) => do
          fields := fields.push (arr.size, field)
          flattened := flattened ++ (← arr.mapM fun x => mkLambdaFVars xs x)
        | none =>
          fields := fields.push (1, fun x => fun xs => pure (mkAppN x[0]! xs))
          flattened := flattened.push (← mkLambdaFVars xs field)
      let lctx ← getLCtx
      let decls := xs.map (fun x => lctx.get! x.fvarId!)
      return some (flattened, fun x xs' => do
        withExistingLocalDecls decls.toList do
          let mut arr := x
          let mut fields' := #[]
          for (num, fn) in fields do
            fields' := fields'.push (← fn (arr.take num) (xs ++ xs'))
            arr := arr.drop num
          return ← mkLambdaFVars xs (← reconstruct fields')
      )
    return none

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
          if let some (arr, reconstruct) ← destructN (.fvar decl.fvarId) (decl.type) then
            let mut fvars : Array Expr := #[]
            for (e, idx) in arr.zipIdx do
              let defined ← (← build.define (s!"{decl.userName.toString}_{idx}").toName (← inferType e) e).intro1P
              build := defined.2
              fvars := fvars.push (.fvar defined.1)

            build ← build.withContext do
              let mvar := ((← getMCtx).findDecl? build).get!
              let reconstructed ← reconstruct fvars #[]
              let elimDecl := fun e : Expr => do
                let e ← Meta.transform (pre := fun e => do
                  withConfig (fun c => { c with proofIrrelevance := false }) do
                    for (replacement, idx) in arr.zipIdx do
                      let (mvars, _, replacement) ← lambdaMetaTelescope replacement
                        if ← isDefEqForce replacement e then
                          return .continue (← instantiateMVars (mkAppN fvars[idx]! mvars))
                    return .continue none
                ) e
                pure (e.replaceFVarId decl.fvarId reconstructed)
              let lctx := { mvar.lctx with decls := ← mvar.lctx.decls.mapM fun decl' => do decl'.mapM fun decl' => do
                if !decl'.isAuxDecl then
                  let decl' := decl'.setType (← elimDecl decl'.type)
                  if !fvars.contains (.fvar decl'.fvarId) then
                    if let some value := decl'.value? then
                      pure (decl'.setValue (← elimDecl value))
                    else pure decl'
                  else pure (.cdecl decl'.index decl'.fvarId decl'.userName decl'.type decl'.binderInfo decl'.kind)
                else pure decl'
              }
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
