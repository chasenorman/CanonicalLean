import Canonical.Basic
import Canonical.Util
import Canonical.Monomorphize
import Lean

open Lean hiding Term
open Meta Expr Std

namespace Canonical

structure Definition where
  type : LOption Typ
  arity : Arity

structure ToCanonicalContext where
  arities : HashMap FVarId Arity

structure ToCanonicalState where
  definitions : HashMap String Definition

abbrev ToCanonicalM := StateT ToCanonicalState (ReaderT ToCanonicalContext MonoM)

def toVar (e : Expr) : MetaM Var := do pure { name := ← toNameString e }

/-- Some Lean Π-types cannot be converted into Canonical Π-types,
    and are instead converted into this structure. -/
structure Pi (A : Type u) (B : A → Type v) where
  f : (a : A) → B a

def elimSpecial (e : Expr) : MetaM Expr := do
  withApp e fun fn args =>
    match fn with
    | forallE name type body info => do
      assert! args.isEmpty
      let l2 ← withLocalDecl name info type fun fvar => getLevel (body.instantiate1 fvar)
      return (mkApp2 (.const ``Pi.mk [← getLevel type, l2]) type (.lam name type body info))
    | lit l => do
      assert! args.isEmpty
      if let .natVal n := l then
        if n <= 5 then
          return rawRawNatLit n
      return e
    | proj type idx struct => do
      let info := getStructureInfo (← getEnv) type
      return mkAppN (← mkProjection struct info.fieldNames[idx]!) args
    | _ => return e

mutual

  partial def toTyp (e : Expr) : ToCanonicalM Typ := do
    forallTelescopeReducing e (whnfType := true) fun xs body => do
      let params ← xs.mapM (toVar ·)
      let ids := xs.map (·.fvarId!)
      let types ← ids.mapM (·.getType)
      let arities ← (ids.zip types).mapM (fun ⟨id, type⟩ => do pure (id, ← typeArity type))
      withReader (fun ctx => { ctx with arities := ctx.arities.insertMany arities } ) do
        let paramTypes ← types.mapM (fun type => do pure (some (← toTyp type)))
        return { paramTypes, params, spine := ← toSpine body }

  partial def toTerm (e : Expr) (type : Expr) (arities : List Arity) (params : Array Var := #[]) : ToCanonicalM Term := do
    match ← whnf type with
    | forallE name binderType body info =>
      withLocalDecl name info binderType fun fvar =>
        match arities with
        | [] =>
          withReader (fun ctx => { ctx with arities := ctx.arities.insert fvar.fvarId! {} }) do
            let e := mkApp3 (const ``Pi.mk [← getLevel binderType, ← getLevel (body.instantiate1 fvar)])
              binderType (lam name binderType body info) e
            toTerm e (← inferType e) [] params
        | arity :: arities =>
          withReader (fun ctx => { ctx with arities := ctx.arities.insert fvar.fvarId! arity }) do
            toTerm (app e fvar) (body.instantiate1 fvar) arities (params.push (← toVar fvar))
    | _ =>
      assert! arities.isEmpty
      return { params, spine := ← toSpine (← whnf e) }

  partial def toSpine (e : Expr) : ToCanonicalM Spine := do
    withApp (← preprocessMono (← elimSpecial e)) fun fn args => do
      let (head, type) ← toHead fn
      let arity ← match e with
      | fvar id => do pure ((← read).arities.get! id)
      | _ => define head.toString type
      return ← addArgs { head := head.toString } type args.toList arity.params.toList

  partial def addArgs (spine : Spine) (type : Expr) (args : List Expr) (arities : List Arity) : ToCanonicalM Spine := do
    match ← whnf type with
    | forallE name binderType body info =>
      if args.isEmpty then
        dbg_trace name
      let spine ← match arities with
      | [] => do
        pure { head := (``Pi.f).toString, args := #[
          ← toTerm binderType (.sort .zero) {}, -- argument type
          ← toTerm (.lam name binderType body info)
                       (.forallE name binderType (.sort .zero) info) [{}], -- output type
          { spine }, -- function
          ← toTerm args.head! binderType {} -- argument
        ]}
      | arity :: _ => do
        let arg ← toTerm args.head! binderType arity.params.toList
        pure { spine with args := spine.args.push arg }
      addArgs spine (body.instantiate1 args.head!) args.tail! arities.tail
    | _ =>
      assert! args.isEmpty
      return spine

  partial def define (name : String) (type : Expr) : ToCanonicalM Arity := do
    let defineType := true
    let defn ← match (← get).definitions.get? name with
    | some defn => do pure defn
    | none => do
      let defn := { type := .undef, arity := ← typeArity type }
      modify fun state => { state with definitions := state.definitions.insert name defn }
      pure defn

    if defineType && defn.type matches .undef then
      modify fun state => { state with definitions := state.definitions.insert name { defn with type := .none } }
      let type ← toTyp type
      modify fun state => { state with definitions := state.definitions.insert name { defn with type := .some type } }
    return defn.arity

end
