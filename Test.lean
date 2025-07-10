import Canonical

def test := Not False

open Lean Meta
#eval (do
  let e := ((← getEnv).find? `test).get!.value!
  withArityUnfold do
    let typ := ← ((do (do Canonical.toTyp e).run' { definitions := ∅ }).run { arities := ∅ }).run' {}
    dbg_trace typ
)
