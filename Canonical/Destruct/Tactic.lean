module

import Lean
public import Lean.Elab.Tactic.Basic
public meta import Canonical.Destruct.Basic

open Lean Elab Tactic

namespace Destruct

syntax (name := destruct) "destruct " ("[" ident,* "]")? : tactic

/-- Eliminates structure types by unpacking them.  -/
@[tactic destruct] public meta def evalDestruct : Tactic
| `(tactic| destruct [$ids:ident,*]) => do
  let names ← ids.getElems.mapM resolveGlobalConstNoOverload
  liftMetaTactic fun x => do
    let destruct ← destructTactic x (STRUCTURES ++ names)
    pure (destruct.map (·.2)).toList
| `(tactic| destruct) => do
  liftMetaTactic fun x => do
    let destruct ← destructTactic x STRUCTURES
    pure (destruct.map (·.2)).toList
| _ => throwUnsupportedSyntax

-- example : ∃ (t : Type 10), True := by
--   destruct
--   · exact Type 9
--
-- example : ∃ (t : Unit), True := by
--   destruct

example : (fun x y => (x * y, y)) 2 3 = (6, 3) := by
  destruct

-- Paper structure:
-- - Proving correctness
-- - Analogy to compilers (treating structures with stack indices? hmm)
-- - Lot's of good examples (showcase why destruct makes a lot of sense for practical stuff)
--   - Skolemization, currying are easy examples
--   - Destructing dependent pi types, propositional use cases are strong because no def eq constraint
--   - Solves blowup in the search?
--   - Program synthesis can be interesting. Skolemization stuff in constraints can be destructed.
-- - Just make it make sense that this is very useful
-- - Destruct is a version of unfold that works on structure types (unfolding
--   and when NOT to unfold is often very important)
-- - Destruct is very similar in ways to observational type theory? Especially
--   with the ext idea
-- - Destruct is constructive, proof producing
-- - Pi types in places (other than like equality) get handled by destruct (maybe give example)
-- - Use the LIPIcs format! I'll probably just overleaf and send to chase

-- Resources for paper examples:
-- https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Canonical/near/538228811
-- https://leanprover.zulipchat.com/#narrow/channel/239415-metaprogramming-.2F-tactics/topic/Destruct.20Tactic/near/538032110

-- Idea: take free variables in the context and pack them into a structure linearly?
-- Seems not reversible; this is just a random chase thought

-- Idea: destructing if statements?
-- Idea: Decidable gets rewritten with decide hmmm
-- Idea: like canonical data generation, but throw agents at it? sort of like
-- autoresearch? (someone to do the dumb things that make practical input) new
-- trend towards  This is a very interesting idea actually. Maybe we can spin an
-- arena on this or something
