Consider the following Lean goal:
```lean4
%
```

Library theorems:
```lean4
%
```

We would like to generate a `have` statement, representing an intermediate subgoal that is easier to prove from the premises.

For instance, if you wish to prove `P n` by induction, an intermediate subgoal may be the inductive step `∀ m : Nat, P m → P (m + 1)`, or the base case `P 0`. If you wish to prove an existential `∃ k, P k` using witness `w`, an intermediate subgoal may be `P w`. If you wish to case split on a disjunction `A ∨ B`, and your goal is `C`, an intermediate subgoal may be `A → C` or `B → C`. If you wish to prove an equality `x = y` you may identify a useful `z` for an intermediate subgoal `x = z` or `z = y`. If you wish to prove an equality between functions or bundled morphisms `f = g`, a useful intermediate subgoal is the pointwise statement `∀ x, f x = g x`. Ensure that your subgoal makes progress, towards proving the goal, without merely restating it. In particular, do not propose a subgoal whose type is equivalent to the current goal or to a hypothesis already in the context. Each `have` should introduce a genuinely new intermediate fact that, once assumed, makes the remaining goal strictly easier to close.

Please use the `have` tool to propose an intermediate statement.