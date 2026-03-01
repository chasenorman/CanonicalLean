# Canonical

[Canonical](https://github.com/chasenorman/Canonical) exhaustively searches for terms in dependent type theory. The `canonical` tactic proves theorems, synthesizes programs, and constructs objects in Lean.

https://github.com/user-attachments/assets/ec13ad85-7d09-4a32-9c73-3b5b501722a4

## Installation

Add the following dependency to your `lakefile.toml`:
```
[[require]]
name = "Canonical"
scope = "chasenorman"
```
Or, if you are using a `lakefile.lean`:
```
require "chasenorman" / "Canonical"
```

You should then be prompted to run `lake update Canonical`.

**On `v4.28.0` and above, it may be necessary to write `import Canonical` and then invoke `lake clean` and `lake build` from the terminal, to properly install Canonical for the first time.**

## Usage

Basic examples:

```lean
import Canonical

-- prove properties by induction
def add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := 
  by canonical

-- enumerate over elements of a type
example : List Nat := by canonical (count := 10)

-- supply premises
def Set (X : Type) := X → Prop
axiom P_ne_not_P : P ≠ ¬ P
theorem Cantor (f : X → Set X) : ¬ ∀ y, ∃ x, f x = y :=
  by canonical [P_ne_not_P, congrFun]
```

More examples can be found [in the Canonical repository](https://github.com/chasenorman/Canonical/tree/main/lean/Results).
