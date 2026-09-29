-- Prove2me | solution 1 for S42Independence.msat_box
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:46:59.386357+00:00
-- url     : https://prove2.me/submissions/753ca204-1c0a-4ac5-9a19-e5de4d38e171

-- Sol generated from Logic/Multiverse/S42Independence.lean
import Mathlib
import Definitions.Def_Logic_Multiverse_InvariantFragment
import Definitions.Def_Logic_Multiverse_S42Independence
/-
# `S4.2` Soundness for Directed Preorders, and Independence of `5` and `.3`

This file completes the calibration begun in
`Catalog/Logic/Multiverse/InvariantFragment.lean` by supplying the *deductive*
half of Direction 2 of the multiverse programme.

We define a modal language, its Kripke semantics, and a Hilbert calculus for
**`S4.2`** (classical propositional logic together with `K`, `T`, `4` and the
directedness axiom `.2`, closed under modus ponens and necessitation), and prove:

* `S42_sound` — **every theorem of `S4.2` is valid on every directed preorder**
  (induction on derivations; the `.2` case is exactly where directedness is used);
* `five_not_derivable` — the axiom `5` (`◇p → □◇p`) is **not** derivable in `S4.2`,
  because it fails on the finite button–switch forcing frame of the realization
  file, which *is* a directed preorder;
* `dot3_not_derivable` — the linearity axiom `.3`
  (`□(□p → q) ∨ □(□q → p)`) is **not** derivable in `S4.2` either: two independent
  buttons refute it.

Together with `BooleanValuedRealization.cacc_dot2` (soundness of `.2` on the frame)
and `MultiverseInvariantFragment.directed_of_dot2` (its exact semantic content),
this shows the modal logic of the finite pre-Boolean forcing frames contains `S4.2`
and is strictly below both `S5` and `S4.3`.
-/

open S42Independence

open BooleanValuedRealization MultiverseInvariantFragment

/-! ## The modal language and its Kripke semantics -/


open MForm
variable {α : Type*}



variable {α W : Type*}





/-! ## The Hilbert calculus `S4.2` -/




/-! ## The finite control frame as a directed preorder -/





/-! ## Independence of `5` -/



/-! ## Independence of `.3` -/






open S42Independence in
@[simp] theorem solution(R : W → W → Prop) (V : α → W → Prop) (p : MForm α) (w : W) :
    msat R V (.box p) w ↔ ∀ v, R w v → msat R V p v := Iff.rfl
