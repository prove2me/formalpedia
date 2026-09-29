-- Prove2me | solution 1 for S42Independence.dot3_fails_ctrl
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:25:54.039267+00:00
-- url     : https://prove2.me/submissions/58652f1f-6162-451a-bf64-2e67e8d6dbe4

-- Sol generated from Logic/Multiverse/S42Independence.lean
import Mathlib
import Definitions.Def_Logic_Multiverse_BooleanValuedRealization
import Definitions.Def_Logic_Multiverse_InvariantFragment
import Definitions.Def_Logic_Multiverse_S42Independence
import Theorems.Thm_S42Independence_msat_atom
import Theorems.Thm_S42Independence_msat_disj
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
theorem solution: ¬ msat ctrlFrame.rel Vpush dot3Formula w₀ := by
  rw [dot3Formula, msat_disj]
  rintro (h | h)
  · have hb : msat ctrlFrame.rel Vpush (.box (.atom true))
        (({true} : Finset Bool), fun _ => false) :=
      fun u hu => hu (Finset.mem_singleton_self true)
    have hq := h ({true}, fun _ => false) (Finset.empty_subset _) hb
    rw [msat_atom, Vpush, Finset.mem_singleton] at hq
    exact Bool.false_ne_true hq
  · have hb : msat ctrlFrame.rel Vpush (.box (.atom false))
        (({false} : Finset Bool), fun _ => false) :=
      fun u hu => hu (Finset.mem_singleton_self false)
    have hq := h ({false}, fun _ => false) (Finset.empty_subset _) hb
    rw [msat_atom, Vpush, Finset.mem_singleton] at hq
    exact Bool.false_ne_true hq.symm
