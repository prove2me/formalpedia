-- Prove2me | solution 1 for MultiverseInvariantFragment.dot3_fails
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:36:57.282225+00:00
-- url     : https://prove2.me/submissions/ef0b0edc-b80a-44e4-a3fc-914a9baefb22

-- Sol generated from Logic/Multiverse/InvariantFragment.lean
import Mathlib
import Definitions.Def_Logic_Multiverse_BooleanValuedRealization
import Definitions.Def_Logic_Multiverse_ButtonsSwitches
import Definitions.Def_Logic_Multiverse_InvariantFragment
/-
# Multiverse-Invariant Fragments, Exact Frame Calibration and Branch Preservation

This file continues `Catalog/Logic/Multiverse/BooleanValuedRealization.lean`, whose
Boolean-valued universe and control frame it takes as given, and settles three
further directions of the multiverse programme.

## 1. Exact calibration of the modal strength of the frame (Direction 2)

* `directed_of_dot2` — the schema `.2` (`◇□p → □◇p`), valid for *all* predicates,
  **implies** directedness: `.2` is exactly directedness, so nothing weaker than a
  directed frame can validate it.
* `cacc_euclidean_iff` — the forcing frame is Euclidean (i.e. validates `5`)
  **iff there are no buttons at all**.  One button already destroys `S5`.
* `dot3_fails` — with two *independent* buttons the frame refutes the linearity
  axiom `.3`.  Hence the frame sits strictly between `S4.2` and `S4.3`: it is a
  genuine `S4.2` frame, not accidentally linear.

## 2. The multiverse-invariant fragment theorem (Direction 3)

`buttonFree_invariant` shows that the **button-free fragment** is invariant under
both forcing extensions and grounds; `invariant_iff_buttonFree` proves the sharp
converse: *an assertion is invariant along the button order iff it is equivalent to
a button-free assertion*.  The proof substitutes `⊥` for every button atom
(`subBtnFls`) and uses the substitution lemma `csat_subBtnFls`.  This is a genuine
characterization, and it is falsifiable in the intended sense: a single button atom
already fails invariance (`btn_atom_not_invariant`).

## 3. Calibration of branching by preserved backgrounds (Direction 4)

The exact preservation criterion is Boolean:

* `background_branches_iff` — a background condition `b` survives into **both** a
  `p`-branch and a `¬p`-branch **iff** `b ⊓ ⟦p⟧ ≠ ⊥` and `b ⊓ ⟦p⟧ᶜ ≠ ⊥`.

Applied to the control frame this yields `button_background_branches`: every
*button-definable* background (the abstract stand-in for an indestructible
large-cardinal assertion) is preserved in both CH branches, while
`background_obstruction` exhibits the boundary — a switch-dependent background has
an empty meet with one branch and therefore cannot be preserved.
-/

open MultiverseInvariantFragment

open Multiverse BooleanValuedRealization

/-! ## 1. Exact calibration of the modal strength of the frame -/


variable {W : Type*}



variable {Btn Sw : Type*}




/-! ## 2. The multiverse-invariant fragment -/


variable {Btn Sw : Type*}











/-! ## 3. Calibration of branching by preserved backgrounds -/


variable {α : Type*} {B : Type*} [BooleanAlgebra B]


variable {Btn Sw : Type*}







open MultiverseInvariantFragment in
theorem solution(b₁ b₂ : Btn) (hne : b₁ ≠ b₂) (g : Sw → Bool) :
    ¬ (box cacc (fun v => box cacc (pushedP b₁) v → pushedP b₂ v)
          ((∅ : Finset Btn), g)
      ∨ box cacc (fun v => box cacc (pushedP b₂) v → pushedP b₁ v)
          ((∅ : Finset Btn), g)) := by
  rintro (h | h)
  · have hb : box cacc (pushedP b₁) (({b₁} : Finset Btn), g) :=
      fun u hu => hu (Finset.mem_singleton_self b₁)
    have := h ({b₁}, g) (Finset.empty_subset _) hb
    rw [pushedP, Finset.mem_singleton] at this
    exact hne this.symm
  · have hb : box cacc (pushedP b₂) (({b₂} : Finset Btn), g) :=
      fun u hu => hu (Finset.mem_singleton_self b₂)
    have := h ({b₂}, g) (Finset.empty_subset _) hb
    rw [pushedP, Finset.mem_singleton] at this
    exact hne this
