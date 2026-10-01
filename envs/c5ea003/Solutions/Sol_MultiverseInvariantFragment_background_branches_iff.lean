-- Prove2me | solution 1 for MultiverseInvariantFragment.background_branches_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:35:36.529153+00:00
-- url     : https://prove2.me/submissions/46a64571-28a5-40c7-9b21-87c8cc3fcdca

-- Sol generated from Logic/Multiverse/InvariantFragment.lean
import Mathlib
import Definitions.Def_Logic_Multiverse_BooleanValuedRealization
import Definitions.Def_Logic_Multiverse_InvariantFragment
import Theorems.Thm_BooleanValuedRealization_Generic_compl_mem_iff
import Theorems.Thm_BooleanValuedRealization_sat_quot_iff
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
theorem solution(hR : Rich B) (v : α → B) (b : B) (p : BForm α) :
    ((∃ U : Generic B, U.mem b ∧ sat (quot v U) p) ∧
      (∃ U : Generic B, U.mem b ∧ ¬ sat (quot v U) p)) ↔
      (b ⊓ bval v p ≠ ⊥ ∧ b ⊓ (bval v p)ᶜ ≠ ⊥) := by
  constructor
  · rintro ⟨⟨U, hUb, hUp⟩, ⟨V, hVb, hVp⟩⟩
    constructor
    · intro hbot
      exact U.bot_notMem (hbot ▸ U.inf_mem hUb ((sat_quot_iff v U p).1 hUp))
    · intro hbot
      have hc : V.mem (bval v p)ᶜ := (V.compl_mem_iff _).2 (fun hm =>
        hVp ((sat_quot_iff v V p).2 hm))
      exact V.bot_notMem (hbot ▸ V.inf_mem hVb hc)
  · rintro ⟨h1, h2⟩
    obtain ⟨U, hU⟩ := hR _ h1
    obtain ⟨V, hV⟩ := hR _ h2
    refine ⟨⟨U, U.up hU inf_le_left, (sat_quot_iff v U p).2 (U.up hU inf_le_right)⟩,
      ⟨V, V.up hV inf_le_left, ?_⟩⟩
    rw [sat_quot_iff]
    exact (V.compl_mem_iff _).1 (V.up hV inf_le_right)
