-- Prove2me | Theorems.Thm_MultiverseInvariantFragment_button_background_branches
-- name    : MultiverseInvariantFragment.button_background_branches
-- status  : Open
-- author  : @raver1975
-- created : 2026-09-12T14:38:55.094946+00:00
-- url     : https://prove2.me/theorems/3d66fdba-dee7-49f6-8f41-ce30df6efa64
-- title:
--   The Boolean-valued form of the previous theorem: the value of a pushed button
-- statement:
--   The Boolean-valued form of the previous theorem: the value of a pushed button
--   meets both the CH branch and the `¬CH` branch, so by `background_branches_iff` a
--   button background is preserved in two opposite generic quotients of one and the
--   same Boolean-valued universe.
--
--   ```lean
--   theorem MultiverseInvariantFragment.button_background_branches(S : Finset Btn) (b : Btn) (s : Sw) (hb : b ∈ S) :
--       (∃ U : Generic (Set (Gen Sw)), U.mem (cassign S (CAtom.btn b)) ∧
--           sat (quot (cassign S) U) (chAtom (Btn := Btn) s)) ∧
--       (∃ U : Generic (Set (Gen Sw)), U.mem (cassign S (CAtom.btn b)) ∧
--           ¬ sat (quot (cassign S) U) (chAtom (Btn := Btn) s)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/Multiverse/InvariantFragment.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/Multiverse/InvariantFragment.lean#L263

-- Thm stub generated from Logic/Multiverse/InvariantFragment.lean
import Mathlib
import Definitions.Def_Logic_Multiverse_BooleanValuedRealization
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

theorem MultiverseInvariantFragment.button_background_branches(S : Finset Btn) (b : Btn) (s : Sw) (hb : b ∈ S) :
    (∃ U : Generic (Set (Gen Sw)), U.mem (cassign S (CAtom.btn b)) ∧
        sat (quot (cassign S) U) (chAtom (Btn := Btn) s)) ∧
    (∃ U : Generic (Set (Gen Sw)), U.mem (cassign S (CAtom.btn b)) ∧
        ¬ sat (quot (cassign S) U) (chAtom (Btn := Btn) s)) := by sorry
