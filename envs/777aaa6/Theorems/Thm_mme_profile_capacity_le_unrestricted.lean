-- Prove2me | Theorems.Thm_mme_profile_capacity_le_unrestricted
-- name    : mme_profile_capacity_le_unrestricted
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T13:59:48.857583+00:00
-- url     : https://prove2.me/theorems/93e27218-3daa-4aa6-9c05-e0934cdbd893
-- title:
--   Profile capacity is bounded by unrestricted fine words
-- statement:
--   The product of the three mode-profile block cardinalities is at most 3 to the power three times the number of fine coordinates. Each exact graded profile is a subtype of all complete-word functions on its positions.
-- source:
--   Natural logarithm repair budgets, finite profile capacities, and exact-step copy rounding.

import Definitions.Def_mme_recursive_yz_CW_cells
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
universe u

theorem mme_profile_capacity_le_unrestricted
    {P C : Type*} [Fintype P] (ell : ℕ) (cell : P → C)
    (shape : C → Fin 3 → ℕ) (mu : Fin 3 → C → CompleteWord ell → ℕ) :
    (∏ i : Fin 3, Nat.card (Block ell cell shape mu i)) ≤
      3 ^ (3 * (Fintype.card P * 2 ^ (ell - 1))) := by sorry
