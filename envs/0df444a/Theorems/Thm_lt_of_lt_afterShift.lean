-- Prove2me | Theorems.Thm_lt_of_lt_afterShift
-- name    : lt_of_lt_afterShift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:44:03.114429+00:00
-- url     : https://prove2.me/theorems/7f4fb758-b49b-465e-98d4-05ecd2779806
-- title:
--   lt of lt after Shift: lt of lt after Shift
-- statement:
--   The lt of lt after Shift construction uses the lt of lt after Shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Ray.lean#L70-L73
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Ray.lean#L70-L73

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Ray
set_option autoImplicit true
@[expose] public section
public section
open Set List
noncomputable section
variable {M : ℕ → ℕ}

theorem lt_of_lt_afterShift {a k : ℕ} (hk : k < afterShift M a) : M k ≤ a := by sorry
