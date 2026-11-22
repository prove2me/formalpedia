-- Prove2me | Theorems.Thm_boolTestExpectation_le_one
-- name    : boolTestExpectation_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:34.210381+00:00
-- url     : https://prove2.me/theorems/4f20d0b5-4949-4a61-a052-5737d55e0c87
-- title:
--   bool Test Expectation le one: bool Test Expectation le one
-- statement:
--   A convex combination of values in `{0, 1}` is at most `1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/FiniteVCApprox.lean#L56-L63
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/FiniteVCApprox.lean#L56-L63

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_FiniteVCApprox
set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section

theorem boolTestExpectation_le_one {H : Type*} [Fintype H]
    (μ : FinitePMF H) (f : H → Bool) :
    boolTestExpectation μ f ≤ 1 := by sorry
