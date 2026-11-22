-- Prove2me | Theorems.Thm_boolTestExpectation_nonneg
-- name    : boolTestExpectation_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:30.967147+00:00
-- url     : https://prove2.me/theorems/15323c06-e00d-47f8-b872-9314487d83af
-- title:
--   bool Test Expectation nonneg: bool Test Expectation nonneg
-- statement:
--   A convex combination of values in `{0, 1}` is nonnegative.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/FiniteVCApprox.lean#L49-L53
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/FiniteVCApprox.lean#L49-L53

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

theorem boolTestExpectation_nonneg {H : Type*} [Fintype H]
    (μ : FinitePMF H) (f : H → Bool) :
    0 ≤ boolTestExpectation μ f := by sorry
