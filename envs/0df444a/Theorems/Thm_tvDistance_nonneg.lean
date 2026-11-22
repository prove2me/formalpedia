-- Prove2me | Theorems.Thm_tvDistance_nonneg
-- name    : tvDistance_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:33:23.469595+00:00
-- url     : https://prove2.me/theorems/042b640e-16c4-479b-9151-959efdadd93f
-- title:
--   tv Distance nonneg: tv Distance nonneg
-- statement:
--   Total variation distance is nonnegative.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/FiniteVCApprox.lean#L79-L82
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/FiniteVCApprox.lean#L79-L82

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

theorem tvDistance_nonneg {H : Type*} [Fintype H]
    (μ ν : FinitePMF H) :
    0 ≤ tvDistance μ ν := by sorry
