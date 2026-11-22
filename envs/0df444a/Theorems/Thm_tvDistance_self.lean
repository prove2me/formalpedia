-- Prove2me | Theorems.Thm_tvDistance_self
-- name    : tvDistance_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:33:35.439536+00:00
-- url     : https://prove2.me/theorems/208becd6-3167-4173-b746-0084ea539b3d
-- title:
--   tv Distance self: tv Distance self
-- statement:
--   Total variation distance from a distribution to itself is zero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/FiniteVCApprox.lean#L91-L94
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/FiniteVCApprox.lean#L91-L94

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

theorem tvDistance_self {H : Type*} [Fintype H]
    (μ : FinitePMF H) :
    tvDistance μ μ = 0 := by sorry
