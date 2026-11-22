-- Prove2me | Theorems.Thm_tvDistance_comm
-- name    : tvDistance_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:33:29.47522+00:00
-- url     : https://prove2.me/theorems/9fd17ab6-dab4-4331-b971-5fade2261fc2
-- title:
--   tv Distance comm: tv Distance comm
-- statement:
--   Total variation distance is symmetric.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/FiniteVCApprox.lean#L85-L88
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/FiniteVCApprox.lean#L85-L88

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

theorem tvDistance_comm {H : Type*} [Fintype H]
    (μ ν : FinitePMF H) :
    tvDistance μ ν = tvDistance ν μ := by sorry
