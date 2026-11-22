-- Prove2me | Theorems.Thm_tv_bound_implies_all_tests
-- name    : tv_bound_implies_all_tests
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:38:04.999799+00:00
-- url     : https://prove2.me/theorems/b840de49-f232-4dc8-b7f0-85ce25985614
-- title:
--   tv bound implies all tests: tv bound implies all tests
-- statement:
--   Uniform variant of `expectation_approx_of_tv`: a single `tvDistance` bound suffices
--   for every test in any finite family simultaneously, with no union bound. The form
--   actually used by the compression characterisation, where the family is the restricted
--   concept class.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/FiniteVCApprox.lean#L128-L133
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/FiniteVCApprox.lean#L128-L133

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

theorem tv_bound_implies_all_tests {H : Type*} [Fintype H]
    (μ ν : FinitePMF H) (ε : ℝ)
    (hε : tvDistance μ ν ≤ ε)
    (tests : Finset (H → Bool)) :
    ∀ f ∈ tests, |boolTestExpectation μ f - boolTestExpectation ν f| ≤ ε := by sorry
