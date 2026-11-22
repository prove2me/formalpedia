-- Prove2me | Theorems.Thm_expectation_approx_of_tv
-- name    : expectation_approx_of_tv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:36.600306+00:00
-- url     : https://prove2.me/theorems/1e2e7184-682b-4216-aea9-d6b43144027b
-- title:
--   expectation approx of tv: expectation approx of tv
-- statement:
--   **Transfer principle.** If `tvDistance μ ν ≤ δ`, then for every `Bool`-valued test
--   `f`, `|E_μ[f] - E_ν[f]| ≤ δ`. This is the inequality that lets the approximate-minimax
--   route to compression replace a target distribution by an empirical distribution: any
--   high-probability event under `μ` is approximately high-probability under `ν`, with
--   slack controlled by the TV distance.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/FiniteVCApprox.lean#L103-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/FiniteVCApprox.lean#L103-L122

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

theorem expectation_approx_of_tv {H : Type*} [Fintype H]
    (μ ν : FinitePMF H) (f : H → Bool) (δ : ℝ)
    (hδ : tvDistance μ ν ≤ δ) :
    |boolTestExpectation μ f - boolTestExpectation ν f| ≤ δ := by sorry
