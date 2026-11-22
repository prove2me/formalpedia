-- Prove2me | Theorems.Thm_boolTestExpectation_empirical_eq_avg
-- name    : boolTestExpectation_empirical_eq_avg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:26.199495+00:00
-- url     : https://prove2.me/theorems/165cf2ee-327f-4b32-b035-c5b719e08ad6
-- title:
--   bool Test Expectation empirical eq avg: bool Test Expectation empirical eq avg
-- statement:
--   Bridges the `FinitePMF` view and the sample-average view: the expectation of a
--   `Bool`-valued test under the empirical PMF of a sample equals the sample average
--   `(1/T) ∑_t f (s_t)`. This lets the MWU updates and the approximation transfer
--   principle live in the same distributional framework.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/FiniteVCApprox.lean#L141-L166
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/FiniteVCApprox.lean#L141-L166

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

theorem boolTestExpectation_empirical_eq_avg
    {H : Type*} [Fintype H] [DecidableEq H]
    {T : ℕ} (hT : 0 < T) (hs : Fin T → H) (f : H → Bool) :
    boolTestExpectation (empiricalPMF hT hs) f =
    (∑ t : Fin T, if f (hs t) then (1 : ℝ) else 0) / T := by sorry
