-- Prove2me | Theorems.Thm_finite_approx_minimax
-- name    : finite_approx_minimax
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:49.752687+00:00
-- url     : https://prove2.me/theorems/df554dfd-5ac5-40ed-b461-c03be02b947e
-- title:
--   finite approx minimax: finite approx minimax
-- statement:
--   **Approximate minimax for finite Boolean games**.
--
--   If for every column mixture q, the row player has a pure best response
--   with expected payoff ≥ v, then there exists a row mixture p such that
--   every pure column gets payoff ≥ v - ε.
--
--   This version uses the covering argument (payoff ≥ 1/|C| for all columns)
--   combined with the feasibility condition v - ε ≤ 1/|C|.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ApproxMinimax.lean#L213-L226
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ApproxMinimax.lean#L213-L226

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section

theorem finite_approx_minimax
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty C] [Nonempty R]
    (M : R → C → Bool) (v ε : ℝ) (hε : 0 < ε)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0))
    (hε_feasible : v - ε ≤ 1 / Fintype.card C) :
    ∃ p : FinitePMF R, ∀ c : C,
      v - ε ≤ boolGamePayoff M p c := by sorry
