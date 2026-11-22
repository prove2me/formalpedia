-- Prove2me | Theorems.Thm_mwu_approx_minimax
-- name    : mwu_approx_minimax
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:19.711252+00:00
-- url     : https://prove2.me/theorems/faa9b5fd-ede9-4622-b164-9ef87dc20566
-- title:
--   mwu approx minimax: mwu approx minimax
-- statement:
--   **Genuine approximate minimax via MWU regret extraction.**
--       If every column mixture admits a pure row with expected payoff ≥ v,
--       then there is a row mixture with payoff ≥ v - ε against every column.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ApproxMinimax.lean#L579-L620
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ApproxMinimax.lean#L579-L620

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section

theorem mwu_approx_minimax
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty R] [Nonempty C]
    (M : R → C → Bool) (v ε : ℝ) (hε : 0 < ε)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
    v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    ∃ p : FinitePMF R, ∀ c : C, v - ε ≤ boolGamePayoff M p c := by sorry
