-- Prove2me | Theorems.Thm_best_response_payoff_weights
-- name    : best_response_payoff_weights
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:11.302809+00:00
-- url     : https://prove2.me/theorems/3f79587a-06f5-4628-b15a-777e2c17f80f
-- title:
--   best response payoff weights: best response payoff weights
-- statement:
--   Best response payoff ≥ v · Φ in terms of weights.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ApproxMinimax.lean#L270-L289
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ApproxMinimax.lean#L270-L289

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section

theorem best_response_payoff_weights {R C : Type*} [Fintype C] [Nonempty C]
    (M : R → C → Bool) (v : ℝ)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0))
    (cfg : MWUConfig C) :
    v * cfg.potential ≤
    ∑ c : C, cfg.weights c *
      (if M (hrow cfg.toPMF).choose c then (1 : ℝ) else 0) := by sorry
