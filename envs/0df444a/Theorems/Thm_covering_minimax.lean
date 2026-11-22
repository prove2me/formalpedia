-- Prove2me | Theorems.Thm_covering_minimax
-- name    : covering_minimax
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:07.065821+00:00
-- url     : https://prove2.me/theorems/b7b5064f-6c33-4488-9b86-8526b4900746
-- title:
--   covering minimax: covering minimax
-- statement:
--   **Covering-based minimax**: if the minimax value > 0, there exists
--       a row distribution with payoff ≥ 1/|C| against every column.
--
--       Proof: for each column c, pick a row r_c with M(r_c, c) = true
--       (guaranteed by `exists_covering_row`). The empirical distribution of
--       these rows gives payoff ≥ 1/|C| against every column, since each
--       column c₀ is covered by at least one row (namely r_c₀).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ApproxMinimax.lean#L167-L201
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ApproxMinimax.lean#L167-L201

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section

theorem covering_minimax
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (v : ℝ) (hv : 0 < v)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    ∃ p : FinitePMF R, ∀ c : C,
      (1 : ℝ) / Fintype.card C ≤ boolGamePayoff M p c := by sorry
