-- Prove2me | Theorems.Thm_minimax_value_le_one
-- name    : minimax_value_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:06.132809+00:00
-- url     : https://prove2.me/theorems/cc25e9a9-c395-48a0-b8c8-caa956781386
-- title:
--   minimax value le one: minimax value le one
-- statement:
--   The minimax value of a Boolean game is at most 1.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ApproxMinimax.lean#L121-L132
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ApproxMinimax.lean#L121-L132

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section

theorem minimax_value_le_one {R C : Type*} [Fintype C] [Nonempty C]
    (M : R → C → Bool) (v : ℝ)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    v ≤ 1 := by sorry
