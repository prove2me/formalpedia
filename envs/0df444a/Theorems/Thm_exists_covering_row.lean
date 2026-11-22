-- Prove2me | Theorems.Thm_exists_covering_row
-- name    : exists_covering_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:06.381285+00:00
-- url     : https://prove2.me/theorems/7cd8990f-9f99-4da5-aa7e-3c56c7896c20
-- title:
--   exists covering row: exists covering row
-- statement:
--   If minimax value > 0, every column has a row with M(r,c) = true.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ApproxMinimax.lean#L137-L156
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ApproxMinimax.lean#L137-L156

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section

theorem exists_covering_row {R C : Type*} [Fintype C]
    (M : R → C → Bool) (v : ℝ) (hv : 0 < v)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    ∀ c₀ : C, ∃ r : R, M r c₀ = true := by sorry
