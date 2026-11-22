-- Prove2me | Theorems.Thm_mwu_potential_T_bound
-- name    : mwu_potential_T_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:09.962375+00:00
-- url     : https://prove2.me/theorems/a2b4a3d2-78c3-4361-b408-04b403a48be3
-- title:
--   mwu potential T bound: mwu potential T bound
-- statement:
--   **Potential bound after T steps**: Φ_T ≤ |C| · (1 - ηv)^T.
--
--   This is the core MWU guarantee. Combined with individual weight lower
--   bounds (w_T(c) = (1-η)^{losses(c)}), it yields the regret bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ApproxMinimax.lean#L359-L383
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ApproxMinimax.lean#L359-L383

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section

theorem mwu_potential_T_bound {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (η : ℝ) (hη : 0 ≤ η) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0))
    (T : ℕ) :
    (mwuConfig M η hη1 v hrow T).potential ≤
    Fintype.card C * (1 - η * v) ^ T := by sorry
