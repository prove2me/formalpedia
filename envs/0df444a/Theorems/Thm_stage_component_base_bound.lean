-- Prove2me | Theorems.Thm_stage_component_base_bound
-- name    : stage_component_base_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T15:31:28.117494+00:00
-- url     : https://prove2.me/theorems/117cf5d4-e632-4588-88dc-37836d5cf860
-- title:
--   stage_component_base_bound
-- statement:
--   Automatically extracted helper theorem stage_component_base_bound from oversized parent candidate 2b1af8f4fbacbe24163e77f6aa890fd7194d81aeec39844c582b2de9ae15a21f.
-- source:
--   candidate-decomposition:4cebd027-58ee-45f9-b27c-450becd3a68f:2b1af8f4fbacbe24163e77f6aa890fd7194d81aeec39844c582b2de9ae15a21f

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_orthStage
import Theorems.Thm_ShorNonsmooth_NonlinEq_local_residual_linear_equivalence
import Theorems.Thm_ShorNonsmooth_NonlinEq_stage_orthDir_uniform_lower_bound
import Theorems.Thm_ShorNonsmooth_NonlinEq_stage_linear_bound_and_growth
import Theorems.Thm_ShorNonsmooth_NonlinEq_residual_after_step_quadratic
import Theorems.Thm_ShorNonsmooth_NonlinEq_orthogonal_increment_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ShorNonsmooth.NonlinEq

theorem stage_component_base_bound {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (δ L : ℝ) (hδ : 0 < δ)
    (hLip : ∀ i, ∀ x' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
      ∀ x'' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
        ‖gradient (ψ i) x' - gradient (ψ i) x''‖ ≤ L * ‖x' - x''‖)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsOrthStage ψ x) (k : Fin n)
    (M S b r : ℝ) (hM : 0 ≤ M) (hS : 0 ≤ S) (hb : 0 < b) (hr : 0 ≤ r)
    (hψk : |ψ k (x k.val)| ≤ M * (S * r))
    (hdir : b ≤ ‖orthDir ψ x k‖)
    (hxk : x k.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
    (hxk1 : x (k.val + 1) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) :
    |ψ k (x (k.val + 1))| ≤ max (max L 0 * (M * S) ^ 2 / (b / 2) ^ 2) 1 * r ^ 2 := by sorry
