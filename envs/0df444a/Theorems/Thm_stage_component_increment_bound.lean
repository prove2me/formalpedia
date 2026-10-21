-- Prove2me | Theorems.Thm_stage_component_increment_bound
-- name    : stage_component_increment_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T15:31:34.261955+00:00
-- url     : https://prove2.me/theorems/9dc3e491-3711-4fd2-b2f1-a8ba6e244223
-- title:
--   stage_component_increment_bound
-- statement:
--   Automatically extracted helper theorem stage_component_increment_bound from oversized parent candidate 2b1af8f4fbacbe24163e77f6aa890fd7194d81aeec39844c582b2de9ae15a21f.
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

theorem stage_component_increment_bound {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (δ L : ℝ) (hδ : 0 < δ)
    (hLip : ∀ i, ∀ x' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
      ∀ x'' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
        ‖gradient (ψ i) x' - gradient (ψ i) x''‖ ≤ L * ‖x' - x''‖)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsOrthStage ψ x)
    (k j : Fin n) (hkj : k.val < j.val)
    (M S b r : ℝ) (hM : 0 ≤ M) (hS : 0 ≤ S) (hb : 0 < b) (hr : 0 ≤ r)
    (hψj : |ψ j (x j.val)| ≤ M * (S * r))
    (hdir : b ≤ ‖orthDir ψ x j‖)
    (hnormk : ‖x k.val‖ ≤ S * r) (hnormj : ‖x j.val‖ ≤ S * r)
    (hballk : x k.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
    (hballj : x j.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
    (hballj1 : x (j.val + 1) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
    (horthEarlier : inner ℝ (gradient (ψ k) (x k.val)) (orthDir ψ x j) = 0) :
    |ψ k (x (j.val + 1)) - ψ k (x j.val)| ≤
      max (max L 0 * (M * S / b) * (M * S / b + 2 * S)) 1 * r ^ 2 := by sorry
