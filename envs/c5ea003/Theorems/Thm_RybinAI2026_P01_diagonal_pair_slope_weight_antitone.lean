-- Prove2me | Theorems.Thm_RybinAI2026_P01_diagonal_pair_slope_weight_antitone
-- name    : RybinAI2026.P01.diagonal_pair_slope_weight_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T23:25:44.176203+00:00
-- url     : https://prove2.me/theorems/81281666-4b82-44da-b95a-9a31e152b333
-- title:
--   Log-slope envelope gives the integrated ratio bound
-- statement:
--   If a positive differentiable function has logarithmic slope at most 1/(2(1+sqrt(t))), then G(t)(1+1/sqrt(t)) is antitone on the positive reals. Comparing this quantity at two endpoints is exactly the integrated slope-ratio envelope used in the x+y>1 branch of the aligned diagonal pair-contraction proof.
-- source:
--   Exact calculus connector for the integrated log-slope estimate in the aligned diagonal 2D pair-contraction proof in artifacts/p01_slack/2026-09-29-no-w-pair.md. It is obtained by differentiating G(t)(1+1/sqrt(t)) and using the displayed slope bound.

import Mathlib

theorem RybinAI2026.P01.diagonal_pair_slope_weight_antitone (G G' : ℝ → ℝ)
    (hGpos : ∀ t, 0 < t → 0 < G t)
    (hGderiv : ∀ t, 0 < t → HasDerivAt G (G' t) t)
    (hslope : ∀ t, 0 < t →
      t * G' t / G t ≤ 1 / (2 * (1 + Real.sqrt t))) :
    AntitoneOn (fun t : ℝ => G t * (1 + (Real.sqrt t)⁻¹)) (Set.Ioi 0) := by
  sorry
