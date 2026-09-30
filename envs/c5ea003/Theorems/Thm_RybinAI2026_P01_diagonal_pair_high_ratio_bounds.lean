-- Prove2me | Theorems.Thm_RybinAI2026_P01_diagonal_pair_high_ratio_bounds
-- name    : RybinAI2026.P01.diagonal_pair_high_ratio_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T01:52:01.678319+00:00
-- url     : https://prove2.me/theorems/d89fd956-dd9a-4fd8-b7e5-ae39343dbca0
-- title:
--   High-parameter diagonal pair ratio bounds
-- statement:
--   In the high branch x+y>1 of the aligned diagonal pair-contraction proof, the antitone weight G(t)(1+1/sqrt(t)) bounds both endpoint ratios. After the exact parameter substitutions alpha=x/(1-y), beta=y/(1-x), A=sqrt(x(1-y)), B=sqrt(y(1-x)), and z=sqrt(T), the bounds are r <= (x+A z)/(1+z) and s <= (B+y z)/(1+z).
-- source:
--   High-branch ratio step in the exact aligned diagonal 2D proof, artifacts/p01_slack/2026-09-29-no-w-pair.md, Addendum: aligned 2D pair contraction resolved. It applies the already-Proved generic endpoint ratio inequality to (T/alpha,T) and (1/(beta*T),1/T); it is a source-faithful prerequisite for RybinAI2026.P01.aligned_diagonal_pair_contraction (9b380478-f4d0-4431-82e4-d7511da6dafb).

import Mathlib
import Theorems.Thm_RybinAI2026_P01_ratio_bound_of_slope_weight_antitone

theorem RybinAI2026.P01.diagonal_pair_high_ratio_bounds (G : ℝ → ℝ)
    (hGpos : ∀ t, 0 < t → 0 < G t)
    (hanti : AntitoneOn (fun t : ℝ => G t * (1 + (Real.sqrt t)⁻¹)) (Set.Ioi 0))
    (x y T : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (hy0 : 0 < y) (hy1 : y < 1) (hT : 0 < T) (hxy : 1 < x + y) :
    let α : ℝ := x / (1 - y)
    let β : ℝ := y / (1 - x)
    let A : ℝ := Real.sqrt (x * (1 - y))
    let B : ℝ := Real.sqrt (y * (1 - x))
    let z : ℝ := Real.sqrt T
    A * (G T / G (T / α)) ≤ (x + A * z) / (1 + z) ∧
      B * (G (1 / T) / G (1 / (β * T))) ≤ (B + y * z) / (1 + z) := by
  sorry
