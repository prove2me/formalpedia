-- Prove2me | Theorems.Thm_RybinAI2026_P01_diagonal_pair_low_ratio_bounds
-- name    : RybinAI2026.P01.diagonal_pair_low_ratio_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T00:04:20.936823+00:00
-- url     : https://prove2.me/theorems/39d7605a-f499-47a6-9d2b-5b7a2ce08031
-- title:
--   Low-parameter diagonal pair ratios
-- statement:
--   In the x+y≤1 branch of the aligned diagonal pair proof, both shape parameters x/(1-y) and y/(1-x) are at most one. If G is positive and increasing, each G-ratio is at most one, so the two normalized ratios are bounded by their square-root prefactors.
-- source:
--   Low-parameter branch of the aligned diagonal pair-contraction proof in artifacts/p01_slack/2026-09-29-no-w-pair.md.

import Mathlib

theorem RybinAI2026.P01.diagonal_pair_low_ratio_bounds (G : ℝ → ℝ)
    (hGpos : ∀ t, 0 < t → 0 < G t)
    (hGmono : MonotoneOn G (Set.Ioi 0))
    (x y T : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (hy0 : 0 < y) (hy1 : y < 1) (hT : 0 < T) (hxy : x + y ≤ 1) :
    (Real.sqrt (x * (1 - y)) *
        (G T / G (T / (x / (1 - y))))) ^ 2 ≤ x * (1 - y) ∧
    (Real.sqrt (y * (1 - x)) *
        (G (1 / T) / G (1 / ((y / (1 - x)) * T)))) ^ 2 ≤ y * (1 - x) := by
  sorry
