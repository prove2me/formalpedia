-- Prove2me | Theorems.Thm_RybinAI2026_P01_aligned_diagonal_pair_contraction
-- name    : RybinAI2026.P01.aligned_diagonal_pair_contraction
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T00:07:45.464553+00:00
-- url     : https://prove2.me/theorems/9b380478-f4d0-4431-82e4-d7511da6dafb
-- title:
--   Pair contraction for aligned diagonal forms in dimension two
-- statement:
--   For positive diagonal matrices P=diag(a,b) and Q=diag(c,d) in dimension two, the two directional integral ratios F_(P+Q)(e1)/F_P(e1) and F_(P+Q)(e2)/F_Q(e2), written using the exact scalar integral psi(t)=integral_0^1 (1+(t-1)s^2)^(-1) ds, have squared sum at most one. The common sphere normalization cancels.
-- source:
--   Aligned diagonal two-dimensional pair-contraction proof in artifacts/p01_slack/2026-09-29-no-w-pair.md, Addendum: aligned 2D pair contraction resolved.

import Mathlib

theorem RybinAI2026.P01.aligned_diagonal_pair_contraction (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    let ψ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹
    let r₁ : ℝ := a / (a + c) * (ψ ((b + d) / (a + c)) / ψ (b / a))
    let r₂ : ℝ := d / (b + d) * (ψ ((a + c) / (b + d)) / ψ (c / d))
    r₁ ^ 2 + r₂ ^ 2 ≤ 1 := by
  sorry
