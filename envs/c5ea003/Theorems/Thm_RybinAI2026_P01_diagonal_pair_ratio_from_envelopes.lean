-- Prove2me | Theorems.Thm_RybinAI2026_P01_diagonal_pair_ratio_from_envelopes
-- name    : RybinAI2026.P01.diagonal_pair_ratio_from_envelopes
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T23:10:32.923811+00:00
-- url     : https://prove2.me/theorems/8e72a12a-d3a3-46ef-952d-7c9f3c7a06b8
-- title:
--   Assembly of the aligned diagonal pair-contraction envelopes
-- statement:
--   The two branch-specific ratio estimates in the aligned diagonal 2D pair-contraction argument imply that the sum of the squared ratios is at most one. In the x+y≤1 branch the ratios are bounded by A and B; in the x+y>1 branch they are bounded by the integrated-slope expressions. The hypotheses A²=x(1-y) and B²=y(1-x) are the exact coefficient definitions in the paper proof.
-- source:
--   Source-faithful scalar assembly step from the aligned diagonal 2D pair-contraction proof in artifacts/p01_slack/2026-09-29-no-w-pair.md, Addendum: aligned 2D pair contraction resolved. This discharges the final branch algebra after the two ratio-envelope estimates and feeds the perpendicular-rank-one P01 reduction.

import Mathlib
import Theorems.Thm_RybinAI2026_P01_diagonal_pair_coefficient_bound

theorem RybinAI2026.P01.diagonal_pair_ratio_from_envelopes {x y A B z r s : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : A ^ 2 = x * (1 - y)) (hB : B ^ 2 = y * (1 - x))
    (hz : 0 ≤ z) (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hlow : x + y ≤ 1 → r ^ 2 ≤ A ^ 2 ∧ s ^ 2 ≤ B ^ 2)
    (hhigh : 1 < x + y →
      r ≤ (x + A * z) / (1 + z) ∧ s ≤ (B + y * z) / (1 + z)) :
    r ^ 2 + s ^ 2 ≤ 1 := by
  sorry
