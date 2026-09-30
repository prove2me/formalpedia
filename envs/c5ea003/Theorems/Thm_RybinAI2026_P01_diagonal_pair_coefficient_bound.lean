-- Prove2me | Theorems.Thm_RybinAI2026_P01_diagonal_pair_coefficient_bound
-- name    : RybinAI2026.P01.diagonal_pair_coefficient_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T22:22:59.882448+00:00
-- url     : https://prove2.me/theorems/41660faf-4814-4d85-af4b-a8565811e287
-- title:
--   Scalar coefficient bound for diagonal pair contraction
-- statement:
--   For x and y in [0,1], nonnegative A and B satisfying A²=x(1-y) and B²=y(1-x), and z≥0, the quadratic expression (x+Az)²+(B+yz)² is at most (1+z)². This is the final scalar coefficient estimate in the aligned diagonal 2D pair-contraction proof.
-- source:
--   Final coefficient estimate from the aligned diagonal 2D pair-contraction argument in artifacts/p01_slack/2026-09-29-no-w-pair.md.

import Mathlib

theorem RybinAI2026.P01.diagonal_pair_coefficient_bound {x y A B z : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hA : A ^ 2 = x * (1 - y)) (hB : B ^ 2 = y * (1 - x)) (hz : 0 ≤ z) :
    (x + A * z) ^ 2 + (B + y * z) ^ 2 ≤ (1 + z) ^ 2 := by
  sorry
