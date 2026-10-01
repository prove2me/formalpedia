-- Prove2me | solution 1 for P01Slope.slope_harmonic_superadditive
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:10:43.500783+00:00
-- url     : https://prove2.me/submissions/1068318d-35c8-4942-bc43-0b8b179f8c76

import Mathlib

theorem solution (p0 p1 q0 q1 : ℝ)
    (hp0 : 0 < p0) (hq0 : 0 < q0) (hp1 : p1 ^ 2 < p0 ^ 2) (hq1 : q1 ^ 2 < q0 ^ 2) :
    (p0 ^ 2 - p1 ^ 2) / p0 + (q0 ^ 2 - q1 ^ 2) / q0 ≤
      ((p0 + q0) ^ 2 - (p1 + q1) ^ 2) / (p0 + q0) := by
  have hs : 0 < p0 + q0 := add_pos hp0 hq0
  have hgap : ((p0 + q0) ^ 2 - (p1 + q1) ^ 2) / (p0 + q0) -
      ((p0 ^ 2 - p1 ^ 2) / p0 + (q0 ^ 2 - q1 ^ 2) / q0) =
      (p1 * q0 - q1 * p0) ^ 2 / (p0 * q0 * (p0 + q0)) := by
    field_simp
    <;> ring
  have hn : 0 ≤ (p1 * q0 - q1 * p0) ^ 2 / (p0 * q0 * (p0 + q0)) :=
    div_nonneg (sq_nonneg _) (le_of_lt (mul_pos (mul_pos hp0 hq0) hs))
  linarith
