-- Prove2me | solution 1 for lean_workbook_plus_76166
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:31:57.159062+00:00
-- url     : https://prove2.me/submissions/689bbc02-254a-403b-8dd5-41d5fb716f4b

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem cleared_gap_lower_bound (x : ℝ) (hx : 1 ≤ x) :
    1 ≤ (x - 3) * ((x - 1) * (x + 1) ^ 3) + 4 * x ^ 3 := by
  let t := x - 1
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hid : (x - 3) * ((x - 1) * (x + 1) ^ 3) + 4 * x ^ 3 =
      t * (t ^ 2 + 2 * t - 2) ^ 2 + 4 * t * (t - 1) ^ 2 +
        12 * (t - 1 / 2) ^ 2 + 1 := by dsimp [t]; ring
  rw [hid]
  have h₁ := mul_nonneg ht (sq_nonneg (t ^ 2 + 2 * t - 2))
  have h₂ := mul_nonneg ht (sq_nonneg (t - 1))
  nlinarith [sq_nonneg (t - 1 / 2)]

theorem solution (x : ℝ) (hx : 1 < x) :
    x + 4 * x ^ 3 / ((x - 1) * (x + 1) ^ 3) > 3 := by
  have hd : 0 < (x - 1) * (x + 1) ^ 3 :=
    mul_pos (by linarith) (pow_pos (by linarith) _)
  have hg := cleared_gap_lower_bound x hx.le
  have hc : (3 - x) * ((x - 1) * (x + 1) ^ 3) < 4 * x ^ 3 := by
    nlinarith only [hg]
  have := (lt_div_iff₀ hd).mpr hc
  linarith
