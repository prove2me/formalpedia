-- Prove2me | solution 1 for lean_workbook_plus_76084
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:05:04.636575+00:00
-- url     : https://prove2.me/submissions/041e766e-934b-4bef-b3ad-6c5473c04003

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

private theorem constraint_bound (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 + a * b * c = 4) :
    3 * Real.sqrt (a * b * c) * (a + b + c) ≤ 8 + a * b * c := by
  have hfactor : (c + 2) * (a * b + c - 2) ≤ 0 := by
    nlinarith only [h, sq_nonneg (a - b)]
  have hab : a * b + c - 2 ≤ 0 := by
    by_contra hh
    have hp := mul_pos (by linarith : 0 < c + 2) (lt_of_not_ge hh)
    linarith only [hfactor, hp]
  have hscaled := mul_le_mul_of_nonneg_right hab hc.le
  let p : ℝ := a * b * c
  have hp : 0 < p := mul_pos (mul_pos ha hb) hc
  have hp1 : p ≤ 1 := by
    dsimp [p]
    nlinarith only [hscaled, sq_nonneg (c - 1)]
  have hsum : (a + b + c)^2 ≤ 3 * (4 - p) := by
    dsimp [p]
    nlinarith only [h, sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have hsqrt := Real.sq_sqrt hp.le
  have hleft : 0 ≤ 3 * Real.sqrt p * (a + b + c) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg p)) (by linarith)
  change 3 * Real.sqrt p * (a + b + c) ≤ 8 + p
  apply (sq_le_sq₀ hleft (by linarith : 0 ≤ 8 + p)).1
  have hid : (3 * Real.sqrt p * (a + b + c))^2 = 9 * p * (a + b + c)^2 := by
    rw [mul_pow, mul_pow, hsqrt]
    ring
  rw [hid]
  have hm := mul_le_mul_of_nonneg_left hsum (by linarith : 0 ≤ 9 * p)
  have hrem : 0 ≤ (1 - p) * (16 - 7 * p) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith only [hm, hrem]

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + a * b * c = 4) :
    3 * Real.sqrt (a * b * c) * (a + b + c) ≤ 8 + a * b * c :=
  constraint_bound a b c ha hb hc h
