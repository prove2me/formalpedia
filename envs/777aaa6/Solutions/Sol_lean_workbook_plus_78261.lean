-- Prove2me | solution 1 for lean_workbook_plus_78261
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:13:26.826306+00:00
-- url     : https://prove2.me/submissions/0b85ab1e-6d05-4c01-91e0-29782fdad142

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y + y * z + z * x ≤ x * y * z) :
    x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 ≥
      9 * (x * y + y * z + z * x) := by
  set s := x + y + z
  set q := x * y + y * z + z * x
  set p := x * y * z
  have hs : 0 < s := by dsimp [s]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hpq : q ≤ p := h
  have hsq : 3 * q ≤ s ^ 2 := by
    dsimp [s, q]
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have hqp : 3 * p * s ≤ q ^ 2 := by
    dsimp [s, q, p]
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x),
      sq_nonneg (z * x - x * y)]
  have hqs : 3 * s ≤ q := by
    have hm : 0 ≤ (p - q) * s := mul_nonneg (sub_nonneg.mpr hpq) hs.le
    have hn : 0 ≤ q * (q - 3 * s) := by nlinarith
    have := nonneg_of_mul_nonneg_right hn hq
    linarith
  have hs9 : 9 ≤ s := by
    have hn : 0 ≤ s * (s - 9) := by nlinarith
    have := nonneg_of_mul_nonneg_right hn hs
    linarith
  have hq27 : 27 ≤ q := by linarith
  have ht : q ^ 2 ≤ 3 * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2) := by
    dsimp [q]
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x),
      sq_nonneg (z * x - x * y)]
  have hm : 0 ≤ q * (q - 27) := mul_nonneg hq.le (by linarith)
  change 9 * q ≤ _
  nlinarith

#print axioms solution
