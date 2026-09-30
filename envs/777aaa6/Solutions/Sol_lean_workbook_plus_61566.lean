-- Prove2me | solution 1 for lean_workbook_plus_61566
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:58:38.972144+00:00
-- url     : https://prove2.me/submissions/233ad78c-c8da-41b9-959f-a03b17a8cbee

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem cubic_sum_remainder (x y : ℝ) :
    4 * (x ^ 3 + y ^ 3) - 1 =
      (x + y - 1) * ((x + y) ^ 2 + (x + y) + 1) +
        3 * (x + y) * (x - y) ^ 2 := by
  ring

theorem cubic_sum_sharp_bound (x y : ℝ) (h : 1 ≤ x + y) :
    1 / 4 ≤ x ^ 3 + y ^ 3 := by
  have hs : 0 ≤ x + y := by linarith
  have hq : 0 ≤ (x + y) ^ 2 + (x + y) + 1 := by
    nlinarith [sq_nonneg (x + y)]
  have hleft := mul_nonneg (sub_nonneg.mpr h) hq
  have hright := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hs)
    (sq_nonneg (x - y))
  nlinarith [cubic_sum_remainder x y]

theorem cubic_sum_minimum_iff (x y : ℝ) (h : 1 ≤ x + y) :
    x ^ 3 + y ^ 3 = 1 / 4 ↔ x = 1 / 2 ∧ y = 1 / 2 := by
  constructor
  · intro he
    have hs : 0 ≤ x + y := by linarith
    have hq : 0 < (x + y) ^ 2 + (x + y) + 1 := by
      nlinarith [sq_nonneg (x + y)]
    have hleft := mul_nonneg (sub_nonneg.mpr h) hq.le
    have hright := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hs)
      (sq_nonneg (x - y))
    have hz : (x + y - 1) * ((x + y) ^ 2 + (x + y) + 1) = 0 := by
      nlinarith [cubic_sum_remainder x y]
    have hsum : x + y = 1 := by
      rcases mul_eq_zero.mp hz with hz | hz
      · linarith
      · exact False.elim (hq.ne' hz)
    have hsq : (x - y) ^ 2 = 0 := by
      nlinarith [cubic_sum_remainder x y]
    have hd : x - y = 0 := sq_eq_zero_iff.mp hsq
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    ring

theorem solution (x y : ℝ) (h1 : x + y ≥ 1) (h2 : |x * y| ≤ 2) :
    x ^ 3 + y ^ 3 ≥ -7 := by
  linarith [cubic_sum_sharp_bound x y h1]

#print axioms solution
#print axioms cubic_sum_minimum_iff
