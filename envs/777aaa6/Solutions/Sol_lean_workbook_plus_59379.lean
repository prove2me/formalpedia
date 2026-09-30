-- Prove2me | solution 1 for lean_workbook_plus_59379
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:16:29.947287+00:00
-- url     : https://prove2.me/submissions/f8f11d39-be94-49b9-b56c-1ed880237873

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

private theorem schur_nonneg (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ a * (a - b) * (a - c) + b * (b - c) * (b - a) + c * (c - a) * (c - b) := by
  by_cases hs : a + b + c = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    have hc0 : c = 0 := by linarith
    simp [ha0, hb0, hc0]
  · have hs0 : 0 < a + b + c := lt_of_le_of_ne (by positivity) (Ne.symm hs)
    have hf : 0 < a + (b + c) / 4 := by linarith
    have hp : 0 ≤ (a + (b + c) / 4) *
        (a * (a - b) * (a - c) + b * (b - c) * (b - a) + c * (c - a) * (c - b)) := by
      calc
        0 ≤ b * c * (b - c) ^ 2 +
            (c * a * (c - a) ^ 2 + a * b * (a - b) ^ 2) / 4 +
            (2 * a ^ 2 - b ^ 2 - c ^ 2 - a * b + 2 * b * c - c * a) ^ 2 / 4 := by
          positivity
        _ = _ := by ring
    exact nonneg_of_mul_nonneg_right hp hf

theorem cubic_constraint_sharp_sum (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a ^ 2 + b ^ 2 + c ^ 2 + a * b * c = 4) :
    a + b + c ≤ 3 ∧ (a + b + c = 3 ↔ a = 1 ∧ b = 1 ∧ c = 1) := by
  let s := a + b + c
  let p := a * b * c
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hvar : 0 ≤ 12 - 3 * p - s ^ 2 := by
    dsimp [p, s]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have hs4 : s < 4 := by nlinarith
  have hschur : 0 ≤ (9 - 2 * s) * p - s ^ 3 + 8 * s := by
    have hid : (9 - 2 * s) * p - s ^ 3 + 8 * s =
        (a * (a - b) * (a - c) + b * (b - c) * (b - a) + c * (c - a) * (c - b)) -
          2 * s * (a ^ 2 + b ^ 2 + c ^ 2 + a * b * c - 4) := by
      dsimp [p, s]
      ring
    rw [hid, h, sub_self, mul_zero, sub_zero]
    exact schur_nonneg a b c ha hb hc
  have hcubic : 0 ≤ 108 - 9 * s ^ 2 - s ^ 3 := by
    have hm := mul_nonneg (show 0 ≤ 9 - 2 * s by linarith) hvar
    nlinarith
  have hbound : s ≤ 3 := by
    by_contra! hs
    have hp := mul_pos (show 0 < s - 3 by linarith)
      (show 0 < s ^ 2 + 12 * s + 36 by positivity)
    nlinarith
  refine ⟨hbound, ?_⟩
  constructor
  · intro he
    have hsEq : s = 3 := he
    have hpEq : p = 1 := by
      rw [hsEq] at hvar hschur
      nlinarith
    have hQ : a ^ 2 + b ^ 2 + c ^ 2 = 3 := by
      dsimp [p] at hpEq
      linarith
    have ha2 : (a - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
    have hb2 : (b - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
    have hc2 : (c - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
    exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp ha2),
      sub_eq_zero.mp (sq_eq_zero_iff.mp hb2), sub_eq_zero.mp (sq_eq_zero_iff.mp hc2)⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

theorem solution (a b c : ℝ) (hpos : 0 < a ∧ 0 < b ∧ 0 < c)
    (habc : a * b * c = 1) (h : a ^ 2 + b ^ 2 + c ^ 2 + a * b * c = 4) :
    a + b + c ≤ 3 :=
  (cubic_constraint_sharp_sum a b c hpos.1.le hpos.2.1.le hpos.2.2.le h).1

#print axioms solution
#print axioms cubic_constraint_sharp_sum
