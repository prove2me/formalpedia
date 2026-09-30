-- Prove2me | solution 1 for lean_workbook_plus_78621
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:57:33.079925+00:00
-- url     : https://prove2.me/submissions/ee2fea3f-5cba-4c80-9f5d-61e017c5ec3c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

private lemma paired_square_bound (S A M : ℝ) (hS : 0 ≤ S) (hA : 0 ≤ A)
    (hM1 : S ^ 2 ≤ M) (hM2 : A ^ 2 ≤ M) :
    4 * S ^ 2 * A ^ 2 ≤ (S + A) ^ 2 * M := by
  rcases le_total S A with h | h
  · have hc : 4 * S ^ 2 ≤ (S + A) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ A + 3 * S by linarith)]
    exact mul_le_mul hc hM2 (sq_nonneg A) (sq_nonneg (S + A))
  · have hc : 4 * A ^ 2 ≤ (S + A) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ S + 3 * A by linarith)]
    have hm := mul_le_mul hc hM1 (sq_nonneg S) (sq_nonneg (S + A))
    nlinarith only [hm]

theorem solution (t1 t2 : ℝ) (ht1 : 0 < t1) (ht2 : 0 < t2) :
    (t2 + 1) ^ 2 * (t1 + 1) ^ 2 * (1 + t1 ^ 2) * (1 + t2 ^ 2) ≥
      4 * (t1 + t2) ^ 2 * (1 + t1 * t2) ^ 2 := by
  have h1 : (t1 + t2) ^ 2 ≤ (1 + t1 ^ 2) * (1 + t2 ^ 2) := by
    nlinarith only [sq_nonneg (t1 * t2 - 1)]
  have h2 : (1 + t1 * t2) ^ 2 ≤ (1 + t1 ^ 2) * (1 + t2 ^ 2) := by
    nlinarith only [sq_nonneg (t1 - t2)]
  have h := paired_square_bound (t1 + t2) (1 + t1 * t2)
    ((1 + t1 ^ 2) * (1 + t2 ^ 2)) (by positivity) (by positivity) h1 h2
  calc
    4 * (t1 + t2) ^ 2 * (1 + t1 * t2) ^ 2 ≤
        (t1 + t2 + (1 + t1 * t2)) ^ 2 * ((1 + t1 ^ 2) * (1 + t2 ^ 2)) := h
    _ = (t2 + 1) ^ 2 * (t1 + 1) ^ 2 * (1 + t1 ^ 2) * (1 + t2 ^ 2) := by ring

#print axioms solution
