-- Prove2me | solution 1 for lean_workbook_plus_61846
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:08:54.122769+00:00
-- url     : https://prove2.me/submissions/4e928385-7b7f-43de-a5cc-eb8410a4016d

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (a - b) * (c - a) * (b - c) < a * b * c   := by
  have h1 : |a - b| < c := abs_lt.mpr ⟨by linarith only [hca], by linarith only [hbc]⟩
  have h2 : |c - a| < b := abs_lt.mpr ⟨by linarith only [hbc], by linarith only [hab]⟩
  have h3 : |b - c| < a := abs_lt.mpr ⟨by linarith only [hab], by linarith only [hca]⟩
  have h12 : |a - b| * |c - a| < c * b := calc
    |a - b| * |c - a| ≤ |a - b| * b :=
      mul_le_mul_of_nonneg_left h2.le (abs_nonneg _)
    _ < c * b := mul_lt_mul_of_pos_right h1 hx.2.1
  calc
    (a - b) * (c - a) * (b - c) ≤ |(a - b) * (c - a) * (b - c)| := le_abs_self _
    _ = |a - b| * |c - a| * |b - c| := by rw [abs_mul, abs_mul]
    _ ≤ (|a - b| * |c - a|) * a :=
      mul_le_mul_of_nonneg_left h3.le (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ < (c * b) * a := mul_lt_mul_of_pos_right h12 hx.1
    _ = a * b * c := by ring

#print axioms solution
