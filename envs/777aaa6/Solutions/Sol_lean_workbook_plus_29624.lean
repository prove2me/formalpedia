-- Prove2me | solution 1 for lean_workbook_plus_29624
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:25:42.796802+00:00
-- url     : https://prove2.me/submissions/9b0995de-24b8-446f-8566-4c6f20b9f324

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 4/3 ≤ a) (hb : 4/3 ≤ b) (hc : 4/3 ≤ c) : a + b + c ≥ (8/5) * (2/a - 1/b + 1/c + 1)   := by
  have ha0 : 0 < a := by linarith only [ha]
  have hb0 : 0 < b := by linarith only [hb]
  have hc0 : 0 < c := by linarith only [hc]
  have hap : 0 ≤ (3*a-4)*(5*a+12) :=
    mul_nonneg (by linarith only [ha]) (by linarith only [ha])
  have hbp : 0 ≤ (3*b-4)*(5*b-6) :=
    mul_nonneg (by linarith only [hb]) (by linarith only [hb])
  have hcp : 0 ≤ (3*c-4)*(5*c+6) :=
    mul_nonneg (by linarith only [hc]) (by linarith only [hc])
  have hid : a+b+c - (8/5)*(2/a-1/b+1/c+1) =
      (3*a-4)*(5*a+12)/(15*a) + (3*b-4)*(5*b-6)/(15*b) +
      (3*c-4)*(5*c+6)/(15*c) := by
    field_simp [ne_of_gt ha0, ne_of_gt hb0, ne_of_gt hc0]
    <;> ring
  apply sub_nonneg.mp
  rw [hid]
  exact add_nonneg
    (add_nonneg (div_nonneg hap (le_of_lt (mul_pos (by norm_num) ha0)))
      (div_nonneg hbp (le_of_lt (mul_pos (by norm_num) hb0))))
    (div_nonneg hcp (le_of_lt (mul_pos (by norm_num) hc0)))

#print axioms solution
