-- Prove2me | solution 1 for lean_workbook_plus_17443
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:46:44.313582+00:00
-- url     : https://prove2.me/submissions/3b3e0727-7a5b-45e7-a030-c14fa721b6db

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^3 + b^3 + c^3 < (a + b + c) * (a * b + b * c + c * a)   := by
  rcases hx with ⟨ha, hb, hc⟩
  have h1 : 0 ≤ a^2*(b+c-a) := mul_nonneg (sq_nonneg a) (le_of_lt (sub_pos.mpr hbc))
  have h2 : 0 ≤ b^2*(a+c-b) := mul_nonneg (sq_nonneg b) (le_of_lt (sub_pos.mpr hca))
  have h3 : 0 ≤ c^2*(a+b-c) := mul_nonneg (sq_nonneg c) (le_of_lt (sub_pos.mpr hab))
  have hp : 0 < 3*a*b*c := mul_pos (mul_pos (mul_pos (by norm_num) ha) hb) hc
  have hg : 0 < a^2*(b+c-a)+b^2*(a+c-b)+c^2*(a+b-c)+3*a*b*c :=
    add_pos_of_nonneg_of_pos (add_nonneg (add_nonneg h1 h2) h3) hp
  nlinarith only [hg]

#print axioms solution
