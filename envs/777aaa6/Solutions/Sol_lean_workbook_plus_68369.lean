-- Prove2me | solution 1 for lean_workbook_plus_68369
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:18:09.179232+00:00
-- url     : https://prove2.me/submissions/2f0f404e-cc9f-4988-911f-a51e6e8f14a9

import Mathlib
set_option autoImplicit false

theorem solution (a A B : ℝ) (ha : a = 10^1965) (hA : A = (a + 1) / (10 * a + 1)) (hB : B = (10 * a + 1) / (100 * a + 1)) : A > B   := by
  have ha_pos : 0 < a := by
    rw [ha]
    positivity
  rw [hA, hB]
  apply (div_lt_div_iff₀ (by positivity : 0 < 100 * a + 1)
    (by positivity : 0 < 10 * a + 1)).2
  nlinarith only [ha_pos]

#print axioms solution
