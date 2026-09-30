-- Prove2me | solution 1 for lean_workbook_plus_7400
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T19:47:32.606382+00:00
-- url     : https://prove2.me/submissions/4c12bdac-221e-404f-88e1-16f9d9963621

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (IsLeast {n : ℚ | 0 < n ∧ (n.den = 99)} (50/99)) := by
  intro h
  have hm : (1/99 : ℚ) ∈ {n : ℚ | 0 < n ∧ (n.den = 99)} := by
    constructor
    · norm_num
    · have hd : (((1/99 : ℚ).den : ℕ) : ℤ) = 99 := by
        simpa using Rat.den_div_eq_of_coprime (a := 1) (b := 99)
          (by norm_num) (by norm_num)
      exact_mod_cast hd
  have hb : (50/99 : ℚ) ≤ 1/99 := h.2 hm
  norm_num at hb

#print axioms solution
