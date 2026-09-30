-- Prove2me | solution 1 for lean_workbook_plus_67683
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:28.083905+00:00
-- url     : https://prove2.me/submissions/d391667f-ddf3-47c2-9b8d-2bd130fb67e7

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (h : b * c * (a * b * c - 1) - a = 2) : a = (b * c + 2) / (b ^ 2 * c ^ 2 - 1)   := by
  have hm : a * (b ^ 2 * c ^ 2 - 1) = b * c + 2 := by nlinarith [h]
  have hd : b ^ 2 * c ^ 2 - 1 ≠ 0 := by
    intro hz
    have hb : b * c = -2 := by rw [hz] at hm; linarith
    have hs : (b * c) ^ 2 = 1 := by nlinarith [hz]
    rw [hb] at hs
    norm_num at hs
  exact (eq_div_iff hd).2 hm

#print axioms solution
