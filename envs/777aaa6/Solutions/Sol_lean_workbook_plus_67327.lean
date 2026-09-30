-- Prove2me | solution 1 for lean_workbook_plus_67327
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:57:38.014578+00:00
-- url     : https://prove2.me/submissions/2aa7b69d-f379-48c4-9618-2db84864155f

import Mathlib
set_option autoImplicit false

theorem solution (x y : ℝ) (hx : -1 < x ∧ x < 1) (hy : -1 < y ∧ y < 1) : -1 < (x + y) / (1 + x * y) ∧ (x + y) / (1 + x * y) < 1   := by
  have hm : 0 < (1 - x) * (1 - y) :=
    mul_pos (sub_pos.mpr hx.2) (sub_pos.mpr hy.2)
  have hp : 0 < (1 + x) * (1 + y) :=
    mul_pos (by linarith only [hx.1]) (by linarith only [hy.1])
  have hd : 0 < 1 + x * y := by nlinarith only [hm, hp]
  constructor
  · apply (lt_div_iff₀ hd).2
    nlinarith only [hp]
  · apply (div_lt_iff₀ hd).2
    nlinarith only [hm]

#print axioms solution
