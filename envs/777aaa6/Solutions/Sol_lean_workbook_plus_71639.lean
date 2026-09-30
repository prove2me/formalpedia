-- Prove2me | solution 1 for lean_workbook_plus_71639
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:34:53.789226+00:00
-- url     : https://prove2.me/submissions/6f9117e9-79ed-4760-857c-00ba74fa5f32

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx : x ≠ 0) : (x+1) / x^2 = 1/x + 1/x^2 := by
  field_simp

#print axioms solution
