-- Prove2me | solution 1 for lean_workbook_plus_63880
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:55:36.321736+00:00
-- url     : https://prove2.me/submissions/fe5c21c6-7d73-4fca-928d-877449bd6052

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : (a + b) / c + (b + c) / a + (c + a) / b = 26 / 3) : (a + b + c) * (a * b + b * c + c * a) ≥ 35 / 3 * a * b * c   := by
  field_simp at h ⊢
  nlinarith

#print axioms solution
