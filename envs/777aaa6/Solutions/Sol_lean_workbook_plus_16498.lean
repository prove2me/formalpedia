-- Prove2me | solution 1 for lean_workbook_plus_16498
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:50:32.225705+00:00
-- url     : https://prove2.me/submissions/0a923ad4-8bb1-45dc-9cf3-3040c3814b2b

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b) = 2 → a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b) = a + b + c)   := by
  rw [← add_halves (a + b + c)]
  intro h
  field_simp [ha.ne', hb.ne', hc.ne'] at h ⊢
  nlinarith

#print axioms solution
