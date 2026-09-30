-- Prove2me | solution 2 for lean_workbook_plus_28716
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:42:14.559135+00:00
-- url     : https://prove2.me/submissions/f1a30f28-3745-4abd-90ee-3d7fb1cf75b5

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → 6 * a * b * c < a * b * (a + b) + b * c * (b + c) + c * a * (c + a) ∧ a * b * (a + b) + b * c * (b + c) + c * a * (c + a) < 2 * (a ^ 3 + b ^ 3 + c ^ 3)) := by
  intro h
  have bad := (h 1 1 1 (by norm_num)).1
  norm_num at bad

#print axioms solution
