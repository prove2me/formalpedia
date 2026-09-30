-- Prove2me | solution 1 for lean_workbook_plus_64429
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:54:24.206534+00:00
-- url     : https://prove2.me/submissions/4d9850d5-afb5-4309-9c1a-874444cec3f9

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) : a ≠ 0 ∧ b ≠ 0 → 1/a - 1/b = (b - a)/(a * b)   := by
  rintro ⟨ha, hb⟩
  field_simp [ha, hb]

#print axioms solution
