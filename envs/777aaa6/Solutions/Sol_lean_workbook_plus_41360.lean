-- Prove2me | solution 1 for lean_workbook_plus_41360
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:05:40.44067+00:00
-- url     : https://prove2.me/submissions/316bdd5e-841a-42ce-b42a-e57897e3cb58

import Mathlib

set_option autoImplicit false

theorem solution {a b c : ℤ} (h : a + b + c = 0) :
    a ^ 3 * b + b ^ 3 * c + c ^ 3 * a = -(a ^ 2 + a * b + b ^ 2) ^ 2 := by
  have hc : c = -(a + b) := by omega
  rw [hc]
  ring

#print axioms solution
