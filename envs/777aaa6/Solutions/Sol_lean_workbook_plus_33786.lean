-- Prove2me | solution 1 for lean_workbook_plus_33786
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:36:03.318876+00:00
-- url     : https://prove2.me/submissions/28aad738-7f07-4cce-97cd-e382890fdf9d

import Mathlib
set_option autoImplicit false

theorem solution {a b c p : ℝ} (h : a + b + c = 2 * p) :
  a * (p - b) * (p - c) * (b ^ 2 - c ^ 2) + b * (p - c) * (p - a) * (c ^ 2 - a ^ 2) +
      c * (p - a) * (p - b) * (a ^ 2 - b ^ 2) = -p ^ 2 * (a - b) * (b - c) * (c - a)   := by
  have hp : p = (a + b + c) / 2 := by linarith [h]
  rw [hp]
  ring

#print axioms solution
