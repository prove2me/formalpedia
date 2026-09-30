-- Prove2me | solution 1 for lean_workbook_plus_52998
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:38:22.830871+00:00
-- url     : https://prove2.me/submissions/0255b8be-ee07-48fc-a19c-9c09087df70c

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx : 0 ≤ x) : (1 + x ^ 2) ^ 3 / (1 + x) ^ 3 ≥ (1 + x ^ 3) / 2   := by
  have hx1 : 0 < 1 + x := by linarith
  have hd : 0 < 2 * (1 + x)^3 := by positivity
  have hn : 0 ≤ (x - 1)^4 * (x^2 + x + 1) := by positivity
  have hgap : 0 ≤ (x - 1)^4 * (x^2 + x + 1) / (2 * (1 + x)^3) :=
    div_nonneg hn hd.le
  have hid : (1 + x^2)^3 / (1 + x)^3 - (1 + x^3) / 2 =
      (x - 1)^4 * (x^2 + x + 1) / (2 * (1 + x)^3) := by
    field_simp [hx1.ne'] <;> ring
  linarith only [hgap, hid]

#print axioms solution
