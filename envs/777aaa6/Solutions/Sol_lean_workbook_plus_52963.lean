-- Prove2me | solution 1 for lean_workbook_plus_52963
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:38:24.05191+00:00
-- url     : https://prove2.me/submissions/2ef3a01b-cff7-411a-9a8a-db114d57e5ed

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 1/a + a/b = 4) : a + b/a ≥ 1   := by
  have hd : 0 < a^2 * b := mul_pos (by positivity) hb
  have hgap : 0 ≤ (a^2 - b)^2 / (a^2 * b) :=
    div_nonneg (sq_nonneg _) hd.le
  have hid : (a + b / a) * (1 / a + a / b) - 4 =
      (a^2 - b)^2 / (a^2 * b) := by
    field_simp [ha.ne', hb.ne'] <;> ring
  rw [hab] at hid
  linarith only [hgap, hid]

#print axioms solution
