-- Prove2me | solution 1 for lean_workbook_plus_21236
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:36:15.055284+00:00
-- url     : https://prove2.me/submissions/2458a89d-0d58-486d-918a-5537060e8c07

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℕ) (u v : Fin n → ℝ) :
  4 * (∑ i, u i * v i - 1 / 2) ^ 2 ≥ 0 := by
  (intros; positivity)
