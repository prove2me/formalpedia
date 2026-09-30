-- Prove2me | solution 2 for lean_workbook_plus_30714
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:54:46.509073+00:00
-- url     : https://prove2.me/submissions/c9c4223f-b3f3-45d9-8201-400290cb7e27

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℕ → ℝ) (hx : x 1 = 0 ∧ x 2 = -5 ∧ x 3 = -2) : x 1 = 0 ∧ x 2 = -5 ∧ x 3 = -2 := by
  (intros; simp_all)
