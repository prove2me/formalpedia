-- Prove2me | solution 1 for lean_workbook_plus_64084
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:50:04.626935+00:00
-- url     : https://prove2.me/submissions/814fd108-715b-4aa5-aac4-9f29dcf0d751

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (h₁ : 2 * f 0 = 4 * f 0) : f 0 = 0 := by
  (intros; simp_all)
