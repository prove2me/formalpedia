-- Prove2me | solution 1 for lean_workbook_plus_71475
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:51:54.510519+00:00
-- url     : https://prove2.me/submissions/52ff4431-3ddd-45ef-b0c6-71082f66595a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (m : ℝ)
  (h₀ : 30 + 1.75 * m = 59.75) :
  m = 17 := by
  (intros; linarith)
