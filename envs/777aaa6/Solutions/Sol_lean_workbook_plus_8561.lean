-- Prove2me | solution 1 for lean_workbook_plus_8561
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:58:07.565903+00:00
-- url     : https://prove2.me/submissions/fc628248-8baf-484b-b31c-a3fff2ad0ada

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p : ℝ)
  (h₀ : 100 * p = 1 + 1 - p + 10 - 10 * p) :
  p = 4 / 37 := by
  (intros; linarith)
