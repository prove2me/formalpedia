-- Prove2me | solution 1 for lean_workbook_plus_35494
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:42:38.94475+00:00
-- url     : https://prove2.me/submissions/1da6b3ed-9a24-43c1-8a98-c451008d90b9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (r : ℝ) (h : 12 * r = 603) : r = 201 / 4 := by
  (intros; linarith)
