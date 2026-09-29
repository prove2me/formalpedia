-- Prove2me | solution 1 for lean_workbook_plus_82039
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:36:01.22898+00:00
-- url     : https://prove2.me/submissions/7b8a3e55-e315-444c-b742-44fd4c709a19

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (k : ℝ) (y : ℝ) : ∃ E, E = 1/2 * k * y^2 := by
  norm_num
