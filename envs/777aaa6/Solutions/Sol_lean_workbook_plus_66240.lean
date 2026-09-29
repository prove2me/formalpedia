-- Prove2me | solution 1 for lean_workbook_plus_66240
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:32:03.009299+00:00
-- url     : https://prove2.me/submissions/c1766e72-15cd-4bb9-ab15-5a530c7f12a7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p q : ℝ) : p = (1 + Real.sqrt (q^3 + 5)) / 2 ↔ p = (1 + Real.sqrt (q^3 + 5)) / 2 := by
  norm_num
