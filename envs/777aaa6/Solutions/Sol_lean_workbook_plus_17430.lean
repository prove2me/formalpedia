-- Prove2me | solution 1 for lean_workbook_plus_17430
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:13:30.010359+00:00
-- url     : https://prove2.me/submissions/5ada4eb7-1515-4817-9ee8-7cc1445995c9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∃ y, (∑' k : ℕ, (1:ℝ) / 2 ^ k) = y := by
  norm_num
