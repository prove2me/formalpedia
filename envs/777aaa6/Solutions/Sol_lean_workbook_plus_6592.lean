-- Prove2me | solution 1 for lean_workbook_plus_6592
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:49:43.875981+00:00
-- url     : https://prove2.me/submissions/8d3c0b62-25f6-4bcc-b645-56012f1e7cd5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ): f '' Set.univ = {0} → ∀ x, f x = 0 := by
  norm_num
