-- Prove2me | solution 1 for lean_workbook_plus_29795
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:04:01.385754+00:00
-- url     : https://prove2.me/submissions/53bac6bc-6bc4-4d0f-8381-1bd8c582354e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (k : ℝ)
  (h₀ : (2 * k - 1) / 16 = 0) :
  k = 1 / 2 := by
  (intros; linarith)
