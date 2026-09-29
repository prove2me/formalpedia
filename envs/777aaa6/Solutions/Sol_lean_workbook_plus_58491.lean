-- Prove2me | solution 1 for lean_workbook_plus_58491
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:45:03.277663+00:00
-- url     : https://prove2.me/submissions/d7f0d4c9-e808-4ca5-82a6-7118066f3abb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : x / 2 - 3 = 4) :
  x = 14 := by
  (intros; linarith)
