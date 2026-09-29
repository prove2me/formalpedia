-- Prove2me | solution 1 for lean_workbook_plus_44088
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:16:43.100144+00:00
-- url     : https://prove2.me/submissions/56ab7d1c-16c5-4f31-a22e-65bc15b91e89

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x ≥ 0, (663*x^4 - 620*x^3 - 790*x^2 + 284*x + 503) > 0 := by
  norm_num
