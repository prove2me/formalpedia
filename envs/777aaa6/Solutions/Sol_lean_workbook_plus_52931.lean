-- Prove2me | solution 1 for lean_workbook_plus_52931
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:03:43.662967+00:00
-- url     : https://prove2.me/submissions/be3be8c6-83b7-4f8a-b825-f27a74e57828

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ)
  (h₀ : 9 * a = -3) :
  7 * a = -7 / 3 := by
  (intros; linarith)
