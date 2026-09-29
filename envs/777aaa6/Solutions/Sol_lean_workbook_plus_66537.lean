-- Prove2me | solution 1 for lean_workbook_plus_66537
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:32:31.84118+00:00
-- url     : https://prove2.me/submissions/e7a99cfb-6b9f-4961-8b7a-83d61493e123

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (s : ℝ)
  (h₀ : 2 * s = 150 * (20 + 1)) :
  s = 1575 := by
  (intros; linarith)
