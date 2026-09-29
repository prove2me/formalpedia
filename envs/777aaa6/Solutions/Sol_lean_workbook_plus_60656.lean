-- Prove2me | solution 1 for lean_workbook_plus_60656
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:00:26.374836+00:00
-- url     : https://prove2.me/submissions/7e66d4f4-e0a8-4744-ba83-2242013abe89

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p : ℝ)
  (h₀ : 0.85 * p - 90 = 0.75 * p - 15) :
  p = 750 := by
  (intros; linarith)
