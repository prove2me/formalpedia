-- Prove2me | solution 1 for lean_workbook_plus_72779
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:19:24.911176+00:00
-- url     : https://prove2.me/submissions/94db1d74-831b-407b-8ecb-a779bd357980

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : x = 0) (h₂ : y = 0) : x^4 + y^4 = 0 := by
  (intros; simp_all)
