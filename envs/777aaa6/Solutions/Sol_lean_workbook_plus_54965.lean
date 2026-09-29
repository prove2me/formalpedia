-- Prove2me | solution 1 for lean_workbook_plus_54965
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:02:10.567492+00:00
-- url     : https://prove2.me/submissions/97917251-7500-4835-9ee8-b9d8bb589aa1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a^2+b^2+c^2 + (a+b+c)^2 = (a+b)^2 + (b+c)^2 + (c+a)^2 := by
  (intros; linarith)
