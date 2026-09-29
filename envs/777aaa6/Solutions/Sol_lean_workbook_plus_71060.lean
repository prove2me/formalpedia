-- Prove2me | solution 1 for lean_workbook_plus_71060
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:53:12.226931+00:00
-- url     : https://prove2.me/submissions/d8ac3c67-22c8-4823-8755-f943defc2e2d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) = (a + b + c - a * b * c)^2 + (a * b + b * c + c * a - 1)^2 := by
  (intros; linarith)
