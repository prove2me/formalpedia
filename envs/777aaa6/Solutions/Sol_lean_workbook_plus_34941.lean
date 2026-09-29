-- Prove2me | solution 1 for lean_workbook_plus_34941
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:17:42.22587+00:00
-- url     : https://prove2.me/submissions/3327b300-8848-449b-a74e-2ca8023225fc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a^3 + b^3 + c^3 - 3*a*b*c = (a + b + c)*(a^2 + b^2 + c^2 - a*b - a*c - b*c) := by
  (intros; linarith)
