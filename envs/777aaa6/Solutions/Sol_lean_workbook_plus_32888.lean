-- Prove2me | solution 1 for lean_workbook_plus_32888
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:05:58.490011+00:00
-- url     : https://prove2.me/submissions/76538482-ff50-40a2-8aa9-7b7860036029

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (1+a^2)*(1+b^2)*(1+c^2) = (a+b+c-(a*b*c))^2 + (a*b+b*c+c*a-1)^2 := by
  (intros; linarith)
