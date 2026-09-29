-- Prove2me | solution 1 for lean_workbook_plus_1495
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:24:03.315909+00:00
-- url     : https://prove2.me/submissions/1ace50a4-d758-40e6-99fb-bda790218708

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : (a^2011+b^2011)*(a+b)-a*b*(a^2010+b^2010)=a^2012+b^2012 := by
  (intros; linarith)
