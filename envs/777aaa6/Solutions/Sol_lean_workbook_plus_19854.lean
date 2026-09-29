-- Prove2me | solution 1 for lean_workbook_plus_19854
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:44:06.965189+00:00
-- url     : https://prove2.me/submissions/93b9e0d1-3319-4b97-9a5e-502968abb5c4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℤ) : (a+b+c)*(a*b+b*c+c*a)-a*b*c=(a+b)*(b+c)*(c+a) := by
  (intros; linarith)
