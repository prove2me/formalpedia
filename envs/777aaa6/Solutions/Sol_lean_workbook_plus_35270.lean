-- Prove2me | solution 1 for lean_workbook_plus_35270
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:17:44.412703+00:00
-- url     : https://prove2.me/submissions/5b99744c-bb75-4025-9ebd-13cda906d867

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 3^2 + 4^2 + 7^2 + 11^2 + 18^2 + 29^2 + 47^2 + 76^2 + 123^2 = 24474) : 3^2 + 4^2 + 7^2 + 11^2 + 18^2 + 29^2 + 47^2 + 76^2 + 123^2 = 24474 := by
  norm_num
