-- Prove2me | solution 1 for lean_workbook_plus_6091
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:06:50.184949+00:00
-- url     : https://prove2.me/submissions/03c7725c-11e3-4122-a13b-5b98cccfc9c0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hab : a + b + c = 1) : a + b = 1 - c := by
  (intros; linarith)
