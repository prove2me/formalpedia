-- Prove2me | solution 1 for lean_workbook_plus_16769
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:44:14.977445+00:00
-- url     : https://prove2.me/submissions/0f083b19-17d6-4767-9899-720848e385f1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (d e : ℤ) : (d^4+e^4)-(d+e)*(d^3+e^3)+d*e*(d^2+e^2)=0 := by
  (intros; linarith)
