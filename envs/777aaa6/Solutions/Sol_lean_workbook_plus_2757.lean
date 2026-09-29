-- Prove2me | solution 1 for lean_workbook_plus_2757
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:52:09.444517+00:00
-- url     : https://prove2.me/submissions/dc38e008-c63b-4794-97ac-3ab5a1d4e0ef

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℤ) : (n+2)^3+20*(n+2)-n^3-20*n = 6*n*(n+2) + 48 := by
  (intros; linarith)
