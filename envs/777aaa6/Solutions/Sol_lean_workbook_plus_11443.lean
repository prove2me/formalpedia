-- Prove2me | solution 1 for lean_workbook_plus_11443
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:48:15.750705+00:00
-- url     : https://prove2.me/submissions/93254620-9f6c-40ef-8fc4-b5add73fc2ed

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : 3*x + 5*y + 7*z = 10) (h' : x + 2*y + 5*z = 6) : 2*x - 3*y + 4*z ≤ 6 := by
  (intros; linarith)
