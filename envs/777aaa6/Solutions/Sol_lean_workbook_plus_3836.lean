-- Prove2me | solution 1 for lean_workbook_plus_3836
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:51:18.596699+00:00
-- url     : https://prove2.me/submissions/6524ac5c-c9ad-4b64-bf6d-c924926c3cde

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℤ) : x^4 + 4*y^4 = (x^2 + 2*y^2 + 2*x*y) * (x^2 + 2*y^2 - 2*x*y) := by
  (intros; linarith)
