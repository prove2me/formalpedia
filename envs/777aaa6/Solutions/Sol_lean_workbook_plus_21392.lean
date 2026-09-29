-- Prove2me | solution 1 for lean_workbook_plus_21392
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:46:04.923376+00:00
-- url     : https://prove2.me/submissions/b7b14e42-0883-4f65-a68e-e9a917053b8e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx: x > 0 ∧ y > 0 ∧ z > 0 ∧ x*y*z = 2 ∧ x + y + z = 2):  x*y + y*z + z*x >= 2*(x + y + z) ∧ Real.sqrt x + Real.sqrt y + Real.sqrt z <= (3*Real.sqrt (x*y*z))/2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
