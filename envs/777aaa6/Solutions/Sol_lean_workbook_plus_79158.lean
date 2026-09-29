-- Prove2me | solution 1 for lean_workbook_plus_79158
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:26:49.085109+00:00
-- url     : https://prove2.me/submissions/87a77e23-c55b-4c25-afbe-232db6547629

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x>0 ∧ y>0 ∧ z>0 ∧ x*y*z=1) : x^4 + y^4 + z^4 >= x + y + z := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
