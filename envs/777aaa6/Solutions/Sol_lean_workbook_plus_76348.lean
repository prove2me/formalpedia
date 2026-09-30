-- Prove2me | solution 1 for lean_workbook_plus_76348
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:06:43.071163+00:00
-- url     : https://prove2.me/submissions/0746f639-6c7a-4231-8f89-44ba27632eb7

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (x y z : ℝ) :
    x^2*(1+y^2)*(1+z^2)+y^2*z^2+2 ≥ 2*x*(y+z)+2*y*z := by
  nlinarith only [sq_nonneg (x*(y+z)-1), sq_nonneg (x*(y*z-1)),
    sq_nonneg (y*z-1)]
