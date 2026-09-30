-- Prove2me | solution 1 for lean_workbook_plus_82142
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:37:41.48621+00:00
-- url     : https://prove2.me/submissions/93e04745-51e7-43a8-b60d-5517d5e930b8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

theorem solution (x y z : ℝ) :
    (x^2*y^2 + y^2*z^2 + z^2*x^2)^2 ≥ (x*y + y*z + z*x)^4 / 9 := by
  have hcs : (x*y + y*z + z*x)^2 ≤ 3*(x^2*y^2 + y^2*z^2 + z^2*x^2) := by
    nlinarith [sq_nonneg (x*y-y*z), sq_nonneg (y*z-z*x), sq_nonneg (z*x-x*y)]
  have hn : 0 ≤ 3*(x^2*y^2 + y^2*z^2 + z^2*x^2) := by positivity
  have hsq := (sq_le_sq₀ (sq_nonneg (x*y+y*z+z*x)) hn).mpr hcs
  nlinarith only [hsq]
