-- Prove2me | solution 1 for lean_workbook_plus_53745
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:05:56.429534+00:00
-- url     : https://prove2.me/submissions/9416bd75-8343-4f41-8ab1-5c4b19382745

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z : ℝ) :
  2 * (x^2 + y^2) * (y^2 + z^2) * (z^2 + x^2) ≥ (x * y * (x + y) + y * z * (y + z) + z * x * (z + x) - 2 * x * y * z)^2 := by
  nlinarith only [sq_nonneg ((x-y)*(x*y+z^2)-(x+y)*z*(x-y))]
