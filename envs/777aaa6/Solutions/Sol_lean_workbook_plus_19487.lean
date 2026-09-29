-- Prove2me | solution 1 for lean_workbook_plus_19487
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:12:21.12486+00:00
-- url     : https://prove2.me/submissions/228833ba-d201-46e5-b1de-02161d2923c8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℝ) (h1 : x + y + z = 0) (h2 : x*y + y*z + z*x = -3) : x^3*y + y^3*z + z^3*x = -9 := by
  intros
  grind
