-- Prove2me | solution 1 for lean_workbook_plus_40703
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:34:14.322201+00:00
-- url     : https://prove2.me/submissions/1e3899dd-9e2e-4f35-bded-dbf858cff09f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℚ) (hx : x = 5 / 6) (hy : y = 4 / 5) (hz : z = 3 / 4) : x * y * z = 1 / 2 := by
  intros
  grind
