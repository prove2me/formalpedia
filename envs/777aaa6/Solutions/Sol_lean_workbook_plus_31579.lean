-- Prove2me | solution 1 for lean_workbook_plus_31579
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:21:51.889808+00:00
-- url     : https://prove2.me/submissions/ef77378a-8c21-438e-a034-4a7242240fce

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {x y z T1 T2 T3 : ℝ} (hx : x + y + z = T1) (hy : x*y + y*z + z*x = T2) (hz : x*y*z = T3) : (x - y) ^ 2 * (y - z) ^ 2 * (z - x) ^ 2 = T1 ^ 2 * T2 ^ 2 + 18*T1*T2*T3 - 4*T1 ^ 3 * T3 - 4*T2 ^ 3 - 27*T3 ^ 2 := by
  intros
  grind
