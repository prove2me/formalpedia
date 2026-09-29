-- Prove2me | solution 1 for lean_workbook_plus_14292
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:51:43.301946+00:00
-- url     : https://prove2.me/submissions/f0541800-3629-4138-9bbc-1926e8509617

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (p s X Y Z R : ℤ) (hX : X = s * (9 * p ^ 2 + 9 * p * s + 10 * s ^ 2)) (hY : Y = s * (6 * p ^ 2 + 12 * p * s + 7 * s ^ 2)) (hZ : Z = 3 * p ^ 3 + 3 * p ^ 2 * s + 15 * p * s ^ 2 + 7 * s ^ 3) (hR : R = 3 * (p + 2 * s) * (p ^ 2 - p * s + s ^ 2)) : X ^ 3 + Y ^ 3 + Z ^ 3 - 3 * X * Y * Z = R ^ 3 := by
  intros
  grind
