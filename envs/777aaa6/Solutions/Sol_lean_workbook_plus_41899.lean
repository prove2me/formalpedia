-- Prove2me | solution 1 for lean_workbook_plus_41899
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:58:23.499058+00:00
-- url     : https://prove2.me/submissions/87cae1e0-bf8b-4663-8faf-8133915e0fe9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℝ) : x / (y / z) = x * (z / y) := by
  intros
  grind
