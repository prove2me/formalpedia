-- Prove2me | solution 1 for lean_workbook_plus_60479
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:53:13.469299+00:00
-- url     : https://prove2.me/submissions/fe6ece5e-f92e-41c2-bb47-d5b911a16013

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : y + |x - y + z| ≥ |x - y| + |y - z| := by
  intros
  grind
