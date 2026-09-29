-- Prove2me | solution 1 for lean_workbook_plus_65615
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:08:14.914407+00:00
-- url     : https://prove2.me/submissions/916d890f-e395-41e7-82e9-24c212e52548

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) (hx: x ≠ 0) (t : ℝ) (ht : t = x - 12/x) : t^2 + 24 = 10*t ↔ t = 4 ∨ t = 6 := by
  intros
  grind
