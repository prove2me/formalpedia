-- Prove2me | solution 1 for lean_workbook_plus_49288
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:48:34.170985+00:00
-- url     : https://prove2.me/submissions/74515e55-f59a-4d86-943c-c4817e133f31

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : (x ≥ 0 → |x| = x) ∧ (x < 0 → |x| = -x) := by
  intros
  grind
