-- Prove2me | solution 1 for lean_workbook_plus_68965
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:13:13.90723+00:00
-- url     : https://prove2.me/submissions/bd7f0ee6-6e75-4f90-acc3-5fb926c298c1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℝ) : (x + y + z - x * y - x * z - y * z) ≤ 1 ↔ (1 - x) * (1 - y) * (1 - z) + x * y * z ≥ 0 := by
  intros
  grind
