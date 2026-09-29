-- Prove2me | solution 1 for lean_workbook_plus_32736
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:16:25.594164+00:00
-- url     : https://prove2.me/submissions/30b67406-b1b1-427d-844f-6e6163557a28

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) : (a + b + c) ^ 2 ≥ 2 * (a + b + c) + a * b + b * c + c * a ↔ a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a ≥ 2 * (a + b + c) := by
  intros
  grind
