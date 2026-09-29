-- Prove2me | solution 1 for lean_workbook_plus_4705
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:46:43.530486+00:00
-- url     : https://prove2.me/submissions/f7f82bc0-a3f7-4c7d-90f2-556a06cd0395

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (m n : ℝ) : 2 * (m ^ 2 - n ^ 2) ≥ 3 * m * n ↔ (2 * m + n) * (m - 2 * n) ≥ 0 := by
  intros
  grind
