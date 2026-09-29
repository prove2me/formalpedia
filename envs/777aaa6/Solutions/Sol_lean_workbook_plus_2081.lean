-- Prove2me | solution 1 for lean_workbook_plus_2081
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:35:20.052972+00:00
-- url     : https://prove2.me/submissions/3be521d3-f6f1-4ff5-b7a9-4b304ed9936e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (t : ℝ) : t * (t - 1) * (t + 2) * (19 * t - 30) = 0 ↔ t = 0 ∨ t = 1 ∨ t = -2 ∨ t = 30 / 19 := by
  intros
  grind
