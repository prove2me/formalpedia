-- Prove2me | solution 1 for lean_workbook_plus_75943
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:34:39.116514+00:00
-- url     : https://prove2.me/submissions/48619995-8f10-44ef-b897-3117dd35a200

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (t : ℝ) : 4 * t ^ 2 - 4 * t + 1 = 0 ↔ t = 1 / 2 := by
  intros
  grind
