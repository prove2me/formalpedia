-- Prove2me | solution 1 for lean_workbook_plus_32289
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:25:59.890494+00:00
-- url     : https://prove2.me/submissions/b4aa4392-100f-4a04-8ae4-537f45260ebf

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) : a^4 + b^4 + 1 / 4 ≥ 2 * a * b * (1 - a * b) ↔ 4 * (a^2 - b^2)^2 + (4 * a * b - 1)^2 ≥ 0 := by
  intros
  grind
