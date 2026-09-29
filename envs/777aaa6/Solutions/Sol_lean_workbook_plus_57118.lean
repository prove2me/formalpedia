-- Prove2me | solution 1 for lean_workbook_plus_57118
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:08:06.556144+00:00
-- url     : https://prove2.me/submissions/5fda3595-3a20-467b-89b0-ecf4bf42a029

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : -4 + x / 2013 = x / 671 ↔ x = -4026 := by
  intros
  grind
