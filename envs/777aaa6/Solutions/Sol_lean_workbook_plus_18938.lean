-- Prove2me | solution 1 for lean_workbook_plus_18938
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:59:31.675979+00:00
-- url     : https://prove2.me/submissions/eef9c1c8-500b-47d5-a188-fb15c5f46ba4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (z w : ℂ) : ‖z + w‖ ≤ ‖z‖ + ‖w‖ := by
  intros
  exact?
