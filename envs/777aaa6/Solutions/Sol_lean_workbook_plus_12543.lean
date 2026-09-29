-- Prove2me | solution 1 for lean_workbook_plus_12543
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:07:06.538768+00:00
-- url     : https://prove2.me/submissions/166241f2-ec9a-4edd-945f-96c47afd7727

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (z1 z2 : ℂ) : ‖z1‖ + ‖z2‖ ≥ ‖z1 + z2‖ := by
  intros
  exact norm_add_le z1 z2
