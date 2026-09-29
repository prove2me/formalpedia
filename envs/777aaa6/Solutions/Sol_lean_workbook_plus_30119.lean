-- Prove2me | solution 1 for lean_workbook_plus_30119
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:29:24.633098+00:00
-- url     : https://prove2.me/submissions/0700c123-585f-4837-af79-4f1c760f93d2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (s t : ℂ) : ‖s + t‖ ≤ ‖s‖ + ‖t‖ := by
  intros
  exact norm_add_le s t
