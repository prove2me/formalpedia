-- Prove2me | solution 1 for lean_workbook_plus_51370
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:42:52.525199+00:00
-- url     : https://prove2.me/submissions/c9890b81-4bd3-4136-9b05-e457db8e744c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (z : ℂ) : ‖z - 1/z‖ ≤ ‖z‖ + ‖1/z‖ := by
  intros
  exact norm_sub_le z (1 / z)
