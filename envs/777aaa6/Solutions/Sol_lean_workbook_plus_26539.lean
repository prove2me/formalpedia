-- Prove2me | solution 1 for lean_workbook_plus_26539
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:30:07.802697+00:00
-- url     : https://prove2.me/submissions/2dcd1247-ef6c-4b7a-8544-bd54282fc42e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a : ℝ, (a - 1) ^ 2 * (a ^ 2 - a + 6) ≥ 0 := by
  intro a
  intros
  nlinarith
