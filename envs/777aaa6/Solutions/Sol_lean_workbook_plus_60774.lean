-- Prove2me | solution 1 for lean_workbook_plus_60774
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:35:13.762536+00:00
-- url     : https://prove2.me/submissions/f4cbcea0-bf83-4269-83b1-ec26426d4012

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ x : ℝ, 3 * x ^ 2 + 3 * x + 5 > 0 := by
  intro x
  intros
  nlinarith
