-- Prove2me | solution 1 for lean_workbook_plus_62425
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:46:07.233714+00:00
-- url     : https://prove2.me/submissions/bce92a40-98e9-4c17-b451-45eac2562d41

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ x : ℝ, (-8 * x ^ 2 + 15) ≤ 15 := by
  intro x
  intros
  nlinarith
