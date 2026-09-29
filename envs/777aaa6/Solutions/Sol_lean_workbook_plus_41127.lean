-- Prove2me | solution 1 for lean_workbook_plus_41127
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:46:34.591898+00:00
-- url     : https://prove2.me/submissions/fa5f11d6-2c3b-40bd-9b09-29a4a53d847b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : Function.Injective (fun x : ℝ => 2 * x + 1) := by
  intro x y h
  linarith
