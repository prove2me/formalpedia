-- Prove2me | solution 1 for lean_workbook_plus_51673
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:48.607351+00:00
-- url     : https://prove2.me/submissions/de3bf6b6-03e6-471b-81aa-2fc574167a3b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : Function.Injective (fun x : ℝ => 2 * x) := by
  intro x y h
  linarith
