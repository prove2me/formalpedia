-- Prove2me | solution 1 for lean_workbook_plus_35979
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:40:34.398388+00:00
-- url     : https://prove2.me/submissions/b5be504b-4c99-4d8e-a49d-edc8f504796d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a : ℝ) (ha : a > 0) : (1 / Real.sqrt a) > 2 * (Real.sqrt (a + 1) - Real.sqrt a) := by
  have hu : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have huv : Real.sqrt a < Real.sqrt (a+1) :=
    Real.sqrt_lt_sqrt ha.le (by linarith)
  have hu2 := Real.sq_sqrt ha.le
  have hv2 := Real.sq_sqrt (show 0 ≤ a+1 by linarith)
  apply (lt_div_iff₀ hu).mpr
  nlinarith only [hu2, hv2, sq_pos_of_pos (sub_pos.mpr huv)]
