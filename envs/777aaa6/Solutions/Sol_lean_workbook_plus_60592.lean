-- Prove2me | solution 1 for lean_workbook_plus_60592
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:48.230737+00:00
-- url     : https://prove2.me/submissions/c211ff89-45fd-4138-aa40-43dfe103e4ac

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (p q r : ℝ) :
  (p^4 + 2 * q^2 * r^2) / (p^6 + q^4 + r^4) ≤ (p^4 + q^4 + r^4) / (p^6 + q^4 + r^4) := by
  apply div_le_div_of_nonneg_right
  · nlinarith only [sq_nonneg (q^2-r^2)]
  · positivity
