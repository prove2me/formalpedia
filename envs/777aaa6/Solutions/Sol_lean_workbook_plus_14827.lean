-- Prove2me | solution 1 for lean_workbook_plus_14827
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:38:49.978013+00:00
-- url     : https://prove2.me/submissions/a40a47ad-6ca2-4494-aa45-5f525c18c902

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x_A y_A : ℝ) (h : y_A / x_A = 7) : y_A = 7 * x_A := by
  intros
  grind
