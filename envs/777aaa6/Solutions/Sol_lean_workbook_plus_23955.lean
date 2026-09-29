-- Prove2me | solution 1 for lean_workbook_plus_23955
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:42:39.17392+00:00
-- url     : https://prove2.me/submissions/178f74c9-fda4-45b3-961b-b121f7c35555

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) (hx : x > 2) : x^4 - 40 * x^2 + 64 * x + 144 > 0 := by
  have hp : 0 ≤ x^2+8*x+8 := by nlinarith [sq_nonneg x]
  have h := mul_nonneg (sq_nonneg (x-4)) hp
  nlinarith only [h]
