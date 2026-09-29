-- Prove2me | solution 1 for lean_workbook_plus_26999
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:17:56.144918+00:00
-- url     : https://prove2.me/submissions/62097039-492d-442a-aa25-4ee17d7488f3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (hx : x ≠ 0) : (x^3 - 1)^2 * (x^6 + x^3 + 1) / x^4 ≥ 0 := by
  have hp : 0≤x^6+x^3+1 := by nlinarith [sq_nonneg (x^3+1/2)]
  positivity
