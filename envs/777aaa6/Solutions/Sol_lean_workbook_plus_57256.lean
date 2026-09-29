-- Prove2me | solution 1 for lean_workbook_plus_57256
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:05:02.045249+00:00
-- url     : https://prove2.me/submissions/dce3d3b3-6bfc-4be8-a68a-8fb33eeab5d4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ a : ℤ, a^4 ≥ a^3 := by
  intro a
  by_cases ha : a≤0
  · have h3 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) ha
    have hp := mul_nonneg_of_nonpos_of_nonpos h3 (show a-1≤0 by omega)
    nlinarith only [hp]
  · have h1 : 1≤a := by omega
    have hp := mul_nonneg (show 0≤a^3 by positivity) (show 0≤a-1 by omega)
    nlinarith only [hp]
