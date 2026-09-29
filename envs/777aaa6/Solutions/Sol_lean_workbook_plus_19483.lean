-- Prove2me | solution 1 for lean_workbook_plus_19483
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:50:46.294635+00:00
-- url     : https://prove2.me/submissions/61270eaa-29bd-4e8e-865e-a73e9973c0c7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) : (a^2+b^2+c^2)^3 ≥ a^6+b^6+c^6 := by
  intros
  nlinarith [sq_nonneg (a * b), sq_nonneg (a * c), sq_nonneg (b * c), sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2)]
