-- Prove2me | solution 1 for lean_workbook_plus_26677
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:35:01.688854+00:00
-- url     : https://prove2.me/submissions/72c88736-4bb6-4c4f-9a2d-1b4c0b1e4bbd

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) : a^8 + b^8 ≥ (a^2 + b^2)^4 / 8 := by
  intros
  nlinarith [sq_nonneg (a * b), sq_nonneg (a^2 - b^2)]
