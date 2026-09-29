-- Prove2me | solution 1 for lean_workbook_plus_51883
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:32:10.223958+00:00
-- url     : https://prove2.me/submissions/9121a3ee-5686-4f0d-86ba-e8ac4b2a6205

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ x y z : ℝ, -(x^2+y^2+z^2)*(x-y-z)^2-2*y^2*z^2 ≤ 0 := by
  intro x y z
  intros
  nlinarith
