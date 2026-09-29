-- Prove2me | solution 1 for lean_workbook_plus_63253
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:55:10.410841+00:00
-- url     : https://prove2.me/submissions/e4c410bd-0aea-4738-bffb-05acea2ae0d1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ)
  (h₀ : abs (x^2 + 2 * x - 4) = 4) :
  x^2 + 2 * x - 4 = 4 ∨ x^2 + 2 * x - 4 = -4 := by
  intros
  exact?
