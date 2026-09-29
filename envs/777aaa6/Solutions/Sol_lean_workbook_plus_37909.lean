-- Prove2me | solution 1 for lean_workbook_plus_37909
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:35:37.201111+00:00
-- url     : https://prove2.me/submissions/4e3f4e1a-3bdd-4f80-9ada-32198aef00ba

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ x y z : ℝ, (3*x+4*y+5*z)^2 ≥ 24*(3*y*z+2*x*z+x*y) := by
  intro x y z
  intros
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
