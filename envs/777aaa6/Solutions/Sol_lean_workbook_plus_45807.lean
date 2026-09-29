-- Prove2me | solution 1 for lean_workbook_plus_45807
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:14:05.517975+00:00
-- url     : https://prove2.me/submissions/bca56134-72a9-41a1-ae5b-9f56f6bef39a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ x y u v : ℝ, x^2 + y^2 = 1 ∧ u^2 + v^2 = 1 → x * u + y * v ≤ 1 := by
  intro x y u v
  intros
  nlinarith [sq_nonneg (x*y - u*v), sq_nonneg (x*u - y*v), sq_nonneg (x*v - y*u)]
