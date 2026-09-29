-- Prove2me | solution 1 for lean_workbook_plus_60705
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:09:57.799389+00:00
-- url     : https://prove2.me/submissions/9c3a1bb7-5352-4dc3-b249-4f9a5a58cc59

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y : ℝ)
  (h₀ : 0 < x ∧ 0 < y) :
  9 * x^2 * y^2 - 12 * x * y + 4 ≥ 0 := by
  nlinarith [sq_nonneg (3*x*y-2)]
