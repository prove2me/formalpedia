-- Prove2me | solution 1 for lean_workbook_plus_59896
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:54:42.878175+00:00
-- url     : https://prove2.me/submissions/c0bff404-ca10-4b71-bf79-0826c614506b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ x y : ℝ, x + y = 2 → x * y ≤ 1 := by
  intro x y
  intros
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x - y)]
