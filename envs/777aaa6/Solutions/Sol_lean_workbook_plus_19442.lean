-- Prove2me | solution 1 for lean_workbook_plus_19442
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:14.422371+00:00
-- url     : https://prove2.me/submissions/1e032fcb-61fe-4272-8fc9-036c2eaac609

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (u : ℝ) (h₁ : 2 * x - 1 = u ^ 2) (h₂ : abs (u + 1) + abs (u - 1) = 2) (h₃ : abs u ≤ 1) : 1 / 2 ≤ x ∧ x ≤ 1 := by
  have hu := abs_le.mp h₃
  constructor
  · nlinarith [sq_nonneg u]
  · nlinarith [mul_nonneg (show 0 ≤ 1-u by linarith [hu.2]) (show 0 ≤ 1+u by linarith [hu.1])]
