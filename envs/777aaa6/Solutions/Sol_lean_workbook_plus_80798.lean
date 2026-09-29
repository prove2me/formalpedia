-- Prove2me | solution 1 for lean_workbook_plus_80798
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T16:57:57.917725+00:00
-- url     : https://prove2.me/submissions/9f97ff0b-cd4e-464b-911d-00ceb62b52c9

import Mathlib.Tactic

theorem solution : ∀ a b c : ℝ, 3 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ (a + b + c) ^ 2 := by
  intro a b c; nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
