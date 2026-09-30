-- Prove2me | solution 1 for lean_workbook_plus_76961
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:21:48.354179+00:00
-- url     : https://prove2.me/submissions/7f748193-8fe4-4024-93f1-db21b702a56c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution : ∀ a b : ℝ, (1+1)*(a^6+b^6) ≥ (a^3+b^3)^2 := by
  intro a b
  nlinarith [sq_nonneg (a^3-b^3)]
