-- Prove2me | solution 1 for lean_workbook_plus_36804
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:48:05.054951+00:00
-- url     : https://prove2.me/submissions/82cf251c-31f1-4065-8863-a92f9b0f115d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (f : ℝ → ℝ) (hf : ∀ x y, x * f y = y * f x) : ∃ k, ∀ x, f x = k * x := by
  refine ⟨f 1,?_⟩
  intro x
  simpa [mul_comm] using hf 1 x
