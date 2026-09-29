-- Prove2me | solution 1 for lean_workbook_plus_46120
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:47:21.81349+00:00
-- url     : https://prove2.me/submissions/dd3146a4-0f9b-48d6-b9ef-12bc13e6553d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (f : ℝ → ℝ) (hf1 : ∀ x, f x ^ 2 = f (x ^ 2)) (hf2 : ∀ x, f (- x) = - f x) : ∀ x ≥ 0, f x ≥ 0 := by
  intro x hx
  have h := hf1 (Real.sqrt x)
  rw [Real.sq_sqrt hx] at h
  rw [← h]
  exact sq_nonneg _
