-- Prove2me | solution 1 for WorkbookRestored.plus_33164
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:41.290709+00:00
-- url     : https://prove2.me/submissions/489f3e49-1b68-419e-939a-fbe12dd99d1d

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_33164.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x ∈ Set.Icc 0 Real.pi, (1 + Real.sin x) * (Real.cos x)^2 ≤ 32/27   := by
  intro x hx
  have h1 := sq_nonneg (sin x - 1 / 3)
  have h2 := sq_nonneg (sin x + 1 / 3)
  nlinarith [sin_sq_add_cos_sq x]
#print axioms solution
