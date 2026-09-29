-- Prove2me | solution 1 for WorkbookRestored.plus_52484
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:24:49.293499+00:00
-- url     : https://prove2.me/submissions/22b141a2-d789-4e0c-9ff0-72b8ea7d372a

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_52484.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution :
  ∀ x ∈ Set.Icc (-Real.pi / 2) (Real.pi / 2), (Real.sin x)^2 + Real.cos x - 5 / 4 ≤ 0   := by
  intro x hx
  have := sin_sq_add_cos_sq x
  nlinarith [sq_nonneg (sin x - 1/2), sq_nonneg (cos x - 1/2)]
#print axioms solution
