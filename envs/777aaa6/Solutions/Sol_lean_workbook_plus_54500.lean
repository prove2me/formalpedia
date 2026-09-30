-- Prove2me | solution 1 for lean_workbook_plus_54500
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:46:03.260358+00:00
-- url     : https://prove2.me/submissions/04c6aff6-23a6-4ce5-8538-26d94b0e3209

import Mathlib.Analysis.Complex.Basic

theorem solution  (a b t k : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < t ∧ 0 < k)
  (h₁ : a * b = t^2)
  (h₂ : Real.sqrt (t^4 + b^4) = 2 * k * b) :
  t^4 + b^4 = 4 * k^2 * b^2 := by
  have hnn : 0 ≤ t^4 + b^4 := by positivity
  have hsq := Real.sq_sqrt hnn
  rw [h₂] at hsq
  rw [← hsq]
  ring
