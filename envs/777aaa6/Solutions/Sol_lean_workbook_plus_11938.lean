-- Prove2me | solution 1 for lean_workbook_plus_11938
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:24:18.624182+00:00
-- url     : https://prove2.me/submissions/eba46c21-a777-43f3-aed9-b68ece1c5d2d

import Mathlib.Analysis.Complex.Basic

theorem solution  (x y z : ℝ)
  (h₀ : x - y = z - x)
  (h₁ : y - z = x - y)
  (h₂ : x - y + y - z + z - x = 0) :
  x - y = 0 ∧ y - z = 0 ∧ z - x = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> linarith
