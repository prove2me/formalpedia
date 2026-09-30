-- Prove2me | solution 1 for lean_workbook_plus_2151
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:05:16.230753+00:00
-- url     : https://prove2.me/submissions/7f523461-f504-4a5d-92a5-6539171e4948

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (c : ℝ) (hc : 0 ≤ c) (f : ℝ → ℝ)
    (hf : ∀ x, f x = 1 / (c * x + 1)) :
    ∀ x y, (x > 0 ∧ y > 0) → f x * f (y * f x) = f (x + y) := by
  rintro x y ⟨hx, hy⟩
  have hxden : 0 < c * x + 1 := by positivity
  have hsumden : 0 < c * (x + y) + 1 := by positivity
  simp only [hf]
  field_simp [ne_of_gt hxden, ne_of_gt hsumden]
  <;> ring

#print axioms solution
