-- Prove2me | solution 1 for lean_workbook_plus_39783
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:51:05.382378+00:00
-- url     : https://prove2.me/submissions/91f3779a-fa2a-4291-9f9d-ea6eaeafb561

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) (q : ℝ) (hq : 0 < q ∧ q < 1) : ∃ x : ℕ → ℂ, x 1 = 1 / x 1 + q ^ 2 * x 2 ∧ x 2 = 1 / x 2 + q ^ 4 * x 3 ∧ ∀ i ∈ Finset.range n, x i = 1 / x i + q ^ (2 * i) * x (i + 1) := by
  refine ⟨fun _ => 0, ?_, ?_, ?_⟩ <;> simp
