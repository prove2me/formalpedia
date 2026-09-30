-- Prove2me | solution 1 for lean_workbook_plus_57616
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:24:10.802024+00:00
-- url     : https://prove2.me/submissions/37eb36d9-5ae8-4783-ab6f-f999782e7980

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ A : Set (ℕ → ℝ), A = {x | ∀ n : ℕ, 0 ≤ x n} ↔ ∀ x : ℕ → ℝ, x ∈ A ↔ ∀ n : ℕ, 0 ≤ x n := by
  intro A
  exact Set.ext_iff
