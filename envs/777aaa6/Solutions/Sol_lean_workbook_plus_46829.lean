-- Prove2me | solution 1 for lean_workbook_plus_46829
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:21:31.440455+00:00
-- url     : https://prove2.me/submissions/fba55450-4e8d-4ca0-a36e-7b964ce3ffa2

import Mathlib.Analysis.Complex.Basic

theorem solution (a x : ℕ) (h : 4 * a * (a + 1) = 8 * x) : ∃ k : ℕ, k * (k + 1) / 2 = x := by
  refine ⟨a, ?_⟩
  have h2 : a * (a + 1) = 2 * x := by linarith
  omega
