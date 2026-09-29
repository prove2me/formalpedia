-- Prove2me | solution 1 for lean_workbook_plus_39830
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:41:22.691124+00:00
-- url     : https://prove2.me/submissions/6fe2cd44-dcbe-46ef-a5ed-6f8d3c6ad2f0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℕ → ℝ) (hx : ∀ n, |x n| > 2 → |x (n + 1)| ≥ 2) : ∀ n, |x n| > 2 → |x (n + 1)| ≥ 2 := by
  (intros; simp_all)
