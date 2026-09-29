-- Prove2me | solution 1 for lean_workbook_plus_66139
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:31:47.707075+00:00
-- url     : https://prove2.me/submissions/11172992-6917-4b65-83f0-bdcf73fd383b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (c : ℝ) (h : ∀ x, f x = c) : ∃ k, f k = c := by
  (intros; simp_all)
