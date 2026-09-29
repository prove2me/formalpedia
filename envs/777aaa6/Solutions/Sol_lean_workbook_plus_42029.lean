-- Prove2me | solution 1 for lean_workbook_plus_42029
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:40:07.532252+00:00
-- url     : https://prove2.me/submissions/90801b93-9da2-4617-91dd-02cf29057342

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (k : ℕ) (x : ℝ) : (f x = (x^2 + 1)^k) ↔ (f x = (x^2 + 1)^k) := by
  norm_num
