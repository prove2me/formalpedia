-- Prove2me | solution 1 for lean_workbook_plus_11736
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:48:37.217444+00:00
-- url     : https://prove2.me/submissions/afdb0524-a083-43ea-88ac-35b79d547ebc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℕ → ℝ) (hf : ∀ n, f n = 1 / (n ^ 2 + 1)) : ∃ l, ∑' n : ℕ, f n = l := by
  norm_num
