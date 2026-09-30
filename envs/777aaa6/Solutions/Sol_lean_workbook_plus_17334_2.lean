-- Prove2me | solution 2 for lean_workbook_plus_17334
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:13:34.75249+00:00
-- url     : https://prove2.me/submissions/e00c2b03-1809-447f-b611-b6cd612210ff

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (u : ℕ → ℝ) (h : ∀ n, u n = 1 / (4 * n + 1) / (4 * n + 2) / (4 * n + 3) / (4 * n + 4)) : ∃ l, ∑' n : ℕ, u n = l := by
  norm_num
