-- Prove2me | solution 2 for lean_workbook_plus_77859
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:24:22.160597+00:00
-- url     : https://prove2.me/submissions/42382918-87c0-44c7-b990-aab180729b9c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℕ → ℝ) (n : ℕ) (h : x (n + 1) * x n + 3 * x n - 2 * x (n + 1) - x (n + 1) ^ 2 - 2 = 0) : x n - 2 = (x (n + 1) + 2) * (x (n + 1) - x n) := by
  (intros; linarith)
