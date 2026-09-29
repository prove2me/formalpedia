-- Prove2me | solution 1 for lean_workbook_plus_70161
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:52:49.733264+00:00
-- url     : https://prove2.me/submissions/55796c05-f3ef-4129-b6b0-8c737b91e5f2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (A B C : Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) (hn : 1 ≤ n) : A ^ n = A ^ n ∧ B ^ n = B ^ n ∧ C ^ n = C ^ n := by
  norm_num
