-- Prove2me | solution 1 for lean_workbook_plus_51283
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:19:05.503463+00:00
-- url     : https://prove2.me/submissions/0fd88a26-8915-4fa4-bafc-52b0b6d58b30

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℕ) (a b : Fin n → ℝ) : ∑ i, a i * b i = ∑ i, a i * b i := by
  norm_num
