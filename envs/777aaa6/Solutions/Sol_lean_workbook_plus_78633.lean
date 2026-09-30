-- Prove2me | solution 1 for lean_workbook_plus_78633
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:05:59.136172+00:00
-- url     : https://prove2.me/submissions/ff28ec54-c025-494a-b996-67110e57b70e

import Mathlib
set_option autoImplicit false

theorem solution (x : ℕ → ℝ) (i : ℕ) : x i * x (i + 1) ≤ (x i ^ 2 + x (i + 1) ^ 2) / 2   := by
  nlinarith [sq_nonneg (x i - x (i + 1))]

#print axioms solution
