-- Prove2me | solution 1 for lean_workbook_plus_42059
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:35:09.469991+00:00
-- url     : https://prove2.me/submissions/0971d481-bfd3-44ca-b208-8cf434b49058

import Mathlib.Analysis.Complex.Basic

theorem solution (y : ℝ) (n : ℕ) (hy : y > 0) : y ^ n - 1 ≥ n * (y - 1) := by
  have h := one_add_mul_le_pow (a := y - 1) (by linarith) n
  have e : (1 : ℝ) + (y - 1) = y := by ring
  rw [e] at h
  linarith
