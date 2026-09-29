-- Prove2me | solution 1 for lean_workbook_plus_68934
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:40:20.809875+00:00
-- url     : https://prove2.me/submissions/8b2b05ed-b1ce-4f7e-bfd0-d5655a6a31e7

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false

theorem solution (n : ℕ) : (n + 1).choose 2 = n * (n + 1) / 2 := by
  rw [Nat.choose_two_right]
  simp [Nat.mul_comm]
