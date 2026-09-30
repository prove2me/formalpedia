-- Prove2me | solution 1 for lean_workbook_plus_47613
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:18:27.252706+00:00
-- url     : https://prove2.me/submissions/975c98af-9d67-4d7d-8bd0-aaf3eb31b208

import Mathlib
set_option autoImplicit false

theorem solution (k : ℕ) (h₁ : 3 ≤ k) : 2 * k + 2 ≤ 2^k   := by
  induction' h₁ with k h₁ ih
  norm_num
  rw [Nat.pow_succ]
  linarith

#print axioms solution
