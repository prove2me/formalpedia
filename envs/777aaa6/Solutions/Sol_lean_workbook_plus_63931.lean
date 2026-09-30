-- Prove2me | solution 1 for lean_workbook_plus_63931
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:54:40.113721+00:00
-- url     : https://prove2.me/submissions/373c425f-10e1-421b-91d4-c3390a420278

import Mathlib
set_option autoImplicit false

theorem solution  (n : ℕ) :
  n^2 - 1 = (n + 1) * (n - 1)   := by
  cases n with
  | zero => norm_num
  | succ n =>
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
    have he : (n + 1) ^ 2 = n * (n + 2) + 1 := by ring
    rw [he, Nat.add_sub_cancel]
    ring

#print axioms solution
