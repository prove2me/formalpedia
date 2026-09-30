-- Prove2me | solution 1 for lean_workbook_plus_42147
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:04:45.568334+00:00
-- url     : https://prove2.me/submissions/9d15a193-7371-48a7-8e08-a33139977ede

import Mathlib

set_option autoImplicit false

theorem solution (j : ℕ) : (j + 2).choose 3 = j.choose 3 + j ^ 2 := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    have h1 := Nat.choose_succ_succ (j + 2) 2
    have h2 := Nat.choose_succ_succ j 2
    have h3 := Nat.choose_succ_succ (j + 1) 1
    have h4 := Nat.choose_succ_succ j 1
    simp only [Nat.choose_one_right] at h3 h4
    nlinarith

#print axioms solution
