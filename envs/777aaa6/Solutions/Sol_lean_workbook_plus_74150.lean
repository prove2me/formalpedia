-- Prove2me | solution 1 for lean_workbook_plus_74150
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:08:47.656276+00:00
-- url     : https://prove2.me/submissions/67694bc8-174d-4393-a90a-f6ccb2a9761b

import Mathlib.Data.Nat.Choose.Basic

theorem solution (n : ℕ) : (n.choose 2) - (n - 1).choose 2 = n - 1 := by
  cases n with
  | zero => simp
  | succ n => simp [Nat.choose_succ_succ]
