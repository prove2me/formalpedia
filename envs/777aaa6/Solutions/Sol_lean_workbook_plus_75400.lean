-- Prove2me | solution 1 for lean_workbook_plus_75400
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:34.670893+00:00
-- url     : https://prove2.me/submissions/ed52c738-6434-4653-8d41-7f202a2c9ba1

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) : (n + 1).choose 2 + n + 1 = (n + 2).choose 2 := by
  have h : (n + 2).choose 2 = (n + 1).choose 1 + (n + 1).choose 2 := Nat.choose_succ_succ (n + 1) 1
  rw [Nat.choose_one_right] at h
  omega
