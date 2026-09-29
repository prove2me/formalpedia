-- Prove2me | solution 1 for lean_workbook_plus_55348
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:29:26.226413+00:00
-- url     : https://prove2.me/submissions/00f42fd2-42f6-49f1-9ffd-d8db80cb229b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℕ) : (n + 1).choose 2 + n.choose 2 = n^2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.choose_succ_succ (n+1) 1]
    simp only [Nat.choose_one_right]
    have hp : (n+1).choose 2 = n + n.choose 2 := by simpa using Nat.choose_succ_succ n 1
    nlinarith
