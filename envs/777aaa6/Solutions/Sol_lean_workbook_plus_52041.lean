-- Prove2me | solution 1 for lean_workbook_plus_52041
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:36:49.473146+00:00
-- url     : https://prove2.me/submissions/865ea502-e688-46b5-beef-a0f954598694

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false

theorem solution (n : ℕ) :
    (n + 2).choose 4 - n.choose 2 = 2 * n.choose 3 + n.choose 4 := by
  rw [Nat.choose_succ_succ' (n + 1) 3, Nat.choose_succ_succ' n 2,
    Nat.choose_succ_succ' n 3]
  simp only [Nat.add_assoc, Nat.add_sub_cancel_left, two_mul]

#print axioms solution
