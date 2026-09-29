-- Prove2me | solution 1 for lean_workbook_plus_56484
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:40:33.849247+00:00
-- url     : https://prove2.me/submissions/13558e5a-fe0b-4764-8aeb-2761f0d9797a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (k : ℕ) : 2 ^ (k - 1) ≥ k := by
  cases k with
  | zero => norm_num
  | succ n =>
    simp only [Nat.succ_sub_one]
    exact Nat.succ_le_of_lt (Nat.lt_two_pow_self (n:=n))
