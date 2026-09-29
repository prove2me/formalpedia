-- Prove2me | solution 1 for lean_workbook_plus_43735
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:09:50.222508+00:00
-- url     : https://prove2.me/submissions/98158fc8-81c1-4d70-a6c4-5c572d706e1a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℕ) : 3 * ((n - 1) * n) / 2 + n = (3 * n ^ 2 - n) / 2 := by
  cases n with
  | zero => norm_num
  | succ k =>
    simp only [Nat.succ_eq_add_one,Nat.add_sub_cancel]
    have he0 : 3*(k+1)^2=3*(k*(k+1))+3*(k+1) := by ring
    have he : 3*(k+1)^2-(k+1)=3*(k*(k+1))+2*(k+1) := by rw [he0]; omega
    rw [he,Nat.add_mul_div_left _ _ (by norm_num : 0<2)]
