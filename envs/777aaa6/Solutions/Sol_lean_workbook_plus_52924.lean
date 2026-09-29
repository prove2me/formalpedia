-- Prove2me | solution 1 for lean_workbook_plus_52924
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:30.101147+00:00
-- url     : https://prove2.me/submissions/5fd26859-7116-4fd5-b71a-f4328b527adc

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℕ) :
  n^2 - (n - 1)^2 = 2 * n - 1 := by
  cases n with
  | zero => norm_num
  | succ k =>
    simp only [Nat.succ_eq_add_one,Nat.add_sub_cancel]
    have he : (k+1)^2=k^2+2*k+1 := by ring
    rw [he]
    omega
