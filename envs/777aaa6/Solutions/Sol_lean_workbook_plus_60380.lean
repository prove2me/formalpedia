-- Prove2me | solution 1 for lean_workbook_plus_60380
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:24:28.240471+00:00
-- url     : https://prove2.me/submissions/431d1b62-b94e-42ad-b6a2-f96797a81cf2

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℕ) : (n^3 - 1) = (n-1)*(n^2+n+1) := by
  cases n with
  | zero => norm_num
  | succ m =>
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
    have he : (m+1)^3=m*((m+1)^2+(m+1)+1)+1 := by ring
    rw [he,Nat.add_sub_cancel]
