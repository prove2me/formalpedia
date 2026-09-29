-- Prove2me | solution 1 for lean_workbook_plus_58182
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:48:23.960849+00:00
-- url     : https://prove2.me/submissions/fdce950a-c758-4dbd-b66a-5c297e70fdb5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (k : ℤ) : k^2 + k - 1332 = 0 ↔ k = 36 ∨ k = -37 := by
  constructor
  · intro h
    have hf : (k-36)*(k+37)=0 := by nlinarith
    rcases mul_eq_zero.mp hf with h | h <;> omega
  · rintro (rfl | rfl) <;> norm_num
