-- Prove2me | solution 1 for lean_workbook_plus_71317
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:40.141555+00:00
-- url     : https://prove2.me/submissions/4e3526a4-9afb-4f8b-984b-3d14651fd74d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℤ) : n^2 + 3*n - 2 = 2*n ↔ n = 1 ∨ n = -2 := by
  constructor
  · intro h
    have hf : (n-1)*(n+2)=0 := by nlinarith
    rcases mul_eq_zero.mp hf with h | h
    · left; omega
    · right; omega
  · rintro (rfl | rfl) <;> norm_num
