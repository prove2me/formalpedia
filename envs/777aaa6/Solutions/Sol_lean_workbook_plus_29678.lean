-- Prove2me | solution 1 for lean_workbook_plus_29678
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:25:38.510617+00:00
-- url     : https://prove2.me/submissions/88b9dd64-c00b-43b6-8153-c3c032782629

import Mathlib
set_option autoImplicit false

theorem solution (n : ℕ) : 4^(2*n+1) + 3^(n+2) ≡ 0 [ZMOD 13]   := by
  have hbase : (4 : ℤ)^2 ≡ 3 [ZMOD 13] := by norm_num [Int.ModEq]
  have hp := hbase.pow n
  have hid : (4 : ℤ)^(2*n+1) + 3^(n+2) = (4^2)^n*4 + 3^n*9 := by
    rw [pow_add, pow_mul, pow_add]
    norm_num
  rw [hid]
  refine ((hp.mul_right 4).add_right ((3 : ℤ)^n*9)).trans ?_
  apply Int.modEq_zero_iff_dvd.2
  refine ⟨3^n, ?_⟩
  ring

#print axioms solution
