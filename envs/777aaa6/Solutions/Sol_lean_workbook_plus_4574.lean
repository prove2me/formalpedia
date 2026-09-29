-- Prove2me | solution 1 for lean_workbook_plus_4574
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:07.978583+00:00
-- url     : https://prove2.me/submissions/8f53d423-7397-4388-a0ec-305e9556bd31

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℤ) (h : x % 2 = 1) : (x ^ 2 + 1) % 2 = 0 ∧ (x ^ 2 + 1) % 4 ≠ 0 := by
  have hm : x%4=1 ∨ x%4=3 := by omega
  constructor
  · norm_num [pow_two,Int.add_emod,Int.mul_emod,h]
  · rcases hm with hm|hm <;> norm_num [pow_two,Int.add_emod,Int.mul_emod,hm]
