-- Prove2me | solution 1 for lean_workbook_plus_67978
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:48:52.002005+00:00
-- url     : https://prove2.me/submissions/cc9ef16f-cf88-4c4c-b495-b684cbbec296

import Mathlib
set_option autoImplicit false

theorem solution : 2 ^ 2005 + 2004 ^ 2005 ≡ 0 [ZMOD 2006]   := by
  have h : (2004 : ℤ) ≡ -2 [ZMOD 2006] := by norm_num [Int.ModEq]
  have hodd : Odd (2005 : ℕ) := ⟨1002, by norm_num⟩
  have hp := (Int.ModEq.pow 2005 h).add_left ((2 : ℤ) ^ 2005)
  simpa only [hodd.neg_pow, add_neg_cancel] using hp

#print axioms solution
