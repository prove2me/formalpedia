-- Prove2me | solution 1 for lean_workbook_plus_27538
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:33:18.73091+00:00
-- url     : https://prove2.me/submissions/951fa111-56d6-4271-9e57-2dea94503f64

import Mathlib

theorem inverse_certificate : (108 : Int) * 289 = 1 + 59 * 529 := by norm_num

theorem solution (x : Nat) :
    108 * x ≡ 171 [ZMOD 529] ↔ x ≡ 222 [ZMOD 529] := by
  simp only [Int.ModEq]
  omega

#print axioms solution
