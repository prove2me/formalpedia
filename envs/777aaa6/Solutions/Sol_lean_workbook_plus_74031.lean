-- Prove2me | solution 1 for lean_workbook_plus_74031
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:50:14.716993+00:00
-- url     : https://prove2.me/submissions/f9398fa3-fc7b-41ab-97c0-a9f94397daa5

import Mathlib
set_option autoImplicit false

theorem solution :
  10^2016 ≡ 1 [MOD 2017]   := by
  have hp : Nat.Prime 2017 := by norm_num
  have hc : Nat.Coprime 10 2017 := by norm_num
  exact Nat.ModEq.pow_card_sub_one_eq_one hp hc

#print axioms solution
