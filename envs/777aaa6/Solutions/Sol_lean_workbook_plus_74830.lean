-- Prove2me | solution 1 for lean_workbook_plus_74830
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:51:13.28572+00:00
-- url     : https://prove2.me/submissions/dd1f1ac3-2198-408f-8598-4a5f5779c31a

import Mathlib
set_option autoImplicit false

theorem solution (a : ℤ) : a^7 ≡ a [ZMOD 7]   := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  apply (ZMod.intCast_eq_intCast_iff (a ^ 7) a 7).mp
  simpa only [Int.cast_pow] using (ZMod.pow_card (a : ZMod 7))

#print axioms solution
