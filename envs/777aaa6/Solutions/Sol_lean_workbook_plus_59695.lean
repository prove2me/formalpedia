-- Prove2me | solution 1 for lean_workbook_plus_59695
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:07:14.645197+00:00
-- url     : https://prove2.me/submissions/9365b2e7-a1c5-41d6-8b6f-62ca102ef6d1

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum

theorem solution (n : ℕ) : (n ^ 10) % 11 = 0 ∨ (n ^ 10) % 11 = 1 := by
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  by_cases hn : (n : ZMod 11) = 0
  · left
    have hp : ((n ^ 10 : ℕ) : ZMod 11) = 0 := by simp [hn]
    simpa only [ZMod.val_natCast, ZMod.val_zero] using congrArg ZMod.val hp
  · right
    have hp : ((n ^ 10 : ℕ) : ZMod 11) = 1 := by
      simpa using ZMod.pow_card_sub_one_eq_one hn
    simpa only [ZMod.val_natCast, ZMod.val_one] using congrArg ZMod.val hp

#check @solution
#print axioms solution
