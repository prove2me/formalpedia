-- Prove2me | solution 1 for Bestiary.fangPair_prod_modEq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T21:39:54.933915+00:00
-- url     : https://prove2.me/submissions/d80816e4-3b7e-4559-8c57-2ac4bf90402c

import Mathlib
import Definitions.Def_Novelty_VampireNumbers
open Bestiary in
theorem solution (b x y : ℕ) (hb : 2 ≤ b) (h : IsFangPair b x y) :
    x * y ≡ x + y [MOD (b - 1)] := by
  -- casting out `(b-1)`s: a number is congruent to its base-`b` digit sum mod `b - 1`
  have hsum : (Nat.digits b (x * y)).sum = (Nat.digits b x).sum + (Nat.digits b y).sum := by
    rw [h.sum_eq, List.sum_append]
  rcases Nat.lt_or_ge b 3 with hb3 | hb3
  · have hb1 : b - 1 = 1 := by omega
    rw [hb1]
    exact Nat.modEq_one
  · have hmod : b % (b - 1) = 1 := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.sub_sub_self (by omega),
        Nat.mod_eq_of_lt (by omega)]
    have h1 := Nat.modEq_digits_sum (b - 1) b hmod (x * y)
    have h2 := Nat.modEq_digits_sum (b - 1) b hmod x
    have h3 := Nat.modEq_digits_sum (b - 1) b hmod y
    rw [hsum] at h1
    exact h1.trans (h2.add h3).symm
