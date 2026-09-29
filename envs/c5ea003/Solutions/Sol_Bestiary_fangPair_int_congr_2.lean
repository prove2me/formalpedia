-- Prove2me | solution 2 for Bestiary.fangPair_int_congr
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T21:34:11.451511+00:00
-- url     : https://prove2.me/submissions/d406368c-1c20-42e3-b06d-3b0221674397

import Mathlib
import Definitions.Def_Novelty_VampireNumbers
open Bestiary in
theorem solution (b x y : ℕ) (hb : 2 ≤ b) (h : IsFangPair b x y) :
    ((x : ℤ) - 1) * ((y : ℤ) - 1) ≡ 1 [ZMOD ((b : ℤ) - 1)] := by
  -- casting out `(b-1)`s: a number is congruent to its base-`b` digit sum mod `b - 1`
  have hnat : x * y ≡ x + y [MOD (b - 1)] := by
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
  -- `(x - 1)(y - 1) - 1 = x y - (x + y)`
  rw [Nat.modEq_iff_dvd] at hnat
  rw [Int.modEq_iff_dvd]
  have hcast : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ b)]
    simp
  rw [← hcast]
  convert hnat using 1
  push_cast
  ring
