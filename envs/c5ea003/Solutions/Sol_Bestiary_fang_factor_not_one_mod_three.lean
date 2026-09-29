-- Prove2me | solution 1 for Bestiary.fang_factor_not_one_mod_three
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T00:32:28.38205+00:00
-- url     : https://prove2.me/submissions/f3b6a6d5-41d5-48e5-9a4b-d8b733305375

import Mathlib
import Definitions.Def_Novelty_VampireNumbers
open Bestiary in
theorem solution {x y : ℕ} (h : IsFangPair 10 x y) : x % 3 ≠ 1 ∧ y % 3 ≠ 1 := by
  -- casting out nines: a number is congruent to its decimal digit sum mod `9`
  have hnat : x * y ≡ x + y [MOD 9] := by
    have hsum : (Nat.digits 10 (x * y)).sum = (Nat.digits 10 x).sum + (Nat.digits 10 y).sum := by
      rw [h.sum_eq, List.sum_append]
    have hmod : 10 % 9 = 1 := by norm_num
    have h1 := Nat.modEq_digits_sum 9 10 hmod (x * y)
    have h2 := Nat.modEq_digits_sum 9 10 hmod x
    have h3 := Nat.modEq_digits_sum 9 10 hmod y
    rw [hsum] at h1
    exact h1.trans (h2.add h3).symm
  -- so `x y ≡ x + y (mod 3)`; a factor `≡ 1` would force `y ≡ y + 1`
  have h3 : x * y % 3 = (x + y) % 3 := Nat.ModEq.of_dvd (by norm_num : 3 ∣ 9) hnat
  rw [Nat.mul_mod, Nat.add_mod] at h3
  constructor
  · intro hx
    rw [hx] at h3
    omega
  · intro hy
    rw [hy] at h3
    omega
