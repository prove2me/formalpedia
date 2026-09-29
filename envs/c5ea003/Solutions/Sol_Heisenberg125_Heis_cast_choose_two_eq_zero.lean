-- Prove2me | solution 1 for Heisenberg125.Heis.cast_choose_two_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-17T19:32:28.789027+00:00
-- url     : https://prove2.me/submissions/0169c03e-d562-481a-99a7-026f094af521

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic

open Heisenberg125 Heis

variable {p : ℕ}

theorem solution (hp : Odd p) : ((p.choose 2 : ℕ) : ZMod p) = 0 := by
  cases p with
  | zero =>
      exact absurd hp Nat.not_odd_zero
  | succ n =>
      rw [ZMod.natCast_eq_zero_iff, Nat.choose_two_right]
      -- goal: n+1 ∣ (n+1)*(n+1-1)/2
      change n + 1 ∣ (n + 1) * n / 2
      have hdiv : 2 ∣ n := by
        rw [Nat.dvd_iff_mod_eq_zero]
        have : (n + 1) % 2 = 1 := Nat.odd_iff.mp hp
        omega
      rw [Nat.mul_div_assoc (n + 1) hdiv]
      exact Nat.dvd_mul_right (n + 1) (n / 2)
