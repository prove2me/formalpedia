-- Prove2me | solution 1 for Heisenberg125.Heis.eq_zero_of_cast_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T05:52:27.914285+00:00
-- url     : https://prove2.me/submissions/5a82688a-665a-4e5e-a71b-953090493297

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_LowerBound

open Heisenberg125 Heis

variable {p : ℕ}

theorem solution (hp : 0 < p) {n : ℕ} (hn : n ≤ p - 1)
    (h : (n : ZMod p) = 0) : n = 0 := by
  have : p ≠ 0 := ne_of_gt hp
  haveI : NeZero p := ⟨this⟩
  have hdiv : p ∣ n := (ZMod.natCast_eq_zero_iff n p).mp h
  obtain ⟨k, hk⟩ := hdiv
  have hk' : n = p * k := hk
  have : k = 0 := by
    by_contra hk0
    have hkpos : 1 ≤ k := Nat.pos_of_ne_zero hk0
    have : p ≤ n := by
      rw [hk']
      exact Nat.le_mul_of_pos_right p hkpos
    have : p ≤ p - 1 := le_trans this hn
    omega
  simp [hk', this]
