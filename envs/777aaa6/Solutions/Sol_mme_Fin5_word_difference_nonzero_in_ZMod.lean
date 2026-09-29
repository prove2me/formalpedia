-- Prove2me | solution 1 for mme_Fin5_word_difference_nonzero_in_ZMod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T22:01:48.873423+00:00
-- url     : https://prove2.me/submissions/c24988b2-147e-4321-a839-e225eed491c9

import Mathlib

set_option autoImplicit false

/-- Distinct five-grade words have a coordinate whose cast difference is
nonzero modulo every modulus larger than four. -/
theorem solution {p N : ℕ} (hp : 5 ≤ p)
    (x y : Fin (N + 1) → Fin 5) (hxy : x ≠ y) :
    ∃ j : Fin (N + 1),
      ((x j).val : ZMod p) - ((y j).val : ZMod p) ≠ 0 := by
  have hcoord : ∃ j : Fin (N + 1), x j ≠ y j := by
    by_contra h
    push_neg at h
    exact hxy (funext h)
  obtain ⟨j, hj⟩ := hcoord
  refine ⟨j, ?_⟩
  intro hzero
  have hcast : ((x j).val : ZMod p) = ((y j).val : ZMod p) :=
    sub_eq_zero.mp hzero
  rw [ZMod.natCast_eq_natCast_iff'] at hcast
  have hxlt : (x j).val < p := lt_of_lt_of_le (x j).isLt hp
  have hylt : (y j).val < p := lt_of_lt_of_le (y j).isLt hp
  rw [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] at hcast
  exact hj (Fin.ext hcast)
