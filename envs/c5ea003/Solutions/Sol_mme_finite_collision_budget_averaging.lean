-- Prove2me | solution 1 for mme_finite_collision_budget_averaging
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T20:40:59.065491+00:00
-- url     : https://prove2.me/submissions/be9b9a39-637b-4510-afaa-4f70daccfdb0

import Mathlib

open BigOperators

set_option autoImplicit false

/-- If the total good mass dominates the total bad mass plus the same budget
in every state, one state realizes that pointwise budget. -/
theorem solution {Ω : Type} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (good bad : Ω → ℕ) (L : ℕ)
    (hbudget : Fintype.card Ω * L + ∑ ω, bad ω ≤ ∑ ω, good ω) :
    ∃ ω, bad ω + L ≤ good ω := by
  by_contra hnone
  push_neg at hnone
  have hsum : (∑ ω, good ω) < ∑ ω, (bad ω + L) := by
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun ω _ => hnone ω)
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hsum' :
      (∑ ω, good ω) < Fintype.card Ω * L + ∑ ω, bad ω := by
    simpa only [Nat.mul_comm, Nat.add_comm] using hsum
  exact (Nat.not_lt_of_ge hbudget) hsum'
