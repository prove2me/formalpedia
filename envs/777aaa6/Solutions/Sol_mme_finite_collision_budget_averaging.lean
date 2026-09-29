-- Prove2me | solution 1 for mme_finite_collision_budget_averaging
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T06:28:36.028137+00:00
-- url     : https://prove2.me/submissions/f48ba7f1-97df-456d-a818-2afb05b1259a

import Mathlib

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {Ω : Type} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
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
