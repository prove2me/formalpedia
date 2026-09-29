-- Prove2me | solution 1 for mme_finite_collision_budget_averaging_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T21:30:23.929424+00:00
-- url     : https://prove2.me/submissions/06eb7409-58e4-40a1-adcf-ab8df80be7d6

import Mathlib

open BigOperators

set_option autoImplicit false

/-- A real-valued version of finite collision-budget averaging.  This avoids
rounding a real target loss before selecting the favorable hash state. -/
theorem solution {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (good bad : Ω → ℕ) (L : ℝ)
    (hbudget :
      (Fintype.card Ω : ℝ) * L + ∑ ω, (bad ω : ℝ) ≤
        ∑ ω, (good ω : ℝ)) :
    ∃ ω, (bad ω : ℝ) + L ≤ (good ω : ℝ) := by
  by_contra hnone
  push_neg at hnone
  have hsum :
      (∑ ω, (good ω : ℝ)) < ∑ ω, ((bad ω : ℝ) + L) := by
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun ω _ => hnone ω)
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hsum' :
      (∑ ω, (good ω : ℝ)) <
        (Fintype.card Ω : ℝ) * L + ∑ ω, (bad ω : ℝ) := by
    simpa only [mul_comm, add_comm] using hsum
  exact (not_lt_of_ge hbudget) hsum'
