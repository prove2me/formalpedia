-- Prove2me | solution 1 for Probability.AdaptiveQS.sum_lt_of_separated
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T20:20:59.074858+00:00
-- url     : https://prove2.me/submissions/edcf198d-2c96-476b-9cf6-0bf5826f3a8f

import Mathlib
import Definitions.Def_Probability_AdaptiveQSAllocation
import Definitions.Def_Probability_AdaptiveQSSkipFlip

open Finset Probability.AdaptiveQS

variable {ι : Type*} [DecidableEq ι]

theorem solution {s K D : Finset ι} {r : ι → ℝ}
    (hunion : K ∪ D = s) (hdisj : Disjoint K D)
    (hsep : ∀ i ∈ K, ∀ j ∈ D, r j ≤ r i)
    {i₀ j₀ : ι} (hi₀ : i₀ ∈ K) (hj₀ : j₀ ∈ D) (hlt : r j₀ < r i₀) :
    (K.card : ℝ) * (∑ i ∈ s, r i) < (s.card : ℝ) * ∑ i ∈ K, r i := by
  have hs : s = K ∪ D := hunion.symm
  subst hs
  have hsum : ∑ i ∈ K ∪ D, r i = ∑ i ∈ K, r i + ∑ i ∈ D, r i :=
    sum_union hdisj
  rw [hsum]
  have hcard : ((K ∪ D).card : ℝ) = (K.card : ℝ) + (D.card : ℝ) := by
    norm_cast
    exact card_union_of_disjoint hdisj
  rw [hcard]
  have hgoal : (K.card : ℝ) * ∑ i ∈ D, r i < (D.card : ℝ) * ∑ i ∈ K, r i →
      (K.card : ℝ) * (∑ i ∈ K, r i + ∑ i ∈ D, r i) <
        ((K.card : ℝ) + (D.card : ℝ)) * ∑ i ∈ K, r i := by
    intro h
    nlinarith
  apply hgoal
  have hpair : ∑ i ∈ K, ∑ j ∈ D, r j < ∑ i ∈ K, ∑ j ∈ D, r i := by
    refine sum_lt_sum (fun i hi => sum_le_sum fun j hj => hsep i hi j hj) ?_
    refine ⟨i₀, hi₀, ?_⟩
    refine sum_lt_sum (fun j hj => hsep i₀ hi₀ j hj) ⟨j₀, hj₀, hlt⟩
  have hL : ∑ i ∈ K, ∑ j ∈ D, r j = (K.card : ℝ) * ∑ j ∈ D, r j := by
    simp [sum_const, nsmul_eq_mul, mul_comm]
  have hR : ∑ i ∈ K, ∑ j ∈ D, r i = (D.card : ℝ) * ∑ i ∈ K, r i := by
    simp_rw [sum_const, nsmul_eq_mul]
    exact (mul_sum K (fun i => r i) (D.card : ℝ)).symm
  rw [hL, hR] at hpair
  exact hpair
