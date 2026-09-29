-- Prove2me | solution 1 for Probability.AdaptiveQS.approx_dial_retention
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T08:39:01.030592+00:00
-- url     : https://prove2.me/submissions/cf3fe40a-c101-42c8-8134-fef47f6de9fa

import Mathlib
import Definitions.Def_Probability_AdaptiveQSAllocation
import Definitions.Def_Probability_AdaptiveQSSkipFlip
open Probability.AdaptiveQS Finset in
theorem solution {ι : Type*} [DecidableEq ι] {s : Finset ι} {d r : ι → ℝ} {ε : ℝ}
    (hε : ∀ i ∈ s, |d i - r i| ≤ ε) (θ : ℝ) :
    ((keepSet s d θ).card : ℝ) * (∑ i ∈ s, r i)
      ≤ (s.card : ℝ) * (∑ i ∈ keepSet s d θ, r i)
        + 2 * ε * (keepSet s d θ).card * (skipSet s d θ).card := by
  set K := keepSet s d θ with hK
  set D := skipSet s d θ with hD
  -- split the population into kept and skipped targets
  have hsum : ∑ i ∈ s, r i = ∑ i ∈ K, r i + ∑ i ∈ D, r i := by
    rw [hK, hD]
    unfold keepSet skipSet
    rw [sum_filter_add_sum_filter_not]
  have hcard : (s.card : ℝ) = K.card + D.card := by
    rw [hK, hD]
    unfold keepSet skipSet
    exact_mod_cast (card_filter_add_card_filter_not (s := s) (fun i => θ ≤ d i)).symm
  -- the retention deficit is the sum of gaps `r j - r k` over skipped `j`, kept `k`
  have hdouble : ∑ j ∈ D, ∑ k ∈ K, (r j - r k)
      = (K.card : ℝ) * ∑ j ∈ D, r j - (D.card : ℝ) * ∑ k ∈ K, r k := by
    simp only [sum_sub_distrib, sum_const, nsmul_eq_mul]
    rw [← mul_sum]
  -- each gap is below `2ε`: the dial orders them, and it is within `ε` of the truth
  have hgap : ∀ j ∈ D, ∀ k ∈ K, r j - r k ≤ 2 * ε := by
    intro j hj k hk
    rw [hD] at hj
    rw [hK] at hk
    unfold skipSet at hj
    unfold keepSet at hk
    rw [mem_filter] at hj hk
    have h1 := abs_le.mp (hε j hj.1)
    have h2 := abs_le.mp (hε k hk.1)
    have h3 : d j < d k := lt_of_lt_of_le (not_le.mp hj.2) hk.2
    linarith [h1.1, h1.2, h2.1, h2.2]
  have hbound : ∑ j ∈ D, ∑ k ∈ K, (r j - r k) ≤ D.card * (K.card * (2 * ε)) := by
    calc ∑ j ∈ D, ∑ k ∈ K, (r j - r k) ≤ ∑ _j ∈ D, ∑ _k ∈ K, 2 * ε :=
          sum_le_sum fun j hj => sum_le_sum fun k hk => hgap j hj k hk
      _ = D.card * (K.card * (2 * ε)) := by simp [sum_const, nsmul_eq_mul]
  rw [hsum, hcard]
  nlinarith [hdouble, hbound]
