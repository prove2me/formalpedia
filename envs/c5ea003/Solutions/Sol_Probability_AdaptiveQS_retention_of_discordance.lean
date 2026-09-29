-- Prove2me | solution 1 for Probability.AdaptiveQS.retention_of_discordance
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T08:43:15.904985+00:00
-- url     : https://prove2.me/submissions/f525fe4f-0658-409d-b8e8-60a900793230

import Mathlib
import Definitions.Def_Probability_AdaptiveQSAllocation
import Definitions.Def_Probability_AdaptiveQSDiscordance
import Definitions.Def_Probability_AdaptiveQSSkipFlip
open Probability.AdaptiveQS Finset in
theorem solution {ι : Type*} [DecidableEq ι] {s : Finset ι} {d r : ι → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hnonneg : ∀ i ∈ s, 0 ≤ r i) (hle : ∀ i ∈ s, r i ≤ M) (θ : ℝ) :
    ((keepSet s d θ).card : ℝ) * (∑ i ∈ s, r i)
      ≤ (s.card : ℝ) * (∑ i ∈ keepSet s d θ, r i)
        + M * (discordantPairs s d r).card := by
  set K := keepSet s d θ with hK
  set D := skipSet s d θ with hD
  have hsum : ∑ i ∈ s, r i = ∑ i ∈ K, r i + ∑ i ∈ D, r i := by
    rw [hK, hD]
    unfold keepSet skipSet
    rw [sum_filter_add_sum_filter_not]
  have hcard : (s.card : ℝ) = K.card + D.card := by
    rw [hK, hD]
    unfold keepSet skipSet
    exact_mod_cast (card_filter_add_card_filter_not (s := s) (fun i => θ ≤ d i)).symm
  -- the deficit is the sum of gaps over skipped × kept pairs
  have hdouble : ∑ j ∈ D, ∑ k ∈ K, (r j - r k)
      = (K.card : ℝ) * ∑ j ∈ D, r j - (D.card : ℝ) * ∑ k ∈ K, r k := by
    simp only [sum_sub_distrib, sum_const, nsmul_eq_mul]
    rw [← mul_sum]
  -- a positive gap only occurs on a discordant pair, and is at most `M`
  have hterm : ∀ p ∈ D ×ˢ K, r p.1 - r p.2
      ≤ if d p.1 < d p.2 ∧ r p.2 < r p.1 then M else 0 := by
    intro p hp
    rw [mem_product] at hp
    obtain ⟨hj, hk⟩ := hp
    rw [hD] at hj
    rw [hK] at hk
    unfold skipSet at hj
    unfold keepSet at hk
    rw [mem_filter] at hj hk
    have hdl : d p.1 < d p.2 := lt_of_lt_of_le (not_le.mp hj.2) hk.2
    split_ifs with hc
    · linarith [hle p.1 hj.1, hnonneg p.2 hk.1]
    · have : r p.1 ≤ r p.2 := by
        by_contra hlt
        exact hc ⟨hdl, not_le.mp hlt⟩
      linarith
  have hsub : (D ×ˢ K).filter (fun p => d p.1 < d p.2 ∧ r p.2 < r p.1) ⊆ discordantPairs s d r := by
    intro p hp
    rw [mem_filter, mem_product] at hp
    unfold discordantPairs
    rw [mem_filter, mem_product]
    refine ⟨⟨?_, ?_⟩, hp.2⟩
    · have := hp.1.1
      rw [hD] at this
      unfold skipSet at this
      exact (mem_filter.mp this).1
    · have := hp.1.2
      rw [hK] at this
      unfold keepSet at this
      exact (mem_filter.mp this).1
  have hbound : ∑ j ∈ D, ∑ k ∈ K, (r j - r k) ≤ M * (discordantPairs s d r).card := by
    rw [← sum_product (f := fun p : ι × ι => r p.1 - r p.2)]
    calc ∑ p ∈ D ×ˢ K, (r p.1 - r p.2)
        ≤ ∑ p ∈ D ×ˢ K, (if d p.1 < d p.2 ∧ r p.2 < r p.1 then M else 0) := sum_le_sum hterm
      _ = M * ((D ×ˢ K).filter (fun p => d p.1 < d p.2 ∧ r p.2 < r p.1)).card := by
          rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ M * (discordantPairs s d r).card :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_card hsub) hM
  rw [hsum, hcard]
  nlinarith [hdouble, hbound]
