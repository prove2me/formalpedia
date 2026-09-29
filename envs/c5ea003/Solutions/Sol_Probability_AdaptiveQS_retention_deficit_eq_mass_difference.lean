-- Prove2me | solution 1 for Probability.AdaptiveQS.retention_deficit_eq_mass_difference
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T08:13:42.025316+00:00
-- url     : https://prove2.me/submissions/48a8c342-3c81-4b4d-af5b-cfc9c74d00c0

import Mathlib
import Definitions.Def_Probability_AdaptiveQSAllocation
import Definitions.Def_Probability_AdaptiveQSDiscordance
import Definitions.Def_Probability_AdaptiveQSInversionMass
import Definitions.Def_Probability_AdaptiveQSSkipFlip
open Probability.AdaptiveQS Finset in
theorem solution {ι : Type*} [DecidableEq ι] {s : Finset ι} {d r : ι → ℝ} (θ : ℝ) :
    ((keepSet s d θ).card : ℝ) * (∑ i ∈ s, r i)
        - (s.card : ℝ) * (∑ i ∈ keepSet s d θ, r i)
      = keptInversionMass s d r θ - keptConcordanceMass s d r θ := by
  -- `max x 0 - max (-x) 0 = x`, so the two ledgers differ by the signed gaps
  have hmax : ∀ x : ℝ, max x 0 - max (-x) 0 = x := by
    intro x
    rcases le_total x 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
  have hrhs : keptInversionMass s d r θ - keptConcordanceMass s d r θ
      = ((keepSet s d θ).card : ℝ) * (∑ i ∈ skipSet s d θ, r i)
        - ((skipSet s d θ).card : ℝ) * (∑ i ∈ keepSet s d θ, r i) := by
    unfold keptInversionMass keptConcordanceMass
    rw [← sum_sub_distrib]
    have e : ∀ p ∈ skipSet s d θ ×ˢ keepSet s d θ,
        max (r p.1 - r p.2) 0 - max (r p.2 - r p.1) 0 = r p.1 - r p.2 := by
      intro p _
      have := hmax (r p.1 - r p.2)
      rw [neg_sub] at this
      exact this
    rw [sum_congr rfl e, sum_product]
    simp only [sum_sub_distrib, sum_const, nsmul_eq_mul]
    rw [← mul_sum]
  -- the population splits into kept and skipped targets
  have hsum : ∑ i ∈ s, r i = ∑ i ∈ keepSet s d θ, r i + ∑ i ∈ skipSet s d θ, r i := by
    unfold keepSet skipSet
    rw [sum_filter_add_sum_filter_not]
  have hcard : (s.card : ℝ) = (keepSet s d θ).card + (skipSet s d θ).card := by
    unfold keepSet skipSet
    exact_mod_cast (card_filter_add_card_filter_not (s := s) (fun i => θ ≤ d i)).symm
  rw [hrhs, hsum, hcard]
  ring
