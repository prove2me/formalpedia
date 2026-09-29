-- Prove2me | solution 1 for FactoringLab.depth_advantage_collapse
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T06:50:52.351003+00:00
-- url     : https://prove2.me/submissions/484d1dc9-4309-46f7-8b86-6ca8e2968192

import Mathlib
import Definitions.Def_Probability_AdaptiveBarrier
import Definitions.Def_Probability_QuantizedBarrier
import Definitions.Def_Probability_StructuralOrthogonality

open FactoringLab QTree Finset in
theorem solution {ι κ : Type*} [DecidableEq κ] (Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ)
    (V : Finset ℝ) (hV : V.Nonempty) :
    ∀ t : QTree ι, t.BandOnly Ω n → (∀ i ∈ Ω, t.eval i ∈ V) →
      quantErr Ω n Y V hV + ∑ i ∈ Ω, (bandMean Ω n Y i - Y i) ^ 2
        ≤ ∑ i ∈ Ω, (t.eval i - Y i) ^ 2 := by
  intro t ht hval
  -- band-only trees evaluate band-measurably
  have hmeas : ∀ s : QTree ι, s.BandOnly Ω n → BandMeasurable Ω n s.eval := by
    intro s
    induction s with
    | leaf v =>
      intro _ i _ j _ _
      rfl
    | node tst l r ihl ihr =>
      intro hs i hi j hj hij
      obtain ⟨htst, hl, hr⟩ := hs
      simp only [eval]
      rw [htst i hi j hj hij, ihl hl i hi j hj hij, ihr hr i hi j hj hij]
  have hbandeq : ∀ i ∈ Ω, ∀ j ∈ Ω, n i = n j → band Ω n i = band Ω n j := by
    intro i _ j _ hij
    unfold band
    rw [hij]
  have hmmeas : BandMeasurable Ω n (bandMean Ω n Y) := by
    intro i hi j hj hij
    unfold bandMean
    rw [hbandeq i hi j hj hij]
  -- orthogonality of band-measurable functions to the residual `m - Y`
  have horth : ∀ h : ι → ℝ, BandMeasurable Ω n h →
      ∑ i ∈ Ω, h i * (bandMean Ω n Y i - Y i) = 0 := by
    intro h hh
    have h1 : ∑ i ∈ Ω, h i * bandMean Ω n Y i
        = ∑ i ∈ Ω, ∑ j ∈ band Ω n i, h i * Y j / (band Ω n i).card := by
      refine sum_congr rfl fun i _ => ?_
      unfold bandMean
      rw [mul_div_assoc', mul_sum, sum_div]
    have h2 : ∑ i ∈ Ω, ∑ j ∈ band Ω n i, h i * Y j / (band Ω n i).card
        = ∑ j ∈ Ω, ∑ i ∈ band Ω n j, h i * Y j / (band Ω n i).card := by
      apply Finset.sum_comm'
      intro i j
      simp only [band, mem_filter]
      constructor
      · rintro ⟨hi, hj, hji⟩
        exact ⟨⟨hi, hji.symm⟩, hj⟩
      · rintro ⟨⟨hi, hij⟩, hj⟩
        exact ⟨hi, hj, hij.symm⟩
    have h3 : ∀ j ∈ Ω, ∑ i ∈ band Ω n j, h i * Y j / (band Ω n i).card = h j * Y j := by
      intro j hj
      have hjb : j ∈ band Ω n j := mem_filter.2 ⟨hj, rfl⟩
      have hc : ((band Ω n j).card : ℝ) ≠ 0 := by
        exact_mod_cast (card_pos.2 ⟨j, hjb⟩).ne'
      calc ∑ i ∈ band Ω n j, h i * Y j / (band Ω n i).card
          = ∑ i ∈ band Ω n j, h j * Y j / (band Ω n j).card := by
            refine sum_congr rfl fun i hi => ?_
            obtain ⟨hiΩ, hij⟩ := mem_filter.1 hi
            rw [hh i hiΩ j hj hij, hbandeq i hiΩ j hj hij]
        _ = (band Ω n j).card * (h j * Y j / (band Ω n j).card) := by
            rw [sum_const, nsmul_eq_mul]
        _ = h j * Y j := by
            field_simp
    have h4 : ∑ i ∈ Ω, h i * (bandMean Ω n Y i - Y i)
        = ∑ i ∈ Ω, h i * bandMean Ω n Y i - ∑ i ∈ Ω, h i * Y i := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun i _ => by ring
    rw [h4, h1, h2, sum_congr rfl h3, sub_self]
  -- Pythagoras, then quantisation
  have hdiff : BandMeasurable Ω n (fun i => t.eval i - bandMean Ω n Y i) := by
    intro i hi j hj hij
    simp only
    rw [hmeas t ht i hi j hj hij, hmmeas i hi j hj hij]
  have hpyth : ∑ i ∈ Ω, (t.eval i - Y i) ^ 2
      = ∑ i ∈ Ω, (t.eval i - bandMean Ω n Y i) ^ 2 + ∑ i ∈ Ω, (bandMean Ω n Y i - Y i) ^ 2 := by
    have hcross := horth _ hdiff
    have e : ∑ i ∈ Ω, (t.eval i - Y i) ^ 2
        = ∑ i ∈ Ω, (t.eval i - bandMean Ω n Y i) ^ 2 + ∑ i ∈ Ω, (bandMean Ω n Y i - Y i) ^ 2
          + 2 * ∑ i ∈ Ω, (t.eval i - bandMean Ω n Y i) * (bandMean Ω n Y i - Y i) := by
      rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun i _ => by ring
    rw [e, hcross, mul_zero, add_zero]
  have hq : quantErr Ω n Y V hV ≤ ∑ i ∈ Ω, (t.eval i - bandMean Ω n Y i) ^ 2 := by
    unfold quantErr
    exact sum_le_sum fun i hi => Finset.inf'_le _ (hval i hi)
  rw [hpyth]
  linarith
