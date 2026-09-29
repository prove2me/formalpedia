-- Prove2me | solution 1 for MarkovChainCLT.indicator_cov_le_phi
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-04T23:04:50.639927+00:00
-- url     : https://prove2.me/submissions/2a581ea8-573b-4ee5-9b36-2d1759e9b12f

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n k : ℕ)
    (A B : Set Ω)
    (hA : MeasurableSet[processSigma Y (Set.Iic k)] A)
    (hA0 : P A ≠ 0)
    (hB : MeasurableSet[processSigma Y (Set.Ici (k + n))] B) :
    |(P (A ∩ B)).toReal - (P A).toReal * (P B).toReal| ≤ phiMixingCoef P Y n := by
  -- Key element of the phi-sup
  have hPA_fin : P A ≠ ⊤ := measure_ne_top P A
  have hPA_pos : 0 < (P A).toReal := ENNReal.toReal_pos hA0 hPA_fin
  have hPA_le_one : (P A).toReal ≤ 1 := by
    have h : P A ≤ 1 := by
      calc P A ≤ P Set.univ := measure_mono (Set.subset_univ A)
        _ = 1 := measure_univ
    exact ENNReal.toReal_mono (by simp) h
  have hPA_nonneg : 0 ≤ (P A).toReal := ENNReal.toReal_nonneg
  -- the phi-element for our k, A, B
  have hmem : |(P (A ∩ B)).toReal / (P A).toReal - (P B).toReal| ∈
      {r | ∃ k' : ℕ, ∃ A' B' : Set Ω,
        MeasurableSet[processSigma Y (Set.Iic k')] A' ∧ P A' ≠ 0 ∧
        MeasurableSet[processSigma Y (Set.Ici (k' + n))] B' ∧
        r = |(P (A' ∩ B')).toReal / (P A').toReal - (P B').toReal|} :=
    ⟨k, A, B, hA, hA0, hB, rfl⟩
  -- boundedness of the phi-set by 1
  have hbdd : BddAbove
      {r | ∃ k' : ℕ, ∃ A' B' : Set Ω,
        MeasurableSet[processSigma Y (Set.Iic k')] A' ∧ P A' ≠ 0 ∧
        MeasurableSet[processSigma Y (Set.Ici (k' + n))] B' ∧
        r = |(P (A' ∩ B')).toReal / (P A').toReal - (P B').toReal|} := by
    use 1
    intro r hr
    obtain ⟨k', A', B', _, hA'0, _, rfl⟩ := hr
    have h1 : (P B').toReal ≤ 1 := by
      have h : P B' ≤ 1 := by
        calc P B' ≤ P Set.univ := measure_mono (Set.subset_univ B')
          _ = 1 := measure_univ
      exact ENNReal.toReal_mono (by simp) h
    have h2 : (P (A' ∩ B')).toReal / (P A').toReal ≤ 1 := by
      have hsub : P (A' ∩ B') ≤ P A' := measure_mono Set.inter_subset_left
      have hle : (P (A' ∩ B')).toReal ≤ (P A').toReal :=
        ENNReal.toReal_mono (measure_ne_top P _) hsub
      have hpos : 0 < (P A').toReal := ENNReal.toReal_pos hA'0 (measure_ne_top P _)
      rw [div_le_one hpos]
      exact hle
    have hnn1 : 0 ≤ (P B').toReal := ENNReal.toReal_nonneg
    have hnn2 : 0 ≤ (P (A' ∩ B')).toReal / (P A').toReal := by positivity
    -- |a - b| ≤ 1 for a,b ∈ [0,1]
    rw [abs_le]
    constructor <;> linarith
  have hle : |(P (A ∩ B)).toReal / (P A).toReal - (P B).toReal| ≤ phiMixingCoef P Y n := by
    unfold phiMixingCoef
    exact le_csSup hbdd hmem
  -- factor (P A).toReal
  have hfactor : (P (A ∩ B)).toReal - (P A).toReal * (P B).toReal =
      (P A).toReal * ((P (A ∩ B)).toReal / (P A).toReal - (P B).toReal) := by
    field_simp
  rw [hfactor, abs_mul]
  have hPA_abs : |(P A).toReal| = (P A).toReal := abs_of_nonneg hPA_nonneg
  rw [hPA_abs]
  calc (P A).toReal * |((P (A ∩ B)).toReal / (P A).toReal - (P B).toReal)|
      ≤ 1 * phiMixingCoef P Y n := by
        apply mul_le_mul hPA_le_one hle (abs_nonneg _) (by positivity)
    _ = phiMixingCoef P Y n := one_mul _
