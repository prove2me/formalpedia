-- Prove2me | solution 1 for MarkovChainCLT.indicator_cov_le_phi_general
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-04T23:15:44.593094+00:00
-- url     : https://prove2.me/submissions/f5207451-f370-49dc-ac05-918f5af0520d

import Definitions.Def_MixingCoefficients
import Theorems.Thm_MarkovChainCLT_indicator_cov_le_phi

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n k : ℕ)
    (A B : Set Ω)
    (hA : MeasurableSet[processSigma Y (Set.Iic k)] A)
    (hB : MeasurableSet[processSigma Y (Set.Ici (k + n))] B) :
    |(P (A ∩ B)).toReal - (P A).toReal * (P B).toReal| ≤ phiMixingCoef P Y n := by
  by_cases hA0 : P A = 0
  · -- P A = 0 forces P (A ∩ B) = 0, so LHS = 0; phi >= 0 since 0 is in the sup
    have hsub : P (A ∩ B) ≤ P A := measure_mono Set.inter_subset_left
    have hAB0 : P (A ∩ B) = 0 := le_antisymm (hsub.trans_eq hA0) (by simp)
    have hLHS : |(P (A ∩ B)).toReal - (P A).toReal * (P B).toReal| = 0 := by
      simp [hAB0, hA0]
    -- 0 ≤ phi: witness k'=0, A'=univ, B'=∅ gives element 0
    have h0mem : (0 : ℝ) ∈ {r | ∃ k' : ℕ, ∃ A' B' : Set Ω,
        MeasurableSet[processSigma Y (Set.Iic k')] A' ∧ P A' ≠ 0 ∧
        MeasurableSet[processSigma Y (Set.Ici (k' + n))] B' ∧
        r = |(P (A' ∩ B')).toReal / (P A').toReal - (P B').toReal|} := by
      refine ⟨0, Set.univ, Set.univ, MeasurableSet.univ, ?_, MeasurableSet.univ, ?_⟩
      · simp
      · simp [measure_univ]
    have hbdd : BddAbove {r | ∃ k' : ℕ, ∃ A' B' : Set Ω,
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
        have hsub2 : P (A' ∩ B') ≤ P A' := measure_mono Set.inter_subset_left
        have hle : (P (A' ∩ B')).toReal ≤ (P A').toReal :=
          ENNReal.toReal_mono (measure_ne_top P _) hsub2
        have hpos : 0 < (P A').toReal := ENNReal.toReal_pos hA'0 (measure_ne_top P _)
        rw [div_le_one hpos]
        exact hle
      have hnn1 : 0 ≤ (P B').toReal := ENNReal.toReal_nonneg
      have hnn2 : 0 ≤ (P (A' ∩ B')).toReal / (P A').toReal := by positivity
      rw [abs_le]
      constructor <;> linarith
    have h0le : (0 : ℝ) ≤ phiMixingCoef P Y n := by
      unfold phiMixingCoef
      exact le_csSup hbdd h0mem
    rw [hLHS]
    exact h0le
  · exact MarkovChainCLT.indicator_cov_le_phi P Y n k A B hA hA0 hB
