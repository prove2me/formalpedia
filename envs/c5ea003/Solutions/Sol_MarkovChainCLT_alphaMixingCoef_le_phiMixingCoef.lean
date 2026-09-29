-- Prove2me | solution 1 for MarkovChainCLT.alphaMixingCoef_le_phiMixingCoef
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-04T23:02:29.870172+00:00
-- url     : https://prove2.me/submissions/9620f470-effc-4963-a1d7-41522cd907c0

import Definitions.Def_MixingCoefficients
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory

namespace AlphaPhiAux

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- The set defining `phiMixingCoef` is bounded above by `1`. -/
theorem bddAbove_phiSet (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n : ℕ) :
    BddAbove {r | ∃ k : ℕ, ∃ A B : Set Ω,
      MeasurableSet[processSigma Y (Set.Iic k)] A ∧ P A ≠ 0 ∧
      MeasurableSet[processSigma Y (Set.Ici (k + n))] B ∧
      r = |(P (A ∩ B)).toReal / (P A).toReal - (P B).toReal|} := by
  refine ⟨1, ?_⟩
  rintro r ⟨k, A, B, -, hA0, -, rfl⟩
  have hAne : (P A).toReal ≠ 0 := by
    simp only [ne_eq, ENNReal.toReal_eq_zero_iff, not_or]
    exact ⟨hA0, measure_ne_top P A⟩
  have hApos : 0 < (P A).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hAne)
  have hq0 : 0 ≤ (P (A ∩ B)).toReal / (P A).toReal :=
    div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hq1 : (P (A ∩ B)).toReal / (P A).toReal ≤ 1 := by
    rw [div_le_one hApos]
    exact ENNReal.toReal_mono (measure_ne_top P A) (measure_mono Set.inter_subset_left)
  have hB0 : 0 ≤ (P B).toReal := ENNReal.toReal_nonneg
  have hB1 : (P B).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ) (measure_mono (Set.subset_univ B))
  rw [abs_le]
  constructor <;> linarith

/-- The uniform mixing coefficient of a probability measure is nonnegative. -/
theorem phiMixingCoef_nonneg (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n : ℕ) :
    0 ≤ phiMixingCoef P Y n := by
  refine le_csSup (bddAbove_phiSet P Y n) ⟨0, Set.univ, Set.univ, MeasurableSet.univ, ?_,
    MeasurableSet.univ, ?_⟩
  · simp
  · simp

/-- Each admissible conditional deviation is bounded by the uniform mixing coefficient. -/
theorem abs_condDeviation_le_phiMixingCoef (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → E) (n k : ℕ) {A B : Set Ω}
    (hA : MeasurableSet[processSigma Y (Set.Iic k)] A) (hA0 : P A ≠ 0)
    (hB : MeasurableSet[processSigma Y (Set.Ici (k + n))] B) :
    |(P (A ∩ B)).toReal / (P A).toReal - (P B).toReal| ≤ phiMixingCoef P Y n :=
  le_csSup (bddAbove_phiSet P Y n) ⟨k, A, B, hA, hA0, hB, rfl⟩

/-- **`α(n) ≤ φ(n)`.** For a probability measure the strong mixing coefficient is at most the
uniform mixing coefficient. -/
theorem alphaMixingCoef_le_phiMixingCoef_aux (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → E) (n : ℕ) :
    alphaMixingCoef P Y n ≤ phiMixingCoef P Y n := by
  refine csSup_le ⟨0, ⟨0, ∅, ∅, @MeasurableSet.empty Ω (processSigma Y (Set.Iic 0)),
    @MeasurableSet.empty Ω (processSigma Y (Set.Ici (0 + n))), by simp⟩⟩ ?_
  rintro r ⟨k, A, B, hA, hB, rfl⟩
  rcases eq_or_ne (P A) 0 with hA0 | hA0
  · have hAB : P (A ∩ B) = 0 :=
      measure_mono_null Set.inter_subset_left hA0
    simp [hAB, hA0, phiMixingCoef_nonneg P Y n]
  · have hAle : (P A).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ) (measure_mono (Set.subset_univ A))
    have hApos : 0 < (P A).toReal := by
      refine lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm ?_)
      simp only [ne_eq, ENNReal.toReal_eq_zero_iff, not_or]
      exact ⟨hA0, measure_ne_top P A⟩
    have hkey := abs_condDeviation_le_phiMixingCoef P Y n k hA hA0 hB
    have hmul : (P A).toReal * ((P (A ∩ B)).toReal / (P A).toReal - (P B).toReal)
        = (P (A ∩ B)).toReal - (P A).toReal * (P B).toReal := by
      field_simp
    have heq : |(P (A ∩ B)).toReal - (P A).toReal * (P B).toReal| =
        (P A).toReal * |(P (A ∩ B)).toReal / (P A).toReal - (P B).toReal| := by
      rw [← hmul, abs_mul, abs_of_pos hApos]
    rw [heq]
    calc (P A).toReal * |(P (A ∩ B)).toReal / (P A).toReal - (P B).toReal|
        ≤ 1 * |(P (A ∩ B)).toReal / (P A).toReal - (P B).toReal| := by
          exact mul_le_mul_of_nonneg_right hAle (abs_nonneg _)
      _ = |(P (A ∩ B)).toReal / (P A).toReal - (P B).toReal| := one_mul _
      _ ≤ phiMixingCoef P Y n := hkey

end AlphaPhiAux

theorem solution {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n : ℕ) :
    alphaMixingCoef P Y n ≤ phiMixingCoef P Y n :=
  AlphaPhiAux.alphaMixingCoef_le_phiMixingCoef_aux P Y n
