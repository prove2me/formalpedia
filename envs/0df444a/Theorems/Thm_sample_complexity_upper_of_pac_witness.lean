-- Prove2me | Theorems.Thm_sample_complexity_upper_of_pac_witness
-- name    : sample_complexity_upper_of_pac_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:36:41.291641+00:00
-- url     : https://prove2.me/theorems/4072f9ef-f7c7-4664-92a9-1896267f9e54
-- title:
--   sample complexity upper of pac witness: sample complexity upper of pac witness
-- statement:
--   Any PAC witness (L, mf) gives an upper bound on SampleComplexity:
--       the infimum is at most the witness sample size.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/PAC.lean#L180-L197
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/PAC.lean#L180-L197

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Compression
public import Definitions.Def_LeanPool_FormalLearningTheory_Bridge
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GeneralizationResults
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_PAC
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem sample_complexity_upper_of_pac_witness (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool)
    (L : BatchLearner X Bool) (mf : ℝ → ℝ → ℕ)
    (hPAC :
      ∀ (ε δ : ℝ), 0 < ε → 0 < δ →
        ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
          ∀ c ∈ C,
            MeasureTheory.Measure.pi (fun _ : Fin (mf ε δ) => D)
              { xs : Fin (mf ε δ) → X |
                D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                  ≤ ENNReal.ofReal ε }
              ≥ ENNReal.ofReal (1 - δ)) :
    ∀ (ε δ : ℝ), 0 < ε → 0 < δ →
      SampleComplexity X C ε δ ≤ mf ε δ := by sorry
