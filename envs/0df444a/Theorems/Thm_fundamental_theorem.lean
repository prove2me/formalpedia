-- Prove2me | Theorems.Thm_fundamental_theorem
-- name    : fundamental_theorem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:39:56.995919+00:00
-- url     : https://prove2.me/theorems/465eae9a-ea20-4708-bac5-304164e9c030
-- title:
--   fundamental theorem: fundamental theorem
-- statement:
--   Fundamental theorem of statistical learning (5-way equivalence, BP₅).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/PAC.lean#L284-L320
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/PAC.lean#L284-L320

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

theorem fundamental_theorem (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool)
    [MeasurableConceptClass X C] :
    (PACLearnable X C ↔ VCDim X C < ⊤) ∧
    ((VCDim X C < ⊤) ↔ ∃ (k : ℕ) (cs : CompressionSchemeWithInfo0 X Bool C), cs.size = k) ∧
    ((VCDim X C < ⊤) ↔
      ∀ ε > 0, ∃ m₀, ∀ (D : MeasureTheory.Measure X),
        MeasureTheory.IsProbabilityMeasure D →
        ∀ m ≥ m₀, RademacherComplexity X C D m < ε) ∧
    (PACLearnable X C →
      ∃ (L : BatchLearner X Bool) (mf : ℝ → ℝ → ℕ),
        (∀ (ε δ : ℝ), 0 < ε → 0 < δ →
          ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
            ∀ c ∈ C,
              MeasureTheory.Measure.pi (fun _ : Fin (mf ε δ) => D)
                { xs : Fin (mf ε δ) → X |
                  D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                    ≤ ENNReal.ofReal ε }
                ≥ ENNReal.ofReal (1 - δ)) ∧
        (∀ (ε δ : ℝ), 0 < ε → 0 < δ →
          SampleComplexity X C ε δ ≤ mf ε δ) ∧
        (∀ (d : ℕ), VCDim X C = d →
          ∀ (ε δ : ℝ), 0 < ε → ε ≤ 1 / 4 →
            0 < δ → δ ≤ 1 → δ ≤ 1 / 7 → 1 ≤ d →
            Nat.ceil ((d - 1 : ℝ) / 2) ≤ SampleComplexity X C ε δ ∧
            Nat.ceil ((d - 1 : ℝ) / 2) ≤ mf ε δ)) ∧
    ((VCDim X C < ⊤) ↔
      ∃ (d : ℕ), ∀ (m : ℕ), d ≤ m →
        GrowthFunction X C m ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose m i) := by sorry
