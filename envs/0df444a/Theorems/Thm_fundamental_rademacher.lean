-- Prove2me | Theorems.Thm_fundamental_rademacher
-- name    : fundamental_rademacher
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:36:53.122968+00:00
-- url     : https://prove2.me/theorems/d2c64b63-279f-48a2-a570-6487f5821ad7
-- title:
--   fundamental rademacher: fundamental rademacher
-- statement:
--   Fundamental theorem: Rademacher complexity characterization.
--       BP₅: two asymmetric directions crossing different paradigm joints.
--       Uses uniform vanishing (∃ m₀ ∀ D), which is the textbook-standard form.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/PAC.lean#L251-L281
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/PAC.lean#L251-L281

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

theorem fundamental_rademacher (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool)
    [MeasurableConceptClass X C] :
    PACLearnable X C ↔
    (∀ ε > 0, ∃ m₀, ∀ (D : MeasureTheory.Measure X),
      MeasureTheory.IsProbabilityMeasure D →
      ∀ m ≥ m₀, RademacherComplexity X C D m < ε) := by sorry
