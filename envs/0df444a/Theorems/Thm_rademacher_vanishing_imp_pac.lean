-- Prove2me | Theorems.Thm_rademacher_vanishing_imp_pac
-- name    : rademacher_vanishing_imp_pac
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:05.171907+00:00
-- url     : https://prove2.me/theorems/e831fe2d-9855-4634-a93a-7b9366c94854
-- title:
--   rademacher vanishing imp pac: rademacher vanishing imp pac
-- statement:
--   Rademacher vanishing → PAC learnability (← direction of fundamental_rademacher).
--       Uses uniform vanishing (∃ m₀ ∀ D), the textbook-standard form.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GeneralizationResults.lean#L261-L283
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GeneralizationResults.lean#L261-L283

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GeneralizationResults
public import Theorems.Thm_MeasurableConceptClass_hWB
public import Theorems.Thm_MeasurableConceptClass_hc_meas

set_option autoImplicit true
@[expose] public section
public section
universe u
attribute [local instance] Classical.propDecidable

theorem rademacher_vanishing_imp_pac (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : ∀ c : Concept X Bool, Measurable c)
    (hWB : WellBehavedVC X C)
    (hrad : ∀ ε > 0, ∃ m₀, ∀ (D : MeasureTheory.Measure X),
      MeasureTheory.IsProbabilityMeasure D →
      ∀ m ≥ m₀, RademacherComplexity X C D m < ε) :
    PACLearnable X C := by sorry
