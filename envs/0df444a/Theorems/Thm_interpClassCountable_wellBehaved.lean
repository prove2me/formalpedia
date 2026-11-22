-- Prove2me | Theorems.Thm_interpClassCountable_wellBehaved
-- name    : interpClassCountable_wellBehaved
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:41:16.825067+00:00
-- url     : https://prove2.me/theorems/39461170-0d95-415c-be12-e348bff42a15
-- title:
--   interp Class Countable well Behaved: interp Class Countable well Behaved
-- statement:
--   Countable-family interpolation of Borel-parameterized classes is well-behaved.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Interpolation.lean#L163-L175
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Interpolation.lean#L163-L175

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Interpolation
set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory
attribute [local instance] Classical.propDecidable

theorem interpClassCountable_wellBehaved
    {X : Type u} [MeasurableSpace X] [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {Θ₁ Θ₂ : Type*}
    [MeasurableSpace Θ₁] [StandardBorelSpace Θ₁]
    [MeasurableSpace Θ₂] [StandardBorelSpace Θ₂]
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (he₁ : Measurable (fun p : Θ₁ × X => e₁ p.1 p.2))
    (he₂ : Measurable (fun p : Θ₂ × X => e₂ p.1 p.2))
    {A : ℕ → Set X} (hA : ∀ n, MeasurableSet (A n)) :
    WellBehavedVCMeasTarget X (interpClassCountable (Set.range e₁) (Set.range e₂) A) := by sorry
