-- Prove2me | Theorems.Thm_interpClassFixed_wellBehaved
-- name    : interpClassFixed_wellBehaved
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:41:10.726635+00:00
-- url     : https://prove2.me/theorems/20ad6c68-dc5e-4be7-ac39-12e3efa1ade0
-- title:
--   interp Class Fixed well Behaved: interp Class Fixed well Behaved
-- statement:
--   Fixed-region interpolation of Borel-parameterized classes is well-behaved.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Interpolation.lean#L149-L160
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Interpolation.lean#L149-L160

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

theorem interpClassFixed_wellBehaved
    {X : Type u} [MeasurableSpace X] [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {Θ₁ Θ₂ : Type*}
    [MeasurableSpace Θ₁] [StandardBorelSpace Θ₁]
    [MeasurableSpace Θ₂] [StandardBorelSpace Θ₂]
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (he₁ : Measurable (fun p : Θ₁ × X => e₁ p.1 p.2))
    (he₂ : Measurable (fun p : Θ₂ × X => e₂ p.1 p.2))
    {A : Set X} (hA : MeasurableSet A) :
    WellBehavedVCMeasTarget X (interpClassFixed (Set.range e₁) (Set.range e₂) A) := by sorry
