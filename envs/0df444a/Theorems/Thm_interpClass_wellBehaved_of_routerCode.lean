-- Prove2me | Theorems.Thm_interpClass_wellBehaved_of_routerCode
-- name    : interpClass_wellBehaved_of_routerCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:41:19.494646+00:00
-- url     : https://prove2.me/theorems/4a2dcdbb-9444-47d7-96c4-233eeed46942
-- title:
--   interp Class well Behaved of router Code: interp Class well Behaved of router Code
-- statement:
--   Conditional interpolation via BorelRouterCode is well-behaved:
--       the range of patchEval with a Borel router satisfies WellBehavedVCMeasTarget.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Interpolation.lean#L233-L246
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Interpolation.lean#L233-L246

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

theorem interpClass_wellBehaved_of_routerCode
    {X : Type u} [MeasurableSpace X] [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {Θ₁ Θ₂ : Type*}
    [MeasurableSpace Θ₁] [StandardBorelSpace Θ₁]
    [MeasurableSpace Θ₂] [StandardBorelSpace Θ₂]
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (he₁ : Measurable (fun p : Θ₁ × X => e₁ p.1 p.2))
    (he₂ : Measurable (fun p : Θ₂ × X => e₂ p.1 p.2))
    (R : BorelRouterCode X) :
    WellBehavedVCMeasTarget X
      (Set.range (letI := R.instMeasΡ; patchEval e₁ e₂ R.eval)) := by sorry
