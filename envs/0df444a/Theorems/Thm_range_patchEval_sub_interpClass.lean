-- Prove2me | Theorems.Thm_range_patchEval_sub_interpClass
-- name    : range_patchEval_sub_interpClass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:41:16.466191+00:00
-- url     : https://prove2.me/theorems/a7147e38-d8aa-418e-be67-2077f9a9f63d
-- title:
--   range patch Eval sub interp Class: range patch Eval sub interp Class
-- statement:
--   The range of patchEval with a BorelRouterCode is contained in interpClass.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Interpolation.lean#L213-L229
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Interpolation.lean#L213-L229

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

theorem range_patchEval_sub_interpClass
    {X : Type u} [MeasurableSpace X]
    {Θ₁ Θ₂ : Type*}
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (R : BorelRouterCode X) :
    Set.range (letI := R.instMeasΡ; patchEval e₁ e₂ R.eval) ⊆
      interpClass (Set.range e₁) (Set.range e₂) := by sorry
