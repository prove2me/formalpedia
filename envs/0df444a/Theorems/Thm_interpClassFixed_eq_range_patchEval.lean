-- Prove2me | Theorems.Thm_interpClassFixed_eq_range_patchEval
-- name    : interpClassFixed_eq_range_patchEval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:17.143992+00:00
-- url     : https://prove2.me/theorems/b0b6b357-9737-4e0f-b9cf-a2bf81a7e275
-- title:
--   interp Class Fixed eq range patch Eval: interp Class Fixed eq range patch Eval
-- statement:
--   interpClassFixed equals the range of patchEval with routerOfSet.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Interpolation.lean#L107-L124
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Interpolation.lean#L107-L124

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

theorem interpClassFixed_eq_range_patchEval
    {X : Type u}
    {Θ₁ Θ₂ : Type*}
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (A : Set X) :
    interpClassFixed (Set.range e₁) (Set.range e₂) A =
      Set.range (patchEval e₁ e₂ (routerOfSet A)) := by sorry
