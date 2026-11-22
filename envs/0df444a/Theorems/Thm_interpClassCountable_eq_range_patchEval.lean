-- Prove2me | Theorems.Thm_interpClassCountable_eq_range_patchEval
-- name    : interpClassCountable_eq_range_patchEval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:17.348162+00:00
-- url     : https://prove2.me/theorems/e245d1ad-c12e-46ab-98b0-019cb68da395
-- title:
--   interp Class Countable eq range patch Eval: interp Class Countable eq range patch Eval
-- statement:
--   interpClassCountable equals the range of patchEval with routerOfSetFamily.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Interpolation.lean#L127-L144
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Interpolation.lean#L127-L144

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

theorem interpClassCountable_eq_range_patchEval
    {X : Type u}
    {Θ₁ Θ₂ : Type*}
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (A : ℕ → Set X) :
    interpClassCountable (Set.range e₁) (Set.range e₂) A =
      Set.range (patchEval e₁ e₂ (routerOfSetFamily A)) := by sorry
