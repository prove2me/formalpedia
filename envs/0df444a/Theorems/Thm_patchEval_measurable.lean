-- Prove2me | Theorems.Thm_patchEval_measurable
-- name    : patchEval_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:21.806047+00:00
-- url     : https://prove2.me/theorems/ca1e649d-62b7-42b1-b80f-c24b187928ff
-- title:
--   patch Eval measurable: patch Eval measurable
-- statement:
--   Closure under patching: if `e₁ : Θ₁ → Concept X`, `e₂ : Θ₂ → Concept X`, and a
--   region selector `r : Ρ → Concept X Bool` are jointly measurable, then so is the
--   piecewise evaluation
--   `(θ₁, θ₂, ρ, x) ↦ if r ρ x then e₁ θ₁ x else e₂ θ₂ x`
--   on the combined parameter space. The basic compositional fact behind
--   `patch_borel_param_wellBehavedVCMeasTarget`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/BorelAnalyticBridge.lean#L240-L261
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/BorelAnalyticBridge.lean#L240-L261

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_AnalyticMeasurability
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory

theorem patchEval_measurable
    {X : Type u} [MeasurableSpace X]
    {Θ₁ Θ₂ Ρ : Type*} [MeasurableSpace Θ₁] [MeasurableSpace Θ₂] [MeasurableSpace Ρ]
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (r : Ρ → Concept X Bool)
    (he₁ : Measurable (fun p : Θ₁ × X => e₁ p.1 p.2))
    (he₂ : Measurable (fun p : Θ₂ × X => e₂ p.1 p.2))
    (hr : Measurable (fun p : Ρ × X => r p.1 p.2)) :
    Measurable (fun p : (Θ₁ × Θ₂ × Ρ) × X => patchEval e₁ e₂ r p.1 p.2) := by sorry
