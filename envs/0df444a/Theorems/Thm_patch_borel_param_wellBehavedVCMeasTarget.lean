-- Prove2me | Theorems.Thm_patch_borel_param_wellBehavedVCMeasTarget
-- name    : patch_borel_param_wellBehavedVCMeasTarget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:35:49.443989+00:00
-- url     : https://prove2.me/theorems/38dd4cfa-f95d-45b2-9a9d-9c1273a29beb
-- title:
--   patch borel param well Behaved VCMeas Target: patch borel param well Behaved VCMeas Target
-- statement:
--   The patched union of two Borel-parameterized classes (with a measurable region
--   selector) is itself Borel-parameterized over `Θ₁ × Θ₂ × Ρ`, and therefore satisfies
--   `WellBehavedVCMeasTarget`. Immediate from `patchEval_measurable` and
--   `borel_param_wellBehavedVCMeasTarget`. Surfacing this corollary at the class level makes
--   the closure of the measurable-target hypothesis under amalgamation explicit.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/BorelAnalyticBridge.lean#L268-L281
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/BorelAnalyticBridge.lean#L268-L281

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

theorem patch_borel_param_wellBehavedVCMeasTarget
    {X : Type u} [MeasurableSpace X] [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {Θ₁ Θ₂ Ρ : Type*}
    [MeasurableSpace Θ₁] [StandardBorelSpace Θ₁]
    [MeasurableSpace Θ₂] [StandardBorelSpace Θ₂]
    [MeasurableSpace Ρ] [StandardBorelSpace Ρ]
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (r : Ρ → Concept X Bool)
    (he₁ : Measurable (fun p : Θ₁ × X => e₁ p.1 p.2))
    (he₂ : Measurable (fun p : Θ₂ × X => e₂ p.1 p.2))
    (hr : Measurable (fun p : Ρ × X => r p.1 p.2)) :
    WellBehavedVCMeasTarget X (Set.range (patchEval e₁ e₂ r)) := by sorry
