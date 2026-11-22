-- Prove2me | Theorems.Thm_amalgClass_wellBehaved
-- name    : amalgClass_wellBehaved
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:41:35.719801+00:00
-- url     : https://prove2.me/theorems/3511e8bf-b8cf-45cf-9989-d336c0c2da66
-- title:
--   amalg Class well Behaved: amalg Class well Behaved
-- statement:
--   The amalgamation class satisfies WellBehavedVCMeasTarget when all
--       parameter spaces are StandardBorelSpace and merge is jointly measurable.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Amalgamation.lean#L84-L109
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Amalgamation.lean#L84-L109

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Interpolation
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Amalgamation
set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory

theorem amalgClass_wellBehaved
    {X : Type u}
    [MeasurableSpace X] [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {Θ₁ Θ₂ S : Type*}
    [MeasurableSpace Θ₁] [StandardBorelSpace Θ₁]
    [MeasurableSpace Θ₂] [StandardBorelSpace Θ₂]
    [MeasurableSpace S] [StandardBorelSpace S]
    (π₁ : Θ₁ → S) (π₂ : Θ₂ → S)
    (hπ₁ : Measurable π₁) (hπ₂ : Measurable π₂)
    (merge : Θ₁ × Θ₂ → Concept X Bool)
    (hmerge : Measurable (fun p : (Θ₁ × Θ₂) × X => merge p.1 p.2)) :
    WellBehavedVCMeasTarget X (amalgClass π₁ π₂ merge) := by sorry
