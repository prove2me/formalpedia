-- Prove2me | Theorems.Thm_measurableSet_agreementRel
-- name    : measurableSet_agreementRel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:24.546271+00:00
-- url     : https://prove2.me/theorems/906f0b0f-6a05-4949-a5e8-b8b8195c825d
-- title:
--   measurable Set agreement Rel: measurable Set agreement Rel
-- statement:
--   The agreement relation is MeasurableSet when projections are measurable
--       and the codomain is StandardBorelSpace.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Amalgamation.lean#L69-L78
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Amalgamation.lean#L69-L78

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

theorem measurableSet_agreementRel
    {Θ₁ Θ₂ S : Type*}
    [MeasurableSpace Θ₁] [MeasurableSpace Θ₂]
    [MeasurableSpace S] [StandardBorelSpace S]
    (π₁ : Θ₁ → S) (π₂ : Θ₂ → S)
    (hπ₁ : Measurable π₁) (hπ₂ : Measurable π₂) :
    MeasurableSet (agreementRel π₁ π₂) := by sorry
