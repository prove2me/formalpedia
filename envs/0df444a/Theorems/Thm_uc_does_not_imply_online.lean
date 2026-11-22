-- Prove2me | Theorems.Thm_uc_does_not_imply_online
-- name    : uc_does_not_imply_online
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:36:22.9811+00:00
-- url     : https://prove2.me/theorems/c2dc69a4-2b21-484c-b517-4c2318c6e5c7
-- title:
--   uc does not imply online: uc does not imply online
-- statement:
--   PAC uniform convergence does NOT imply online learnability.
--       There exist concept classes with finite VCDim (hence PAC learnable)
--       but infinite Littlestone dimension (hence not online learnable with
--       finite mistake bound).
--       Witness: threshold class C_φ on X via embedding φ : ℕ ↪ X.
--       VCDim(C_φ) ≤ 1 (monotonicity prevents 2-shattering).
--       LittlestoneDim(C_φ) = ∞ (adversary binary search forces d mistakes for any d).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GeneralizationResults.lean#L147-L164
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GeneralizationResults.lean#L147-L164

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GeneralizationResults
set_option autoImplicit true
@[expose] public section
public section
universe u
attribute [local instance] Classical.propDecidable

theorem uc_does_not_imply_online (X : Type u) [MeasurableSpace X] [Infinite X]
    (hmeas_C_all : ∀ (C : ConceptClass X Bool), ∀ h ∈ C, Measurable h)
    (hc_meas_all : ∀ c : Concept X Bool, Measurable c)
    (hWB_all : ∀ (C : ConceptClass X Bool), WellBehavedVC X C) :
    ¬ (∀ (C : ConceptClass X Bool),
      HasUniformConvergence X C →
        ∃ (M : ℕ), MistakeBounded X Bool C M) := by sorry
