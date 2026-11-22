-- Prove2me | Theorems.Thm_labeledSampleOfFinset_eq_of_eq_on_support
-- name    : labeledSampleOfFinset_eq_of_eq_on_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:36:02.617198+00:00
-- url     : https://prove2.me/theorems/27a8e1fd-9133-47c4-bb45-ed43ecda29ad
-- title:
--   labeled Sample Of Finset eq of eq on support: labeled Sample Of Finset eq of eq on support
-- statement:
--   If two label functions agree on all points of `Z`, then the labeled samples they
--   induce on `Z.equivFin` are equal.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Compression.lean#L441-L448
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Compression.lean#L441-L448

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_FiniteVCApprox
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_FiniteSupportUC
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Compression
set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
universe u
attribute [local instance] Classical.propDecidable

theorem labeledSampleOfFinset_eq_of_eq_on_support
    {X : Type u}
    {ℓ₁ ℓ₂ : X → Bool} {Z : Finset X}
    (hℓ : ∀ x ∈ Z, ℓ₁ x = ℓ₂ x) :
    labeledSampleOfFinset ℓ₁ Z = labeledSampleOfFinset ℓ₂ Z := by sorry
