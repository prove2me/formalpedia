-- Prove2me | Theorems.Thm_supportError_le_one
-- name    : supportError_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:38:49.387528+00:00
-- url     : https://prove2.me/theorems/38501094-b9f7-43b2-8c0e-b462e7adaf3f
-- title:
--   support Error le one: support Error le one
-- statement:
--   supportError is at most 1.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Compression.lean#L88-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Compression.lean#L88-L93

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

theorem supportError_le_one {X : Type u} (Y : Finset X) (q : FinitePMF ↥Y)
    (h c : X → Bool) : supportError Y q h c ≤ 1 := by sorry
