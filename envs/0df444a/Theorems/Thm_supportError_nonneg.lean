-- Prove2me | Theorems.Thm_supportError_nonneg
-- name    : supportError_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:38:34.767545+00:00
-- url     : https://prove2.me/theorems/b458b4e8-61c6-499c-b782-a666b61f13d7
-- title:
--   support Error nonneg: support Error nonneg
-- statement:
--   supportError is nonneg.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Compression.lean#L82-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Compression.lean#L82-L85

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

theorem supportError_nonneg {X : Type u} (Y : Finset X) (q : FinitePMF ↥Y)
    (h c : X → Bool) : 0 ≤ supportError Y q h c := by sorry
