-- Prove2me | Theorems.Thm_supportAgreement_eq_one_sub_supportError
-- name    : supportAgreement_eq_one_sub_supportError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:35:59.566074+00:00
-- url     : https://prove2.me/theorems/8298db12-52f3-4775-8c19-23613986e766
-- title:
--   support Agreement eq one sub support Error: support Agreement eq one sub support Error
-- statement:
--   Weighted agreement = 1 - supportError.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Compression.lean#L66-L79
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Compression.lean#L66-L79

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

theorem supportAgreement_eq_one_sub_supportError {X : Type u} (Y : Finset X)
    (q : FinitePMF ↥Y) (h c : X → Bool) :
    (∑ y : ↥Y, q.prob y * (if h (y : X) = c (y : X) then (1 : ℝ) else 0)) =
    1 - supportError Y q h c := by sorry
