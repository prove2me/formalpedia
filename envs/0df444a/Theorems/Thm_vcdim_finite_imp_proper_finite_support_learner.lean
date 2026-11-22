-- Prove2me | Theorems.Thm_vcdim_finite_imp_proper_finite_support_learner
-- name    : vcdim_finite_imp_proper_finite_support_learner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:36:03.326096+00:00
-- url     : https://prove2.me/theorems/2e9a15cd-1c12-45ad-b5ff-2f092c1f1190
-- title:
--   vcdim finite imp proper finite support learner: vcdim finite imp proper finite support learner
-- statement:
--   Finite VC dimension implies existence of a proper finite-support learner.
--       The construction uses ERM + finite_support_vc_approx on the disagreement family.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Compression.lean#L194-L304
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Compression.lean#L194-L304

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

theorem vcdim_finite_imp_proper_finite_support_learner
    (X : Type u) (C : ConceptClass X Bool)
    (hCne : C.Nonempty) (hC : VCDim X C < ⊤) :
    ∃ _L : ProperFiniteSupportLearner X C, True := by sorry
