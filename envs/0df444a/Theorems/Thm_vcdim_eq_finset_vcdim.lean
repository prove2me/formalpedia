-- Prove2me | Theorems.Thm_vcdim_eq_finset_vcdim
-- name    : vcdim_eq_finset_vcdim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:36:02.800663+00:00
-- url     : https://prove2.me/theorems/55d432c1-e4f0-46f6-bd13-da9ee537b5cd
-- title:
--   vcdim eq finset vcdim: vcdim eq finset vcdim
-- statement:
--   Our VCDim equals Mathlib's Finset.vcDim (cast to WithTop ℕ) for finite types.
--
--       This theorem connects our learning-theoretic VCDim (defined as a supremum
--       over shattered sets in WithTop ℕ) to Mathlib's combinatorial vcDim (defined
--       as shatterer.sup card in ℕ).
--
--       The proof requires shatters_iff_finset_shatters plus the equivalence between
--       iSup over Shatters-witnesses and Finset.sup over shatterer members.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Bridge.lean#L217-L247
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Bridge.lean#L217-L247

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Data
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Ordinal
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Bayesian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Bridge
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem vcdim_eq_finset_vcdim {X : Type u} [Fintype X] [DecidableEq X]
    (C : Finset (X → Bool)) :
    VCDim X (↑C : Set (X → Bool)) = ↑(Finset.vcDim (conceptClassToFinsetFamily C)) := by sorry
