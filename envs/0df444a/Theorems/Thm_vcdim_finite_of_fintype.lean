-- Prove2me | Theorems.Thm_vcdim_finite_of_fintype
-- name    : vcdim_finite_of_fintype
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:39:12.865017+00:00
-- url     : https://prove2.me/theorems/c30cc015-37b9-466e-8aba-e25a7db647ba
-- title:
--   vcdim finite of fintype: vcdim finite of fintype
-- statement:
--   VCDim is finite for finite concept classes over finite domains.
--       This is a consequence of the bridge: Finset.vcDim is always finite (it's ℕ).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Bridge.lean#L251-L257
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Bridge.lean#L251-L257

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

theorem vcdim_finite_of_fintype {X : Type u}
    (hX : Fintype X) (hdec : DecidableEq X) (C : Finset (X → Bool)) :
    VCDim X (↑C : Set (X → Bool)) < ⊤ := by sorry
