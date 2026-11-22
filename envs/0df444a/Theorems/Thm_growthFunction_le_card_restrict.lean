-- Prove2me | Theorems.Thm_growthFunction_le_card_restrict
-- name    : growthFunction_le_card_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:39:16.448004+00:00
-- url     : https://prove2.me/theorems/ab6dd4fa-5784-43cd-aa0e-f44b9dc63ecd
-- title:
--   growth Function le card restrict: growth Function le card restrict
-- statement:
--   The number of distinct restrictions is our GrowthFunction.
--       GrowthFunction X C m = max over m-element S of |C|_S|.
--       This lemma connects GrowthFunction to the restriction operation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Bridge.lean#L286-L289
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Bridge.lean#L286-L289

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

theorem growthFunction_le_card_restrict {X : Type u}
    (C : Finset (X → Bool)) (S : Finset X) :
    (restrictConceptClass C S).card ≤ C.card := by sorry
