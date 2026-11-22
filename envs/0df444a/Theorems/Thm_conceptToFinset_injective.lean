-- Prove2me | Theorems.Thm_conceptToFinset_injective
-- name    : conceptToFinset_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:39:25.282405+00:00
-- url     : https://prove2.me/theorems/f59d48a8-0083-4256-b499-12370b0cf1d3
-- title:
--   concept To Finset injective: concept To Finset injective
-- statement:
--   The concept-to-finset map is injective: distinct Bool-valued functions
--       produce distinct level sets. This ensures conceptClassToFinsetFamily
--       preserves the cardinality of C.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Bridge.lean#L103-L109
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Bridge.lean#L103-L109

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

theorem conceptToFinset_injective {X : Type u} [Fintype X] :
    Function.Injective (conceptToFinset (X := X)) := by sorry
