-- Prove2me | Theorems.Thm_singleton_badEvent_not_measurable
-- name    : singleton_badEvent_not_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:26.632807+00:00
-- url     : https://prove2.me/theorems/073f01fd-1faa-46cb-903e-667822c0e6cf
-- title:
--   singleton bad Event not measurable: singleton bad Event not measurable
-- statement:
--   For `A` non-Borel, the singleton bad event is non-Borel. Combine
--   `singleton_badEvent_eq_preimage_planar` with `planarWitnessEvent_not_measurable`: the
--   preimage of a non-Borel set under a measurable *surjection* cannot itself be Borel.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/BorelAnalyticSeparation.lean#L202-L214
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/BorelAnalyticSeparation.lean#L202-L214

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_BorelAnalyticSeparation
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory

theorem singleton_badEvent_not_measurable
    (A : Set ℝ) (hA_non : ¬ MeasurableSet A) :
    ¬ MeasurableSet (singletonBadEvent A) := by sorry
