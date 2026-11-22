-- Prove2me | Theorems.Thm_singleton_badEvent_eq_preimage_planar
-- name    : singleton_badEvent_eq_preimage_planar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:33.748612+00:00
-- url     : https://prove2.me/theorems/c78b409c-0a5c-4ebd-9653-8449ab4daf41
-- title:
--   singleton bad Event eq preimage planar: singleton bad Event eq preimage planar
-- statement:
--   The singleton bad event equals `samplePair1ToPlane ⁻¹' planarWitnessEvent`. The set
--   equality that transports both analyticity and non-Borelness from the planar witness to
--   the learning-theoretic bad event.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/BorelAnalyticSeparation.lean#L100-L151
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/BorelAnalyticSeparation.lean#L100-L151

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

theorem singleton_badEvent_eq_preimage_planar
    (A : Set ℝ) :
    singletonBadEvent A = samplePair1ToPlane ⁻¹' planarWitnessEvent A := by sorry
