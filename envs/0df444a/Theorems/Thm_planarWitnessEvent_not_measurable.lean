-- Prove2me | Theorems.Thm_planarWitnessEvent_not_measurable
-- name    : planarWitnessEvent_not_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:29.212837+00:00
-- url     : https://prove2.me/theorems/b183bdea-fef0-446e-af2c-dcbc5397db15
-- title:
--   planar Witness Event not measurable: planar Witness Event not measurable
-- statement:
--   For `A` non-Borel, `planarWitnessEvent A` is non-Borel. The proof picks some
--   `a ∉ A` and shows the vertical section `y ↦ (a, y)` pulls the planar event back to `A`
--   itself: if the planar event were Borel, its preimage under this measurable map would be
--   Borel too, contradicting the hypothesis on `A`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/BorelAnalyticSeparation.lean#L180-L195
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/BorelAnalyticSeparation.lean#L180-L195

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

theorem planarWitnessEvent_not_measurable
    (A : Set ℝ) (hA_non : ¬ MeasurableSet A) :
    ¬ MeasurableSet (planarWitnessEvent A) := by sorry
