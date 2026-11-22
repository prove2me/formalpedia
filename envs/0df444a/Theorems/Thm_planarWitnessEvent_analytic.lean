-- Prove2me | Theorems.Thm_planarWitnessEvent_analytic
-- name    : planarWitnessEvent_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:42:07.981788+00:00
-- url     : https://prove2.me/theorems/30771861-d05f-4490-8cd9-b89efbb3da02
-- title:
--   planar Witness Event analytic: planar Witness Event analytic
-- statement:
--   For `A` analytic, `planarWitnessEvent A` is analytic. The proof presents it as the
--   intersection of `Prod.snd ⁻¹' A` (analytic, by preimage of analytic under a continuous
--   map) with the Borel set `{(x, y) | x ≠ y}` (the complement of the diagonal). Analytic
--   sets are closed under intersection with Borel sets.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/BorelAnalyticSeparation.lean#L159-L172
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/BorelAnalyticSeparation.lean#L159-L172

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

theorem planarWitnessEvent_analytic
    (A : Set ℝ) (hA : AnalyticSet A) :
    AnalyticSet (planarWitnessEvent A) := by sorry
