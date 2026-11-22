-- Prove2me | Theorems.Thm_paramWitnessSet_measurable
-- name    : paramWitnessSet_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:11.754234+00:00
-- url     : https://prove2.me/theorems/759b799c-a1bc-4392-be3c-9fcc5350fb94
-- title:
--   param Witness Set measurable: param Witness Set measurable
-- statement:
--   The witness set {(θ, p) | ghost-gap ≥ ε/2} is MeasurableSet
--       when the evaluation map e and target c are measurable.
--       This is the Borel half of the Borel-analytic bridge.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/BorelAnalyticBridge.lean#L117-L129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/BorelAnalyticBridge.lean#L117-L129

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_AnalyticMeasurability
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory

theorem paramWitnessSet_measurable
    {X : Type u} [MeasurableSpace X]
    {Θ : Type*} [MeasurableSpace Θ]
    (e : Θ → Concept X Bool)
    (he : Measurable (fun p : Θ × X => e p.1 p.2))
    (c : Concept X Bool) (hc : Measurable c)
    (m : ℕ) (ε : ℝ) :
    MeasurableSet (paramWitnessSet e c m ε) := by sorry
