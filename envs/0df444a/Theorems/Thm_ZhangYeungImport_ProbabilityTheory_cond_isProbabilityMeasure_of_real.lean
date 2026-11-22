-- Prove2me | Theorems.Thm_ZhangYeungImport_ProbabilityTheory_cond_isProbabilityMeasure_of_real
-- name    : ZhangYeungImport.ProbabilityTheory.cond_isProbabilityMeasure_of_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:43:21.386116+00:00
-- url     : https://prove2.me/theorems/4f41ad2d-51f4-4931-b64c-17190775e4cf
-- title:
--   Probability Theory: cond is Probability Measure of real
-- statement:
--   The conditional probability measure of any finite measure on any set of positive
--   measure
--   is a probability measure.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/ConditionalProbability.lean#L38-L45
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/ConditionalProbability.lean#L38-L45

module
public import Mathlib.Probability.ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
variable {Ω Ω' α : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'} {μ : Measure Ω}
  {s t : Set Ω}
open ProbabilityTheory

theorem ZhangYeungImport.ProbabilityTheory.cond_isProbabilityMeasure_of_real {α : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    {s : Set α} (hcs : μ.real s ≠ 0) :
    IsProbabilityMeasure μ[|s] := by sorry

alias «ProbabilityTheory».«cond_isProbabilityMeasure_of_real» := ZhangYeungImport.ProbabilityTheory.cond_isProbabilityMeasure_of_real
