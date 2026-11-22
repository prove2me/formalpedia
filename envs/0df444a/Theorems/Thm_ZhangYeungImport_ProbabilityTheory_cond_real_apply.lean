-- Prove2me | Theorems.Thm_ZhangYeungImport_ProbabilityTheory_cond_real_apply
-- name    : ZhangYeungImport.ProbabilityTheory.cond_real_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:27:41.473801+00:00
-- url     : https://prove2.me/theorems/87485bd8-23b7-4c5e-8363-ce79378b499f
-- title:
--   Probability Theory: cond real apply
-- statement:
--   The axiomatic definition of conditional probability derived from a measure-theoretic
--   one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/ConditionalProbability.lean#L31-L33
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/ConditionalProbability.lean#L31-L33

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

theorem ZhangYeungImport.ProbabilityTheory.cond_real_apply (hms : MeasurableSet s) (μ : Measure Ω) (t : Set Ω) :
    μ[|s].real t = (μ.real s)⁻¹ * μ.real (s ∩ t) := by sorry

alias «ProbabilityTheory».«cond_real_apply» := ZhangYeungImport.ProbabilityTheory.cond_real_apply
