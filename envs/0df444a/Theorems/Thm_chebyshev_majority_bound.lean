-- Prove2me | Theorems.Thm_chebyshev_majority_bound
-- name    : chebyshev_majority_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:41:58.756787+00:00
-- url     : https://prove2.me/theorems/109f2ea5-6669-42d1-8410-41149c850d1f
-- title:
--   chebyshev majority bound: chebyshev majority bound
-- statement:
--   Chebyshev majority bound: if k ≥ 9/δ independent events each have probability ≥ 2 / 3,
--       then the probability that strictly more than k/2 of them hold is ≥ 1-δ.
--       Uses indicator random variables, Popoviciu's variance bound, independence for
--       variance of sums, and Chebyshev's inequality.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/Concentration.lean#L50-L157
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/Concentration.lean#L50-L157

module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_Concentration
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
attribute [local instance] Classical.propDecidable

theorem chebyshev_majority_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    {k : ℕ} {δ : ℝ} (h_delta_pos : 0 < δ)
    (hk : (9 : ℝ) / δ ≤ k)
    (events : Fin k → Set Ω)
    (hevents_meas : ∀ j, MeasurableSet (events j))
    (hindep : ProbabilityTheory.iIndepSet (fun j => events j) μ)
    (hprob : ∀ j, μ (events j) ≥ ENNReal.ofReal (2 / 3)) :
    μ {ω | k < 2 * (Finset.univ.filter (fun j => ω ∈ events j)).card} ≥
      ENNReal.ofReal (1 - δ) := by sorry
