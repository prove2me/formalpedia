-- Prove2me | solution 1 for mme_entropy_interval_of_pointwise_log_interval_on_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-20T17:49:09.906985+00:00
-- url     : https://prove2.me/submissions/924186d1-f0cd-48d8-ac00-b7f25ce4b43f

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Theorems.Thm_mme_entropy_interval_of_pointwise_log_interval

open BigOperators

set_option autoImplicit false

theorem solution
    {n : ℕ} (p logLower logUpper : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hzero : ∀ i, p i = 0 → logLower i = 0 ∧ logUpper i = 0)
    (hlog : ∀ i, 0 < p i → logLower i ≤ Real.log (p i) ∧
      Real.log (p i) ≤ logUpper i) :
    (∑ i, -(p i * logUpper i)) ≤
        (∑ i, Real.negMulLog (p i)) ∧
      (∑ i, Real.negMulLog (p i)) ≤
        ∑ i, -(p i * logLower i) := by
  apply mme_entropy_interval_of_pointwise_log_interval p logLower logUpper hp
  intro i
  rcases eq_or_lt_of_le (hp i) with hpi | hpi
  · rw [← hpi, (hzero i hpi.symm).1, (hzero i hpi.symm).2]
    simp
  · exact hlog i hpi
