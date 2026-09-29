-- Prove2me | solution 1 for mme_entropy_interval_of_pointwise_log_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-20T17:46:34.592378+00:00
-- url     : https://prove2.me/submissions/17734cf2-45f9-4ba6-90c9-70333da5c373

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open BigOperators

set_option autoImplicit false

theorem solution
    {n : ℕ} (p logLower logUpper : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hlog : ∀ i, logLower i ≤ Real.log (p i) ∧
      Real.log (p i) ≤ logUpper i) :
    (∑ i, -(p i * logUpper i)) ≤
        (∑ i, Real.negMulLog (p i)) ∧
      (∑ i, Real.negMulLog (p i)) ≤
        ∑ i, -(p i * logLower i) := by
  constructor
  · apply Finset.sum_le_sum
    intro i _
    rw [Real.negMulLog_eq_neg]
    exact neg_le_neg (mul_le_mul_of_nonneg_left (hlog i).2 (hp i))
  · apply Finset.sum_le_sum
    intro i _
    rw [Real.negMulLog_eq_neg]
    exact neg_le_neg (mul_le_mul_of_nonneg_left (hlog i).1 (hp i))

/- Zero cells may be omitted from a numerical log certificate.  This is the
   form used by sparse beta/quarter/gamma distributions in the DWZ witness. -/
