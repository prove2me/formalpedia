-- Prove2me | Definitions.Def_MachineLearning_BenfordDynamics_BenfordCriterion
-- name    : MachineLearning_BenfordDynamics_BenfordCriterion
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:36:54.964727+00:00
-- url     : https://prove2.me/theorems/4ad76105-7cb4-4b97-9942-f79976d1ce71
-- title:
--   Aether Catalog definitions — MachineLearning_BenfordDynamics_BenfordCriterion
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.BenfordDynamics.BenfordCriterion`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/BenfordDynamics/BenfordCriterion.lean by skeleton subtraction
import Mathlib

/-!
# Benford Criterion from Equidistribution

This file proves foundational results connecting Benford's law to
equidistribution of logarithmic mantissae modulo 1.

## Main Results

- `leadDigitBase_eq_iff_fract`: The leading digit of `n` in base `b` equals `m`
  iff `fract(log_b n)` lies in `[log_b m, log_b(m+1))`.
- `benford_target_sum_one`: The Benford probabilities sum to 1.
- `benford_target_pos`: Each Benford probability is positive.
- `benfordCriterion`: If a sequence has equidistributed log mantissae,
  leading digits follow Benford's law.
-/

open Real Nat Finset Filter

noncomputable section

/-- The Benford target probability: `log_b(1 + 1/m)` for digit `m` in base `b`. -/
def benfordProb (b m : ℕ) : ℝ :=
  Real.log (1 + 1 / (m : ℝ)) / Real.log (b : ℝ)

/-
Benford probabilities are positive for valid digits.
-/

/-
The Benford probabilities for digits 1 through b-1 sum to 1.
    This is a telescoping product: `∑_{m=1}^{b-1} log_b(1+1/m) = log_b(b) = 1`.
-/

/-
**Leading digit characterization via logarithmic mantissa.**

    For `n ≥ 1` and `b ≥ 2`, the leading digit of `n` in base `b`
    equals `m` (where `1 ≤ m < b`) if and only if
    `fract(log_b n) ∈ [log_b m, log_b(m+1))`.

    This is the fundamental bridge between digit statistics and
    equidistribution theory.
-/

end


