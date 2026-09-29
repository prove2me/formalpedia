-- Prove2me | Theorems.Thm_leadDigitBase_eq_iff_fract_log
-- name    : leadDigitBase_eq_iff_fract_log
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T20:02:09.139911+00:00
-- url     : https://prove2.me/theorems/10c621b9-0f27-4352-a07d-8789af10529f
-- title:
--   LeadDigitBase eq iff fract log
-- statement:
--   Formal statement of `leadDigitBase_eq_iff_fract_log` from the Aether Catalog (MachineLearning). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem leadDigitBase_eq_iff_fract_log(b n m : ℕ) (hb : 2 ≤ b) (hn : 1 ≤ n)
--       (hm : 1 ≤ m) (hm' : m < b) :
--       n / b ^ (Nat.log b n) = m ↔
--         Real.log (m : ℝ) / Real.log (b : ℝ) ≤
--           Int.fract (Real.log (n : ℝ) / Real.log (b : ℝ)) ∧
--         Int.fract (Real.log (n : ℝ) / Real.log (b : ℝ)) <
--           Real.log ((m : ℝ) + 1) / Real.log (b : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/BenfordDynamics/BenfordCriterion.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/BenfordDynamics/BenfordCriterion.lean#L59

-- Thm stub generated from MachineLearning/BenfordDynamics/BenfordCriterion.lean
import Mathlib
import Definitions.Def_MachineLearning_BenfordDynamics_BenfordCriterion

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

theorem leadDigitBase_eq_iff_fract_log(b n m : ℕ) (hb : 2 ≤ b) (hn : 1 ≤ n)
    (hm : 1 ≤ m) (hm' : m < b) :
    n / b ^ (Nat.log b n) = m ↔
      Real.log (m : ℝ) / Real.log (b : ℝ) ≤
        Int.fract (Real.log (n : ℝ) / Real.log (b : ℝ)) ∧
      Int.fract (Real.log (n : ℝ) / Real.log (b : ℝ)) <
        Real.log ((m : ℝ) + 1) / Real.log (b : ℝ) := by sorry
