-- Prove2me | Theorems.Thm_syracuse_valuation_tail_almost_uniform
-- name    : syracuse_valuation_tail_almost_uniform
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-09T06:21:02.91136+00:00
-- url     : https://prove2.me/theorems/f7eef9b6-b2be-40c7-bda7-af2faab9160e
-- title:
--   Syracuse valuation tail for almost-uniform odd residue laws
-- statement:
--   For every positive gap c and nonnegative error constant K, there are positive constants A,d uniform over all probability spaces, measurable positive-odd random inputs N, thresholds q>0, and orbit lengths t. If q≥(2+c)t and the unhalved total-variation distance of N modulo 2^q from the uniform odd residue law is at most K/2^q, then the probability that the first t Syracuse valuation exponents have sum at least q is at most A exp(-dt). The finite L1 hypothesis is written explicitly on residue-cylinder probabilities. This is an explicit-constant form of the valuation-tail implication in Tao's Lemma 4.1, not Proposition 1.9's full joint-distribution approximation or the almost-boundedness theorem.

import Mathlib
import Definitions.Def_syracuseStep
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

theorem syracuse_valuation_tail_almost_uniform (c K : ℝ) (hc : 0 < c) (hK : 0 ≤ K) : ∃ A d : ℝ, 0 < A ∧ 0 < d ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (N : Ω → ℕ), Measurable N → (∀ᵐ ω ∂μ, 0 < N ω ∧ Odd (N ω)) → ∀ q t : ℕ, 0 < q → (2 + c) * (t : ℝ) ≤ (q : ℝ) → (∑ r : Fin (2 ^ q), |(μ {ω : Ω | N ω % 2 ^ q = r.val}).toReal - (if Odd r.val then 2 / (2 : ℝ) ^ q else 0)| ≤ K / (2 : ℝ) ^ q) → μ {ω : Ω | q ≤ ∑ i ∈ Finset.range t, (3 * (syracuseStep^[i]) (N ω) + 1).factorization 2} ≤ ENNReal.ofReal (A * Real.exp (-d * (t : ℝ))) := by sorry
