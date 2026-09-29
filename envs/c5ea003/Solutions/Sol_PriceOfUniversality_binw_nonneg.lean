-- Prove2me | solution 1 for PriceOfUniversality.binw_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:43:15.594828+00:00
-- url     : https://prove2.me/submissions/5d8ae0c8-41f6-4707-8e46-3f6eaa97548f

-- Sol generated from Novelty/BinomialConcentration.lean
import Mathlib
import Definitions.Def_Novelty_BinomialConcentration
/-
# Binomial moments and Chebyshev concentration

Elementary, fully explicit development of the first two moments of the binomial
weights

  `binw n t k = C(n,k) * t ^ k * (1 - t) ^ (n - k)`

and of the resulting Chebyshev concentration inequality.  These are the
analytic ingredients used in `UniversalRedundancyBernoulli.lean` to prove a
Rissanen-style `(1/2) log₂ n` lower bound on the minimax redundancy of the class
of memoryless binary sources.

Main results:

* `binw_sum` — the weights sum to one (binomial theorem);
* `binw_mean` — `∑ k * binw n t k = n * t`;
* `binw_sq` — `∑ k ^ 2 * binw n t k = n * t * ((n - 1) * t + 1)`;
* `binw_variance` — `∑ (k - n t) ^ 2 * binw n t k = n * t * (1 - t)`;
* `binw_chebyshev` / `binw_concentration` — Chebyshev's inequality for the
  binomial law.
-/

open PriceOfUniversality

open Finset












open PriceOfUniversality in
theorem solution{t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n k : ℕ) : 0 ≤ binw n t k := by
  have h1 : 0 ≤ 1 - t := by linarith
  unfold binw
  positivity
