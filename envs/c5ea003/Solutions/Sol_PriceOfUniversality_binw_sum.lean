-- Prove2me | solution 1 for PriceOfUniversality.binw_sum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:40:17.265683+00:00
-- url     : https://prove2.me/submissions/70268221-23b4-4a7d-888b-0456741d2c25

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
theorem solution(n : ℕ) (t : ℝ) : ∑ k ∈ range (n + 1), binw n t k = 1 := by
  have h := add_pow t (1 - t) n
  have ht : t + (1 - t) = 1 := by ring
  rw [ht, one_pow] at h
  calc ∑ k ∈ range (n + 1), binw n t k
      = ∑ k ∈ range (n + 1), t ^ k * (1 - t) ^ (n - k) * (n.choose k : ℝ) :=
        Finset.sum_congr rfl fun k _ => by unfold binw; ring
    _ = 1 := h.symm
