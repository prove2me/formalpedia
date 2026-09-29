-- Prove2me | solution 1 for PriceOfUniversality.binw_concentration
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:50:24.30829+00:00
-- url     : https://prove2.me/submissions/3526d193-969a-4eb3-b51e-191a2a96e178

-- Sol generated from Novelty/BinomialConcentration.lean
import Mathlib
import Definitions.Def_Novelty_BinomialConcentration
import Theorems.Thm_PriceOfUniversality_binw_chebyshev
import Theorems.Thm_PriceOfUniversality_binw_sum
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
theorem solution{n : ℕ} {t d : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hd : 0 < d)
    {K : Finset ℕ} (hK : K ⊆ range (n + 1))
    (hnear : ∀ k ∈ range (n + 1), k ∉ K → d ^ 2 ≤ ((k : ℝ) - (n : ℝ) * t) ^ 2) :
    1 - (n : ℝ) * t * (1 - t) / d ^ 2 ≤ ∑ k ∈ K, binw n t k := by
  have hsplit : ∑ k ∈ (range (n + 1)) \ K, binw n t k + ∑ k ∈ K, binw n t k = 1 := by
    rw [Finset.sum_sdiff hK]
    exact binw_sum n t
  have hcomp : ∑ k ∈ (range (n + 1)) \ K, binw n t k ≤ (n : ℝ) * t * (1 - t) / d ^ 2 := by
    refine binw_chebyshev ht0 ht1 hd (Finset.sdiff_subset) ?_
    intro k hk
    rw [Finset.mem_sdiff] at hk
    exact hnear k hk.1 hk.2
  linarith
