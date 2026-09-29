-- Prove2me | solution 1 for PriceOfUniversality.binw_mul_succ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:43:14.987149+00:00
-- url     : https://prove2.me/submissions/752330e4-c0a7-486d-bce8-a9fe55d7f2c3

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
theorem solution(m j : ℕ) (t : ℝ) :
    ((j : ℝ) + 1) * binw (m + 1) t (j + 1) = ((m : ℝ) + 1) * t * binw m t j := by
  have hc : (j + 1) * ((m + 1).choose (j + 1)) = (m + 1) * (m.choose j) := by
    rw [Nat.add_one_mul_choose_eq]
    ring
  have hcR : ((j : ℝ) + 1) * (((m + 1).choose (j + 1) : ℕ) : ℝ)
      = ((m : ℝ) + 1) * ((m.choose j : ℕ) : ℝ) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) hc
    push_cast at this
    linarith [this]
  unfold binw
  have hsub : (m + 1) - (j + 1) = m - j := by omega
  rw [hsub]
  calc ((j : ℝ) + 1) * ((((m + 1).choose (j + 1) : ℕ) : ℝ) * (t ^ (j + 1) * (1 - t) ^ (m - j)))
      = (((j : ℝ) + 1) * (((m + 1).choose (j + 1) : ℕ) : ℝ)) * (t ^ (j + 1) * (1 - t) ^ (m - j)) := by
        ring
    _ = (((m : ℝ) + 1) * ((m.choose j : ℕ) : ℝ)) * (t ^ (j + 1) * (1 - t) ^ (m - j)) := by
        rw [hcR]
    _ = ((m : ℝ) + 1) * t * (((m.choose j : ℕ) : ℝ) * (t ^ j * (1 - t) ^ (m - j))) := by
        ring
