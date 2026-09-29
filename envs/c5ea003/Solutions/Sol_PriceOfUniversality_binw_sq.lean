-- Prove2me | solution 1 for PriceOfUniversality.binw_sq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:45:29.59059+00:00
-- url     : https://prove2.me/submissions/fdf635cf-860d-4e18-8ac9-a093d6ad84ba

-- Sol generated from Novelty/BinomialConcentration.lean
import Mathlib
import Definitions.Def_Novelty_BinomialConcentration
import Theorems.Thm_PriceOfUniversality_binw_mul_succ
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





/-- Weighted reindexing: a sum of `k * g k * binw (m+1) t k` reduces to a sum against
`binw m t`. -/
lemma binw_weighted (m : ℕ) (t : ℝ) (g : ℕ → ℝ) :
    ∑ k ∈ range (m + 2), (k : ℝ) * g k * binw (m + 1) t k
      = ((m : ℝ) + 1) * t * ∑ j ∈ range (m + 1), g (j + 1) * binw m t j := by
  rw [Finset.sum_range_succ' (fun k => (k : ℝ) * g k * binw (m + 1) t k) (m + 1)]
  simp only [Nat.cast_zero, zero_mul, add_zero]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := binw_mul_succ m j t
  push_cast
  calc ((j : ℝ) + 1) * g (j + 1) * binw (m + 1) t (j + 1)
      = g (j + 1) * (((j : ℝ) + 1) * binw (m + 1) t (j + 1)) := by ring
    _ = g (j + 1) * (((m : ℝ) + 1) * t * binw m t j) := by rw [this]
    _ = ((m : ℝ) + 1) * t * (g (j + 1) * binw m t j) := by ring

/-- The mean of the binomial law. -/
theorem binw_mean (n : ℕ) (t : ℝ) :
    ∑ k ∈ range (n + 1), (k : ℝ) * binw n t k = (n : ℝ) * t := by
  cases n with
  | zero => simp [binw]
  | succ m =>
      have h := binw_weighted m t (fun _ => 1)
      simp only [mul_one, one_mul] at h
      rw [show m + 1 + 1 = m + 2 from rfl, h, binw_sum m t, mul_one]
      push_cast
      ring






open PriceOfUniversality in
theorem solution(n : ℕ) (t : ℝ) :
    ∑ k ∈ range (n + 1), (k : ℝ) ^ 2 * binw n t k = (n : ℝ) * t * (((n : ℝ) - 1) * t + 1) := by
  cases n with
  | zero => simp [binw]
  | succ m =>
      have h := binw_weighted m t (fun k => (k : ℝ))
      have hleft : ∑ k ∈ range (m + 2), (k : ℝ) * (k : ℝ) * binw (m + 1) t k
          = ∑ k ∈ range (m + 2), (k : ℝ) ^ 2 * binw (m + 1) t k :=
        Finset.sum_congr rfl fun k _ => by ring
      rw [hleft] at h
      have hright : ∑ j ∈ range (m + 1), ((j : ℝ) + 1) * binw m t j
          = (m : ℝ) * t + 1 := by
        have : ∑ j ∈ range (m + 1), ((j : ℝ) + 1) * binw m t j
            = (∑ j ∈ range (m + 1), (j : ℝ) * binw m t j)
              + ∑ j ∈ range (m + 1), binw m t j := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [this, binw_mean m t, binw_sum m t]
      have hcast : ∑ j ∈ range (m + 1), ((j + 1 : ℕ) : ℝ) * binw m t j
          = ∑ j ∈ range (m + 1), ((j : ℝ) + 1) * binw m t j :=
        Finset.sum_congr rfl fun j _ => by push_cast; ring
      rw [show m + 1 + 1 = m + 2 from rfl, h, hcast, hright]
      push_cast
      ring
