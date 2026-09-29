-- Prove2me | solution 1 for PriceOfUniversality.binw_chebyshev
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:47:31.991133+00:00
-- url     : https://prove2.me/submissions/2a8b306c-a2e4-4f0c-8b6f-6bc9d08470fa

-- Sol generated from Novelty/BinomialConcentration.lean
import Mathlib
import Definitions.Def_Novelty_BinomialConcentration
import Theorems.Thm_PriceOfUniversality_binw_mul_succ
import Theorems.Thm_PriceOfUniversality_binw_nonneg
import Theorems.Thm_PriceOfUniversality_binw_sq
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


/-- The variance of the binomial law. -/
theorem binw_variance (n : ℕ) (t : ℝ) :
    ∑ k ∈ range (n + 1), ((k : ℝ) - (n : ℝ) * t) ^ 2 * binw n t k
      = (n : ℝ) * t * (1 - t) := by
  have hexpand : ∀ k ∈ range (n + 1),
      ((k : ℝ) - (n : ℝ) * t) ^ 2 * binw n t k
        = (k : ℝ) ^ 2 * binw n t k
          + (-(2 * (n : ℝ) * t)) * ((k : ℝ) * binw n t k)
          + ((n : ℝ) * t) ^ 2 * binw n t k := by
    intro k _; ring
  rw [Finset.sum_congr rfl hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    binw_sq n t, binw_mean n t, binw_sum n t]
  ring




open PriceOfUniversality in
theorem solution{n : ℕ} {t d : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hd : 0 < d)
    {K : Finset ℕ} (hK : K ⊆ range (n + 1))
    (hfar : ∀ k ∈ K, d ^ 2 ≤ ((k : ℝ) - (n : ℝ) * t) ^ 2) :
    ∑ k ∈ K, binw n t k ≤ (n : ℝ) * t * (1 - t) / d ^ 2 := by
  have hd2 : (0:ℝ) < d ^ 2 := by positivity
  have h1 : ∑ k ∈ K, d ^ 2 * binw n t k
      ≤ ∑ k ∈ K, ((k : ℝ) - (n : ℝ) * t) ^ 2 * binw n t k := by
    refine Finset.sum_le_sum fun k hk => ?_
    exact mul_le_mul_of_nonneg_right (hfar k hk) (binw_nonneg ht0 ht1 n k)
  have h2 : ∑ k ∈ K, ((k : ℝ) - (n : ℝ) * t) ^ 2 * binw n t k
      ≤ ∑ k ∈ range (n + 1), ((k : ℝ) - (n : ℝ) * t) ^ 2 * binw n t k := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hK fun k _ _ => ?_
    have := binw_nonneg ht0 ht1 n k
    positivity
  rw [binw_variance n t] at h2
  rw [← Finset.mul_sum] at h1
  rw [le_div_iff₀ hd2]
  calc (∑ k ∈ K, binw n t k) * d ^ 2 = d ^ 2 * ∑ k ∈ K, binw n t k := by ring
    _ ≤ (n : ℝ) * t * (1 - t) := le_trans h1 h2
