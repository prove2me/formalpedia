-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.SparseEntropy.sum_choose_ge_exp_binEntropy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:00:20.066166+00:00
-- url     : https://prove2.me/submissions/85cad1fa-145d-46e4-9305-0de9d18313cd

-- Sol generated from Probability/SparseEntropyLowerBound.lean
import Mathlib
import Definitions.Def_Probability_SparseEntropyLowerBound
import Theorems.Thm_Catalog_Probability_NeuralCoding_SparseEntropy_exp_binEntropy_le_choose
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The entropy estimate for sparse neural codes is exact up to `log (N + 1)`

`SparseEntropyBound.lean` proved the Chernoff-style *upper* bound

`∑_{j ≤ k} C(N, j) ≤ exp (N · binEntropy (k / N))`   (for `2k ≤ N`).

This file supplies the matching *lower* bound, so that the exponential rate of a
`k`-sparse neural population is pinned down exactly:

`exp (N · binEntropy (k / N)) / (N + 1) ≤ ∑_{j ≤ k} C(N, j)`.

The proof is the classical "method of types" argument.  Let `p = k / N` and
weight the patterns by the Bernoulli(`p`) product measure.  The weights
`T j = C(N, j) p^j (1-p)^{N-j}` sum to `1` over `0 ≤ j ≤ N` (binomial theorem),
and `T` is maximal at `j = k` precisely because `p = k / N`.  Hence
`1 ≤ (N + 1) T k`, and `T k = C(N,k) exp (-N binEntropy p)`.

## Main results

* `binTerm` — the Bernoulli weight `C(N,j) p^j (1-p)^{N-j}`;
* `binTerm_le_succ`, `binTerm_succ_le` — the weight increases up to `j = k` and
  decreases afterwards, when `p = k / N`;
* `binTerm_le_mode` — `k` is a mode of the binomial distribution `Bin(N, k/N)`;
* `sum_binTerm` — the weights sum to `1`;
* `exp_binEntropy_le_choose` — `exp (N · binEntropy (k/N)) ≤ (N + 1) · C(N,k)`;
* `sum_choose_ge_exp_binEntropy` — the lower bound for the sparse code size;
* `log_sum_choose_sub_entropy_abs_le` — combining with the upper bound of
  `SparseEntropyBound.lean`, `|log (∑_{j≤k} C(N,j)) - N·binEntropy(k/N)| ≤ log (N+1)`:
  the entropy estimate is exact to within an additive `log (N + 1)` nats, hence
  the *rate* `log (∑) / N` equals `binEntropy (k/N)` up to `O(log N / N)`.
-/

open Catalog.Probability.NeuralCoding.SparseEntropy

open Finset Real
















open Catalog.Probability.NeuralCoding.SparseEntropy in
theorem solution{N k : ℕ} (hk : 0 < k) (h2k : 2 * k ≤ N) :
    Real.exp ((N : ℝ) * Real.binEntropy ((k : ℝ) / N)) / ((N : ℝ) + 1)
      ≤ ∑ j ∈ range (k + 1), (N.choose j : ℝ) := by
  have hkN : k < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hmain := exp_binEntropy_le_choose hk hkN
  have hterm : (N.choose k : ℝ) ≤ ∑ j ∈ range (k + 1), (N.choose j : ℝ) := by
    refine Finset.single_le_sum (f := fun j => (N.choose j : ℝ)) (fun i _ => by positivity) ?_
    simp
  rw [div_le_iff₀ hNR]
  calc Real.exp ((N : ℝ) * Real.binEntropy ((k : ℝ) / N))
      ≤ ((N : ℝ) + 1) * (N.choose k : ℝ) := hmain
    _ ≤ (∑ j ∈ range (k + 1), (N.choose j : ℝ)) * ((N : ℝ) + 1) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right hterm hNR.le
