-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.SparseEntropy.exp_binEntropy_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:56:10.686261+00:00
-- url     : https://prove2.me/submissions/7de301a3-6aa0-4e15-8a60-b4b20daf9a77

-- Sol generated from Probability/SparseEntropyLowerBound.lean
import Mathlib
import Definitions.Def_Probability_SparseEntropyLowerBound
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
theorem solution{N k : ℕ} (hk : 0 < k) (hkN : k < N) :
    Real.exp (N * Real.binEntropy ((k : ℝ) / N))
      = (((k : ℝ) / N) ^ k * (1 - (k : ℝ) / N) ^ (N - k))⁻¹ := by
  have hN : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set p : ℝ := (k : ℝ) / N with hpdef
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hp0 : 0 < p := div_pos hkR hNR
  have hp1 : p < 1 := by
    rw [hpdef, div_lt_one hNR]; exact_mod_cast hkN
  have hq0 : (0 : ℝ) < 1 - p := by linarith
  have hNk : ((N - k : ℕ) : ℝ) = (N : ℝ) - k := Nat.cast_sub hkN.le
  have hexp : (N : ℝ) * Real.binEntropy p
      = (k : ℝ) * Real.log p⁻¹ + ((N : ℝ) - k) * Real.log (1 - p)⁻¹ := by
    have h1 : (N : ℝ) * p = k := by rw [hpdef]; field_simp
    have h2 : (N : ℝ) * (1 - p) = (N : ℝ) - k := by rw [mul_sub, mul_one, h1]
    simp only [Real.binEntropy]
    rw [mul_add, ← mul_assoc, ← mul_assoc, h1, h2]
  rw [hexp, Real.exp_add, ← hNk]
  have e1 : Real.exp ((k : ℝ) * Real.log p⁻¹) = (p⁻¹) ^ k := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  have e2 : Real.exp (((N - k : ℕ) : ℝ) * Real.log (1 - p)⁻¹) = ((1 - p)⁻¹) ^ (N - k) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  rw [e1, e2, mul_inv, inv_pow, inv_pow]
