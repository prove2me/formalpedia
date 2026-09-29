-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.SparseEntropy.binTerm_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:56:10.071423+00:00
-- url     : https://prove2.me/submissions/e9923089-5a88-48e6-b89d-d686a977f25f

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




/-- Cast form of the recurrence `C(N, j+1)·(j+1) = C(N, j)·(N - j)`. -/
theorem choose_succ_cast {N j : ℕ} (hj : j < N) :
    (N.choose (j + 1) : ℝ) * ((j : ℝ) + 1) = (N.choose j : ℝ) * ((N : ℝ) - j) := by
  have h : N.choose (j + 1) * (j + 1) = N.choose j * (N - j) := Nat.choose_succ_right_eq N j
  have hc : ((N.choose (j + 1) * (j + 1) : ℕ) : ℝ) = ((N.choose j * (N - j) : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) h
  push_cast [Nat.cast_sub hj.le] at hc
  linarith












open Catalog.Probability.NeuralCoding.SparseEntropy in
theorem solution{N k j : ℕ} (hkN : k ≤ N) (hkj : k ≤ j) (hjN : j < N) :
    binTerm ((k : ℝ) / N) N (j + 1) ≤ binTerm ((k : ℝ) / N) N j := by
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := lt_of_le_of_lt (Nat.zero_le j) hjN
    exact_mod_cast this
  set p : ℝ := (k : ℝ) / N with hp
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_le_one hNpos]; exact_mod_cast hkN
  have hq0 : (0 : ℝ) ≤ 1 - p := by linarith
  set m : ℕ := N - (j + 1) with hm
  have hsub : N - j = m + 1 := by omega
  have hineq : ((N : ℝ) - j) * p ≤ (1 - p) * ((j : ℝ) + 1) := by
    have hkj' : (k : ℝ) ≤ (j : ℝ) := by exact_mod_cast hkj
    have hjN' : ((j : ℝ) + 1) ≤ (N : ℝ) := by exact_mod_cast hjN
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [hp, ← sub_nonneg]
    have hrw : (1 - (k : ℝ) / N) * ((j : ℝ) + 1) - ((N : ℝ) - j) * ((k : ℝ) / N)
        = (((N : ℝ) - k) * ((j : ℝ) + 1) - ((N : ℝ) - j) * k) / N := by
      field_simp
    rw [hrw]
    refine div_nonneg ?_ hNpos.le
    nlinarith
  have hApos : (0 : ℝ) ≤ (N.choose j : ℝ) * (p ^ j * (1 - p) ^ m) := by positivity
  have hchoose := choose_succ_cast (N := N) (j := j) hjN
  have key : binTerm p N (j + 1) * ((j : ℝ) + 1) ≤ binTerm p N j * ((j : ℝ) + 1) := by
    unfold binTerm
    rw [hsub, show N - (j + 1) = m from hm.symm]
    have e1 : (N.choose j : ℝ) * (p ^ j * (1 - p) ^ (m + 1)) * ((j : ℝ) + 1)
        = ((N.choose j : ℝ) * (p ^ j * (1 - p) ^ m)) * ((1 - p) * ((j : ℝ) + 1)) := by ring
    have e2 : (N.choose (j + 1) : ℝ) * (p ^ (j + 1) * (1 - p) ^ m) * ((j : ℝ) + 1)
        = ((N.choose j : ℝ) * (p ^ j * (1 - p) ^ m)) * (((N : ℝ) - j) * p) := by
      have e : (N.choose (j + 1) : ℝ) * (p ^ (j + 1) * (1 - p) ^ m) * ((j : ℝ) + 1)
          = ((N.choose (j + 1) : ℝ) * ((j : ℝ) + 1)) * (p ^ (j + 1) * (1 - p) ^ m) := by ring
      rw [e, hchoose]; ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left hineq hApos
  have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  exact le_of_mul_le_mul_right key hjpos
