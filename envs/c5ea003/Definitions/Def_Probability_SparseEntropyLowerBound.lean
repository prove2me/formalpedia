-- Prove2me | Definitions.Def_Probability_SparseEntropyLowerBound
-- name    : Probability_SparseEntropyLowerBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:36:13.211972+00:00
-- url     : https://prove2.me/theorems/3777e249-b04b-4076-993f-477961f59ac0
-- title:
--   Aether Catalog definitions — Probability_SparseEntropyLowerBound
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.SparseEntropyLowerBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/SparseEntropyLowerBound.lean by skeleton subtraction
import Mathlib
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

namespace Catalog.Probability.NeuralCoding.SparseEntropy

open Finset Real

/-- The Bernoulli(`p`) weight of the set of patterns of weight `j` on `N` neurons. -/
noncomputable def binTerm (p : ℝ) (N j : ℕ) : ℝ :=
  (N.choose j : ℝ) * (p ^ j * (1 - p) ^ (N - j))














end Catalog.Probability.NeuralCoding.SparseEntropy


