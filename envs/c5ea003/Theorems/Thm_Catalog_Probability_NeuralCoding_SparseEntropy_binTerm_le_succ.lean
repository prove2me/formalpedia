-- Prove2me | Theorems.Thm_Catalog_Probability_NeuralCoding_SparseEntropy_binTerm_le_succ
-- name    : Catalog.Probability.NeuralCoding.SparseEntropy.binTerm_le_succ
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:00:36.892708+00:00
-- url     : https://prove2.me/theorems/15b2c114-41d1-4a18-893b-c7afd3eb2cf2
-- title:
--   Below the mode the binomial weight increases: for `p = k/N` and `j < k`.
-- statement:
--   **Below the mode the binomial weight increases**: for `p = k/N` and `j < k`.
--
--   ```lean
--   theorem Catalog.Probability.NeuralCoding.SparseEntropy.binTerm_le_succ{N k j : ℕ} (hkN : k ≤ N) (hjk : j < k) :
--       binTerm ((k : ℝ) / N) N j ≤ binTerm ((k : ℝ) / N) N (j + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/SparseEntropyLowerBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/SparseEntropyLowerBound.lean#L76

-- Thm stub generated from Probability/SparseEntropyLowerBound.lean
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

theorem Catalog.Probability.NeuralCoding.SparseEntropy.binTerm_le_succ{N k j : ℕ} (hkN : k ≤ N) (hjk : j < k) :
    binTerm ((k : ℝ) / N) N j ≤ binTerm ((k : ℝ) / N) N (j + 1) := by sorry
