-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.SparseEntropy.exp_binEntropy_le_choose
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:58:54.52535+00:00
-- url     : https://prove2.me/submissions/eab4aa48-afa2-4897-8bcc-40d70b307fa9

-- Sol generated from Probability/SparseEntropyLowerBound.lean
import Mathlib
import Definitions.Def_Probability_SparseEntropyLowerBound
import Theorems.Thm_Catalog_Probability_NeuralCoding_SparseEntropy_binTerm_le_succ
import Theorems.Thm_Catalog_Probability_NeuralCoding_SparseEntropy_binTerm_succ_le
import Theorems.Thm_Catalog_Probability_NeuralCoding_SparseEntropy_exp_binEntropy_eq
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



/-- The Bernoulli weights sum to `1` (binomial theorem). -/
theorem sum_binTerm (p : ℝ) (N : ℕ) :
    ∑ j ∈ range (N + 1), binTerm p N j = 1 := by
  have hbin : (p + (1 - p)) ^ N =
      ∑ j ∈ range (N + 1), p ^ j * (1 - p) ^ (N - j) * (N.choose j : ℝ) :=
    add_pow p (1 - p) N
  simp only [add_sub_cancel, one_pow] at hbin
  unfold binTerm
  calc ∑ j ∈ range (N + 1), (N.choose j : ℝ) * (p ^ j * (1 - p) ^ (N - j))
      = ∑ j ∈ range (N + 1), p ^ j * (1 - p) ^ (N - j) * (N.choose j : ℝ) :=
        Finset.sum_congr rfl (fun j _ => by ring)
    _ = 1 := hbin.symm




/-- Weights below the mode. -/
theorem binTerm_le_mode_of_le {N k : ℕ} (hkN : k ≤ N) :
    ∀ d j : ℕ, k - j = d → j ≤ k →
      binTerm ((k : ℝ) / N) N j ≤ binTerm ((k : ℝ) / N) N k := by
  intro d
  induction d with
  | zero =>
      intro j hd _
      have hjk : j = k := by omega
      rw [hjk]
  | succ d ih =>
      intro j hd hjk
      have hlt : j < k := by omega
      exact le_trans (binTerm_le_succ hkN hlt) (ih (j + 1) (by omega) (by omega))

/-- Weights above the mode. -/
theorem binTerm_le_mode_of_ge {N k : ℕ} (hkN : k ≤ N) :
    ∀ j : ℕ, k ≤ j → j ≤ N → binTerm ((k : ℝ) / N) N j ≤ binTerm ((k : ℝ) / N) N k := by
  intro j hkj
  induction j, hkj using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ j hkj ih =>
      intro hjN
      have hj : j < N := by omega
      exact le_trans (binTerm_succ_le hkN hkj hj) (ih (by omega))

/-- **`k` is a mode of `Bin(N, k/N)`.** -/
theorem binTerm_le_mode {N k : ℕ} (hkN : k ≤ N) {j : ℕ} (hj : j ≤ N) :
    binTerm ((k : ℝ) / N) N j ≤ binTerm ((k : ℝ) / N) N k := by
  by_cases h : j ≤ k
  · exact binTerm_le_mode_of_le hkN (k - j) j rfl h
  · exact binTerm_le_mode_of_ge hkN j (by omega) hj

/-- **The modal weight is at least `1 / (N + 1)`.** -/
theorem one_le_succ_mul_binTerm {N k : ℕ} (hkN : k ≤ N) :
    1 ≤ ((N : ℝ) + 1) * binTerm ((k : ℝ) / N) N k := by
  have hsum := sum_binTerm ((k : ℝ) / N) N
  have hle : ∑ j ∈ range (N + 1), binTerm ((k : ℝ) / N) N j
      ≤ ∑ _j ∈ range (N + 1), binTerm ((k : ℝ) / N) N k := by
    refine Finset.sum_le_sum (fun j hj => ?_)
    exact binTerm_le_mode hkN (by simpa [Nat.lt_succ_iff] using mem_range.mp hj)
  rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
  push_cast at hle
  linarith






open Catalog.Probability.NeuralCoding.SparseEntropy in
theorem solution{N k : ℕ} (hk : 0 < k) (hkN : k < N) :
    Real.exp ((N : ℝ) * Real.binEntropy ((k : ℝ) / N)) ≤ ((N : ℝ) + 1) * (N.choose k : ℝ) := by
  have hN : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set p : ℝ := (k : ℝ) / N with hpdef
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hp0 : 0 < p := div_pos hkR hNR
  have hp1 : p < 1 := by rw [hpdef, div_lt_one hNR]; exact_mod_cast hkN
  have hw : (0 : ℝ) < p ^ k * (1 - p) ^ (N - k) := by
    have : (0 : ℝ) < 1 - p := by linarith
    positivity
  have hmode := one_le_succ_mul_binTerm (N := N) (k := k) hkN.le
  rw [binTerm] at hmode
  -- `1 ≤ (N+1) * (C(N,k) * w)` with `w = p^k (1-p)^{N-k}`
  have hstep : 1 ≤ (((N : ℝ) + 1) * (N.choose k : ℝ)) * (p ^ k * (1 - p) ^ (N - k)) := by
    rw [mul_assoc]; exact hmode
  rw [exp_binEntropy_eq hk hkN, ← hpdef]
  rw [inv_le_iff_one_le_mul₀ hw]
  linarith
