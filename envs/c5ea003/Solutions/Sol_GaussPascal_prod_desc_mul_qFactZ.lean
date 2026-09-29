-- Prove2me | solution 1 for GaussPascal.prod_desc_mul_qFactZ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:25:13.741051+00:00
-- url     : https://prove2.me/submissions/216af88b-5443-451f-a1dd-fc75c747250e

-- Sol generated from Algebra/GaussianBinomialPascal.lean
import Mathlib
import Definitions.Def_Algebra_GaussianBinomialPascal
/-
# The `q`-Pascal recursion for Gaussian binomial coefficients

This file settles target 2 of the previous research cycle of the conditional Hilbert class field
thread: it proves the `q`-Pascal recursion

`gaussBinom q (n+1) (k+1) = gaussBinom q n k + q^(k+1) * gaussBinom q n (k+1)`

*directly in `ℕ`* for every base `q ≥ 2`, and deduces the symmetry
`gaussBinom q n k = gaussBinom q n (n - k)` for arbitrary `q ≥ 2` — not only for prime `q`,
where the earlier proof (`Catalog/NumberTheory/SubspaceCounting.lean`) went through the
`(ZMod q)^n` subspace model and therefore required `q` to be a prime power realised by a field.

The Gaussian binomial coefficient is the one used in `Catalog/NumberTheory/SubspaceCounting.lean`,

`gaussBinom q n k = (∏_{i<k} (q^n - q^i)) / (∏_{i<k} (q^k - q^i))`,

a truncated natural division of two natural numbers.  The whole point of the file is that this
division is exact and that the resulting arithmetic function obeys the `q`-Pascal recursion.

## Strategy

* `qBinom` is the recursively defined `q`-binomial coefficient (`q`-Pascal by fiat);
* `qFactZ q m = ∏_{j<m} (q^{j+1} - 1)` is the `q`-factorial, computed in `ℤ` so that no truncated
  subtraction occurs;
* `qFactZ_mul_qBinom` : `qFactZ q k * qFactZ q (n-k) * qBinom q n k = qFactZ q n` for `k ≤ n`
  (induction on `n`, the heart of the file);
* `gaussBinom_eq_qBinom` : the truncated division defining `gaussBinom` is exact and computes
  `qBinom`, for every `q ≥ 2`;
* consequently `gaussBinom_pascal`, `gaussBinom_symm`, `gaussBinom_pos`,
  `gaussBinom_mul_qFact` and the closed form `gaussBinom q n 1 = ∑_{i<n} q^i`.

All results are unconditional in `q ≥ 2`; the case `q = 4` (not a prime) is recorded explicitly.
-/


open Finset

open GaussPascal




/-! ## Elementary properties of `qBinom` and `qFactZ` -/







theorem qFactZ_succ (q m : ℕ) : qFactZ q (m + 1) = qFactZ q m * ((q : ℤ) ^ (m + 1) - 1) := by
  simp [qFactZ, Finset.prod_range_succ]


/-! ## The `q`-factorial identity -/




/-! ## Identification of the two definitions -/









/-! ## The main theorems about `gaussBinom` -/









/-! ## Explicit values: the falsifiable checks

The base `q = 4` is not prime, so none of these values were accessible from the subspace model of
`Catalog/NumberTheory/SubspaceCounting.lean`. -/






/-! ## The dual recursion and the Galois numbers

The `q`-Pascal recursion has a mirror image, obtained from `gaussBinom_symm`; the two together
give the classical three-term recursion for the **Galois numbers** `G_q(n) = ∑_{k≤n} binom(n,k)_q`
(the number of subspaces of an `n`-dimensional space over a field with `q` elements; OEIS A006116
for `q = 2`).  The auxiliary sequence is the `q`-weighted sum `S_q(n) = ∑_{k≤n} q^k binom(n,k)_q`.
-/

open GaussPascal














open GaussPascal in
theorem solution(q : ℕ) : ∀ {n k : ℕ}, k ≤ n →
    (∏ i ∈ Finset.range k, ((q : ℤ) ^ (n - i) - 1)) * qFactZ q (n - k) = qFactZ q n := by
  intro n k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hkn : k ≤ n := by omega
      have hnk : n - k = (n - (k + 1)) + 1 := by omega
      rw [Finset.prod_range_succ]
      have : ((q : ℤ) ^ (n - k) - 1) * qFactZ q (n - (k + 1)) = qFactZ q (n - k) := by
        rw [hnk, qFactZ_succ, ← hnk]; ring
      calc (∏ i ∈ Finset.range k, ((q : ℤ) ^ (n - i) - 1)) * ((q : ℤ) ^ (n - k) - 1)
            * qFactZ q (n - (k + 1))
          = (∏ i ∈ Finset.range k, ((q : ℤ) ^ (n - i) - 1))
            * (((q : ℤ) ^ (n - k) - 1) * qFactZ q (n - (k + 1))) := by ring
        _ = qFactZ q n := by rw [this, ih hkn]
