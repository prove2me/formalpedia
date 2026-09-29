-- Prove2me | Definitions.Def_Algebra_GaussianBinomialPascal
-- name    : Algebra_GaussianBinomialPascal
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:14:22.406009+00:00
-- url     : https://prove2.me/theorems/9624db10-8b4d-48c8-b803-42a43d408080
-- title:
--   Aether Catalog definitions — Algebra_GaussianBinomialPascal
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.GaussianBinomialPascal`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/GaussianBinomialPascal.lean by skeleton subtraction
import Mathlib
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

namespace GaussPascal

/-- The Gaussian (`q`-)binomial coefficient `binom(n,k)_q`, defined as the truncated natural
quotient `∏_{i<k}(q^n - q^i) / ∏_{i<k}(q^k - q^i)`.  This is the definition used in
`Catalog/NumberTheory/SubspaceCounting.lean`. -/
def gaussBinom (q n k : ℕ) : ℕ :=
  (∏ i ∈ Finset.range k, (q ^ n - q ^ i)) / (∏ i ∈ Finset.range k, (q ^ k - q ^ i))

/-- The `q`-binomial coefficient defined by the `q`-Pascal recursion. -/
def qBinom (q : ℕ) : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1)

/-- The `q`-factorial `∏_{j<m}(q^{j+1} - 1)`, computed in `ℤ` to avoid truncated subtraction. -/
def qFactZ (q m : ℕ) : ℤ := ∏ j ∈ Finset.range m, ((q : ℤ) ^ (j + 1) - 1)

/-! ## Elementary properties of `qBinom` and `qFactZ` -/









/-! ## The `q`-factorial identity -/




/-! ## Identification of the two definitions -/









/-! ## The main theorems about `gaussBinom` -/









/-! ## Explicit values: the falsifiable checks

The base `q = 4` is not prime, so none of these values were accessible from the subspace model of
`Catalog/NumberTheory/SubspaceCounting.lean`. -/





end GaussPascal

/-! ## The dual recursion and the Galois numbers

The `q`-Pascal recursion has a mirror image, obtained from `gaussBinom_symm`; the two together
give the classical three-term recursion for the **Galois numbers** `G_q(n) = ∑_{k≤n} binom(n,k)_q`
(the number of subspaces of an `n`-dimensional space over a field with `q` elements; OEIS A006116
for `q = 2`).  The auxiliary sequence is the `q`-weighted sum `S_q(n) = ∑_{k≤n} q^k binom(n,k)_q`.
-/

namespace GaussPascal


/-- The **Galois number** `G_q(n) = ∑_{k ≤ n} binom(n,k)_q`. -/
def galoisNumber (q n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), gaussBinom q n k

/-- The `q`-weighted sum `S_q(n) = ∑_{k ≤ n} q^k binom(n,k)_q`. -/
def qWeightedSum (q n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), q ^ k * gaussBinom q n k










end GaussPascal


