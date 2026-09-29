-- Prove2me | Theorems.Thm_GaussPascal_denom_mul_qBinom
-- name    : GaussPascal.denom_mul_qBinom
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:33:24.229432+00:00
-- url     : https://prove2.me/theorems/c6810c42-215e-4312-a23d-e96d26a07825
-- title:
--   Exactness of the division defining `gaussBinom`, in `ℤ`.
-- statement:
--   **Exactness of the division defining `gaussBinom`**, in `ℤ`.
--
--   ```lean
--   theorem GaussPascal.denom_mul_qBinom(q : ℕ) {n k : ℕ} (hq : 2 ≤ q) (hk : k ≤ n) :
--       (∏ i ∈ Finset.range k, ((q : ℤ) ^ k - (q : ℤ) ^ i)) * (qBinom q n k : ℤ)
--         = ∏ i ∈ Finset.range k, ((q : ℤ) ^ n - (q : ℤ) ^ i) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/GaussianBinomialPascal.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/GaussianBinomialPascal.lean#L208

-- Thm stub generated from Algebra/GaussianBinomialPascal.lean
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









/-! ## The `q`-factorial identity -/




/-! ## Identification of the two definitions -/

theorem GaussPascal.denom_mul_qBinom(q : ℕ) {n k : ℕ} (hq : 2 ≤ q) (hk : k ≤ n) :
    (∏ i ∈ Finset.range k, ((q : ℤ) ^ k - (q : ℤ) ^ i)) * (qBinom q n k : ℤ)
      = ∏ i ∈ Finset.range k, ((q : ℤ) ^ n - (q : ℤ) ^ i) := by sorry
