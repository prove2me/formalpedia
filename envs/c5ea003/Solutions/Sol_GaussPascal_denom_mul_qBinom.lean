-- Prove2me | solution 1 for GaussPascal.denom_mul_qBinom
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:29:39.441239+00:00
-- url     : https://prove2.me/submissions/7d7e106b-1e26-4cd0-8a83-6a6320db94bd

-- Sol generated from Algebra/GaussianBinomialPascal.lean
import Mathlib
import Definitions.Def_Algebra_GaussianBinomialPascal
import Theorems.Thm_GaussPascal_prod_desc_mul_qFactZ
import Theorems.Thm_GaussPascal_qFactZ_mul_qBinom
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






@[simp] theorem qFactZ_zero (q : ℕ) : qFactZ q 0 = 1 := by simp [qFactZ]


theorem qFactZ_pos {q : ℕ} (hq : 2 ≤ q) (m : ℕ) : 0 < qFactZ q m := by
  refine Finset.prod_pos fun j _ => ?_
  have h1 : (1 : ℤ) < (q : ℤ) := by exact_mod_cast hq.trans_lt' one_lt_two
  have : (1 : ℤ) < (q : ℤ) ^ (j + 1) := one_lt_pow₀ h1 (by omega)
  omega

/-! ## The `q`-factorial identity -/




/-! ## Identification of the two definitions -/


/-- The numerator of `gaussBinom` factors as `q^{k(k-1)/2}` times a product of `q^j - 1`. -/
theorem prod_pow_sub_eq (q : ℕ) {n k : ℕ} (hk : k ≤ n) :
    ∏ i ∈ Finset.range k, ((q : ℤ) ^ n - (q : ℤ) ^ i)
      = (q : ℤ) ^ (∑ i ∈ Finset.range k, i) * ∏ i ∈ Finset.range k, ((q : ℤ) ^ (n - i) - 1) := by
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i ≤ n := le_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)
  have : (q : ℤ) ^ i * (q : ℤ) ^ (n - i) = (q : ℤ) ^ n := by
    rw [← pow_add]; congr 1; omega
  rw [mul_sub, this, mul_one]


/-- The denominator of `gaussBinom`, in `ℤ`: `∏_{i<k}(q^k - q^i) = q^{k(k-1)/2} * qFactZ q k`. -/
theorem denom_eq (q k : ℕ) :
    ∏ i ∈ Finset.range k, ((q : ℤ) ^ k - (q : ℤ) ^ i)
      = (q : ℤ) ^ (∑ i ∈ Finset.range k, i) * qFactZ q k := by
  rw [prod_pow_sub_eq q (le_refl k)]
  congr 1
  have := prod_desc_mul_qFactZ q (le_refl k)
  simpa using this





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
theorem solution(q : ℕ) {n k : ℕ} (hq : 2 ≤ q) (hk : k ≤ n) :
    (∏ i ∈ Finset.range k, ((q : ℤ) ^ k - (q : ℤ) ^ i)) * (qBinom q n k : ℤ)
      = ∏ i ∈ Finset.range k, ((q : ℤ) ^ n - (q : ℤ) ^ i) := by
  have hq0 : (0 : ℤ) < (q : ℤ) := by exact_mod_cast (by omega : 0 < q)
  have hpow : (0 : ℤ) < (q : ℤ) ^ (∑ i ∈ Finset.range k, i) := pow_pos hq0 _
  have hnk : (0 : ℤ) < qFactZ q (n - k) := qFactZ_pos hq _
  rw [denom_eq, prod_pow_sub_eq q hk]
  -- cancel `q^{k(k-1)/2}` and `qFactZ q (n-k)`
  refine mul_left_cancel₀ (ne_of_gt hnk) ?_
  have h1 := qFactZ_mul_qBinom q hk
  have h2 := prod_desc_mul_qFactZ q hk
  calc qFactZ q (n - k) * ((q : ℤ) ^ (∑ i ∈ Finset.range k, i) * qFactZ q k * (qBinom q n k : ℤ))
      = (q : ℤ) ^ (∑ i ∈ Finset.range k, i)
        * (qFactZ q k * qFactZ q (n - k) * (qBinom q n k : ℤ)) := by ring
    _ = (q : ℤ) ^ (∑ i ∈ Finset.range k, i) * qFactZ q n := by rw [h1]
    _ = (q : ℤ) ^ (∑ i ∈ Finset.range k, i)
        * ((∏ i ∈ Finset.range k, ((q : ℤ) ^ (n - i) - 1)) * qFactZ q (n - k)) := by rw [h2]
    _ = qFactZ q (n - k) * ((q : ℤ) ^ (∑ i ∈ Finset.range k, i)
        * ∏ i ∈ Finset.range k, ((q : ℤ) ^ (n - i) - 1)) := by ring
