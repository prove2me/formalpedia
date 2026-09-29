-- Prove2me | solution 1 for GaussPascal.gaussBinom_pascal_p
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T00:59:59.164543+00:00
-- url     : https://prove2.me/submissions/5c8b1c25-347b-4deb-b6c2-b8a14be1adc7

-- Sol generated from Algebra/GaussianBinomialPascal.lean
import Mathlib
import Definitions.Def_Algebra_GaussianBinomialPascal
import Theorems.Thm_GaussPascal_cast_prod_pow_sub
import Theorems.Thm_GaussPascal_denom_mul_qBinom
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



theorem qBinom_succ_succ (q n k : ℕ) :
    qBinom q (n + 1) (k + 1) = qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1) := rfl

theorem qBinom_eq_zero_of_lt {q n k : ℕ} (h : n < k) : qBinom q n k = 0 := by
  induction n generalizing k with
  | zero => obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0); rfl
  | succ n ih =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      rw [qBinom_succ_succ, ih (by omega), ih (by omega)]
      simp

@[simp] theorem qBinom_self (q n : ℕ) : qBinom q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [qBinom_succ_succ, ih, qBinom_eq_zero_of_lt (by omega)]; simp



theorem qFactZ_pos {q : ℕ} (hq : 2 ≤ q) (m : ℕ) : 0 < qFactZ q m := by
  refine Finset.prod_pos fun j _ => ?_
  have h1 : (1 : ℤ) < (q : ℤ) := by exact_mod_cast hq.trans_lt' one_lt_two
  have : (1 : ℤ) < (q : ℤ) ^ (j + 1) := one_lt_pow₀ h1 (by omega)
  omega

/-! ## The `q`-factorial identity -/



/-- **Symmetry of the recursive `q`-binomial coefficient**, for every base `q ≥ 2`. -/
theorem qBinom_symm {q : ℕ} (hq : 2 ≤ q) {n k : ℕ} (hk : k ≤ n) :
    qBinom q n k = qBinom q n (n - k) := by
  have h1 := qFactZ_mul_qBinom q hk
  have h2 := qFactZ_mul_qBinom q (Nat.sub_le n k)
  rw [Nat.sub_sub_self hk] at h2
  have hpos : (0 : ℤ) < qFactZ q k * qFactZ q (n - k) :=
    mul_pos (qFactZ_pos hq k) (qFactZ_pos hq (n - k))
  have : qFactZ q k * qFactZ q (n - k) * (qBinom q n k : ℤ)
      = qFactZ q k * qFactZ q (n - k) * (qBinom q n (n - k) : ℤ) := by
    rw [h1, ← h2]; ring
  have := mul_left_cancel₀ (ne_of_gt hpos) this
  exact_mod_cast this

/-! ## Identification of the two definitions -/






/-- The denominator of `gaussBinom` is positive for `q ≥ 2`. -/
theorem denom_nat_pos {q : ℕ} (hq : 2 ≤ q) (k : ℕ) :
    0 < ∏ i ∈ Finset.range k, (q ^ k - q ^ i) := by
  refine Finset.prod_pos fun i hi => ?_
  have : q ^ i < q ^ k := Nat.pow_lt_pow_right (by omega) (Finset.mem_range.mp hi)
  omega

/-- `gaussBinom` vanishes above the diagonal. -/
@[simp] theorem gaussBinom_eq_zero_of_lt {q n k : ℕ} (h : n < k) : gaussBinom q n k = 0 := by
  have hmem : n ∈ Finset.range k := Finset.mem_range.mpr h
  rw [gaussBinom, Finset.prod_eq_zero hmem (by omega), Nat.zero_div]

/-- **The two definitions agree.**  For every base `q ≥ 2` the truncated natural division
defining `gaussBinom` is exact and computes the recursively defined `qBinom`. -/
theorem gaussBinom_eq_qBinom {q : ℕ} (hq : 2 ≤ q) (n k : ℕ) :
    gaussBinom q n k = qBinom q n k := by
  by_cases hk : k ≤ n
  · have hZ := denom_mul_qBinom q hq hk
    rw [← cast_prod_pow_sub (q := q) (by omega) k k, ← cast_prod_pow_sub (q := q) (by omega) n k] at hZ
    have hN : (∏ i ∈ Finset.range k, (q ^ k - q ^ i)) * qBinom q n k
        = ∏ i ∈ Finset.range k, (q ^ n - q ^ i) := by exact_mod_cast hZ
    rw [gaussBinom, ← hN, Nat.mul_div_cancel_left _ (denom_nat_pos hq k)]
  · push_neg at hk
    rw [gaussBinom_eq_zero_of_lt hk, qBinom_eq_zero_of_lt hk]

/-! ## The main theorems about `gaussBinom` -/

/-- **The `q`-Pascal recursion**, in `ℕ`, for every base `q ≥ 2`. -/
theorem gaussBinom_pascal {q : ℕ} (hq : 2 ≤ q) (n k : ℕ) :
    gaussBinom q (n + 1) (k + 1) = gaussBinom q n k + q ^ (k + 1) * gaussBinom q n (k + 1) := by
  rw [gaussBinom_eq_qBinom hq, gaussBinom_eq_qBinom hq, gaussBinom_eq_qBinom hq,
    qBinom_succ_succ]

/-- **Symmetry of the Gaussian binomial coefficient for an arbitrary base `q ≥ 2`.**  This
generalises `SubspaceCounting.gaussBinom_symm`, which was available only for prime `q`. -/
theorem gaussBinom_symm {q : ℕ} (hq : 2 ≤ q) {n k : ℕ} (hk : k ≤ n) :
    gaussBinom q n k = gaussBinom q n (n - k) := by
  rw [gaussBinom_eq_qBinom hq, gaussBinom_eq_qBinom hq, qBinom_symm hq hk]



@[simp] theorem gaussBinom_zero (q n : ℕ) : gaussBinom q n 0 = 1 := by simp [gaussBinom]

@[simp] theorem gaussBinom_self {q : ℕ} (hq : 2 ≤ q) (n : ℕ) : gaussBinom q n n = 1 := by
  rw [gaussBinom_eq_qBinom hq, qBinom_self]



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
theorem solution{q : ℕ} (hq : 2 ≤ q) (n k : ℕ) :
    gaussBinom q (n + 1) (k + 1) = q ^ (n - k) * gaussBinom q n k + gaussBinom q n (k + 1) := by
  by_cases hk : k ≤ n
  · have h1 : gaussBinom q (n + 1) (k + 1) = gaussBinom q (n + 1) (n - k) := by
      rw [gaussBinom_symm hq (show k + 1 ≤ n + 1 by omega)]
      congr 1
      omega
    rw [h1]
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · have h2 : k - k = 0 := by omega
      rw [h2, gaussBinom_zero, gaussBinom_self hq, gaussBinom_eq_zero_of_lt (Nat.lt_succ_self k)]
      simp
    · obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - k - 1, by omega⟩
      have hmn : m ≤ n := by omega
      have hnm : n - m = k + 1 := by omega
      have hm1 : m + 1 = n - k := hm.symm
      rw [hm, gaussBinom_pascal hq n m, gaussBinom_symm hq hmn, hnm, hm1,
        gaussBinom_symm hq (show n - k ≤ n by omega)]
      have : n - (n - k) = k := by omega
      rw [this, Nat.add_comm]
  · push_neg at hk
    rw [gaussBinom_eq_zero_of_lt (by omega : n + 1 < k + 1),
      gaussBinom_eq_zero_of_lt (by omega : n < k),
      gaussBinom_eq_zero_of_lt (by omega : n < k + 1)]
    simp
