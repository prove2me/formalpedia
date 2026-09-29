-- Prove2me | solution 1 for GaussPascal.qWeightedSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:09:02.080994+00:00
-- url     : https://prove2.me/submissions/33d1bb8b-e567-4b09-a05f-fb7e975e5b20

import Mathlib
import Definitions.Def_Algebra_GaussianBinomialPascal

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Algebra/GaussianBinomialPascal.lean ====
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

-- [dropped: platform already declares gaussBinom]
-- [dropped: platform already declares qBinom]
-- [dropped: platform already declares qFactZ]
@[simp] theorem qBinom_zero_right (q n : ℕ) : qBinom q n 0 = 1 := by
  cases n <;> rfl

@[simp] theorem qBinom_zero_succ (q k : ℕ) : qBinom q 0 (k + 1) = 0 := rfl

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

@[simp] theorem qFactZ_zero (q : ℕ) : qFactZ q 0 = 1 := by simp [qFactZ]

theorem qFactZ_succ (q m : ℕ) : qFactZ q (m + 1) = qFactZ q m * ((q : ℤ) ^ (m + 1) - 1) := by
  simp [qFactZ, Finset.prod_range_succ]

theorem qFactZ_pos {q : ℕ} (hq : 2 ≤ q) (m : ℕ) : 0 < qFactZ q m := by
  refine Finset.prod_pos fun j _ => ?_
  have h1 : (1 : ℤ) < (q : ℤ) := by exact_mod_cast hq.trans_lt' one_lt_two
  have : (1 : ℤ) < (q : ℤ) ^ (j + 1) := one_lt_pow₀ h1 (by omega)
  omega

/-! ## The `q`-factorial identity -/

/-- **The key identity.**  `qFactZ q k * qFactZ q (n-k) * qBinom q n k = qFactZ q n` for `k ≤ n`,
proved by induction on `n` from the `q`-Pascal recursion. -/
theorem qFactZ_mul_qBinom (q : ℕ) : ∀ {n k : ℕ}, k ≤ n →
    qFactZ q k * qFactZ q (n - k) * (qBinom q n k : ℤ) = qFactZ q n := by
  intro n
  induction n with
  | zero => intro k hk; interval_cases k; simp
  | succ n ih =>
      intro k hk
      match k with
      | 0 => simp
      | (k + 1) =>
        have hkn : k ≤ n := by omega
        have hsub : n + 1 - (k + 1) = n - k := by omega
        rcases eq_or_lt_of_le hkn with rfl | hlt
        · -- `k = n`: the second term of the recursion vanishes
          rw [hsub, qBinom_succ_succ, qBinom_eq_zero_of_lt (Nat.lt_succ_self _)]
          simp
        · -- `k < n`
          have h1 := ih hkn
          have h2 := ih (by omega : k + 1 ≤ n)
          have hnk : n - k = (n - (k + 1)) + 1 := by omega
          have hpow : (q : ℤ) ^ (k + 1) * (q : ℤ) ^ (n - k) = (q : ℤ) ^ (n + 1) := by
            rw [← pow_add]; congr 1; omega
          rw [hnk, qFactZ_succ q (n - (k + 1)), ← hnk] at h1
          rw [qFactZ_succ q k] at h2
          rw [hsub, qBinom_succ_succ]
          push_cast
          rw [qFactZ_succ q k, hnk, qFactZ_succ q (n - (k + 1)), qFactZ_succ q n, ← hnk]
          linear_combination ((q : ℤ) ^ (k + 1) - 1) * h1
            + (q : ℤ) ^ (k + 1) * ((q : ℤ) ^ (n - k) - 1) * h2 + qFactZ q n * hpow

/-- Positivity of the recursive `q`-binomial coefficient in the admissible range. -/
theorem qBinom_pos {q : ℕ} (hq : 2 ≤ q) {n k : ℕ} (hk : k ≤ n) : 0 < qBinom q n k := by
  rcases Nat.eq_zero_or_pos (qBinom q n k) with h | h
  · exfalso
    have := qFactZ_mul_qBinom q hk
    rw [h] at this
    have hpos := qFactZ_pos hq n
    simp at this
    omega
  · exact h

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

/-- The numerator of `gaussBinom`, computed in `ℤ`: truncated subtraction does no harm because
for `k > n` both products vanish (at the index `i = n`). -/
theorem cast_prod_pow_sub {q : ℕ} (hq : 1 ≤ q) (n k : ℕ) :
    ((∏ i ∈ Finset.range k, (q ^ n - q ^ i) : ℕ) : ℤ)
      = ∏ i ∈ Finset.range k, ((q : ℤ) ^ n - (q : ℤ) ^ i) := by
  by_cases hk : k ≤ n
  · rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' : i ≤ n := le_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)
    have hle : q ^ i ≤ q ^ n := Nat.pow_le_pow_right hq hi'
    push_cast [Nat.cast_sub hle]
    ring
  · push_neg at hk
    have hmem : n ∈ Finset.range k := Finset.mem_range.mpr hk
    rw [Finset.prod_eq_zero hmem (by omega), Finset.prod_eq_zero hmem (by ring)]
    simp

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

/-- The "descending" product `∏_{i<k}(q^{n-i}-1)` completes `qFactZ q (n-k)` to `qFactZ q n`. -/
theorem prod_desc_mul_qFactZ (q : ℕ) : ∀ {n k : ℕ}, k ≤ n →
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

/-- The denominator of `gaussBinom`, in `ℤ`: `∏_{i<k}(q^k - q^i) = q^{k(k-1)/2} * qFactZ q k`. -/
theorem denom_eq (q k : ℕ) :
    ∏ i ∈ Finset.range k, ((q : ℤ) ^ k - (q : ℤ) ^ i)
      = (q : ℤ) ^ (∑ i ∈ Finset.range k, i) * qFactZ q k := by
  rw [prod_pow_sub_eq q (le_refl k)]
  congr 1
  have := prod_desc_mul_qFactZ q (le_refl k)
  simpa using this

/-- **Exactness of the division defining `gaussBinom`**, in `ℤ`. -/
theorem denom_mul_qBinom (q : ℕ) {n k : ℕ} (hq : 2 ≤ q) (hk : k ≤ n) :
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

/-- **Positivity for an arbitrary base `q ≥ 2`.** -/
theorem gaussBinom_pos {q : ℕ} (hq : 2 ≤ q) {n k : ℕ} (hk : k ≤ n) : 0 < gaussBinom q n k := by
  rw [gaussBinom_eq_qBinom hq]; exact qBinom_pos hq hk

/-- The `q`-factorial identity for `gaussBinom` itself, over `ℤ`. -/
theorem qFactZ_mul_gaussBinom {q : ℕ} (hq : 2 ≤ q) {n k : ℕ} (hk : k ≤ n) :
    qFactZ q k * qFactZ q (n - k) * (gaussBinom q n k : ℤ) = qFactZ q n := by
  rw [gaussBinom_eq_qBinom hq]; exact qFactZ_mul_qBinom q hk

@[simp] theorem gaussBinom_zero (q n : ℕ) : gaussBinom q n 0 = 1 := by simp [gaussBinom]

@[simp] theorem gaussBinom_self {q : ℕ} (hq : 2 ≤ q) (n : ℕ) : gaussBinom q n n = 1 := by
  rw [gaussBinom_eq_qBinom hq, qBinom_self]

/-- **Closed form in the first column.**  `binom(n,1)_q = 1 + q + ... + q^{n-1}`. -/
theorem gaussBinom_one {q : ℕ} (hq : 2 ≤ q) (n : ℕ) :
    gaussBinom q n 1 = ∑ i ∈ Finset.range n, q ^ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [gaussBinom_pascal hq n 0, ih, gaussBinom_zero, Finset.sum_range_succ']
      simp [Finset.mul_sum, pow_succ, mul_comm, Nat.add_comm]

/-- **The second column.**  `binom(n+1,1)_q = 1 + q * binom(n,1)_q`, a sanity check of the
recursion in a form independent of the closed formula. -/
theorem gaussBinom_one_succ {q : ℕ} (hq : 2 ≤ q) (n : ℕ) :
    gaussBinom q (n + 1) 1 = 1 + q * gaussBinom q n 1 := by
  rw [gaussBinom_pascal hq n 0, gaussBinom_zero, pow_one]

/-! ## Explicit values: the falsifiable checks

The base `q = 4` is not prime, so none of these values were accessible from the subspace model of
`Catalog/NumberTheory/SubspaceCounting.lean`. -/

theorem gaussBinom_four_two_one : gaussBinom 4 2 1 = 5 := by decide

/-- The falsifiable instance of the `q`-Pascal recursion announced for `q = 4, n = 2, k = 1`. -/
theorem gaussBinom_pascal_four :
    gaussBinom 4 2 1 = gaussBinom 4 1 0 + 4 ^ 1 * gaussBinom 4 1 1 :=
  gaussBinom_pascal (by norm_num) 1 0

/-- Symmetry at the non-prime base `q = 6`. -/
theorem gaussBinom_symm_six : gaussBinom 6 5 2 = gaussBinom 6 5 3 :=
  gaussBinom_symm (by norm_num) (by norm_num)

/-- The Galois number `∑_{k ≤ 3} binom(3,k)_4 = 1 + 21 + 21 + 1 = 44`. -/
theorem galois_number_four_three : ∑ k ∈ Finset.range 4, gaussBinom 4 3 k = 44 := by decide

end GaussPascal

/-! ## The dual recursion and the Galois numbers

The `q`-Pascal recursion has a mirror image, obtained from `gaussBinom_symm`; the two together
give the classical three-term recursion for the **Galois numbers** `G_q(n) = ∑_{k≤n} binom(n,k)_q`
(the number of subspaces of an `n`-dimensional space over a field with `q` elements; OEIS A006116
for `q = 2`).  The auxiliary sequence is the `q`-weighted sum `S_q(n) = ∑_{k≤n} q^k binom(n,k)_q`.
-/

namespace GaussPascal

/-- **The dual `q`-Pascal recursion**, `binom(n+1,k+1)_q = q^{n-k} binom(n,k)_q + binom(n,k+1)_q`,
obtained from `gaussBinom_pascal` by symmetry. -/
theorem gaussBinom_pascal' {q : ℕ} (hq : 2 ≤ q) (n k : ℕ) :
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

-- [dropped: platform already declares galoisNumber]
-- [dropped: platform already declares qWeightedSum]
theorem qWeightedSum_eq_tail_add_one (q n : ℕ) :
    qWeightedSum q n
      = (∑ k ∈ Finset.range (n + 1), q ^ (k + 1) * gaussBinom q n (k + 1)) + 1 := by
  rw [Finset.sum_range_succ (fun k => q ^ (k + 1) * gaussBinom q n (k + 1)) n,
    gaussBinom_eq_zero_of_lt (Nat.lt_succ_self n)]
  rw [qWeightedSum, Finset.sum_range_succ' (fun k => q ^ k * gaussBinom q n k) n]
  simp

/-- **The Galois numbers grow by the `q`-weighted sum.** -/
theorem galoisNumber_succ {q : ℕ} (hq : 2 ≤ q) (n : ℕ) :
    galoisNumber q (n + 1) = galoisNumber q n + qWeightedSum q n := by
  rw [galoisNumber, Finset.sum_range_succ' (fun k => gaussBinom q (n + 1) k) (n + 1),
    gaussBinom_zero]
  rw [Finset.sum_congr rfl fun k _ => gaussBinom_pascal hq n k, Finset.sum_add_distrib,
    qWeightedSum_eq_tail_add_one, galoisNumber]
  omega

/-- **The recursion for the `q`-weighted sums.** -/
theorem qWeightedSum_succ {q : ℕ} (hq : 2 ≤ q) (n : ℕ) :
    qWeightedSum q (n + 1) = q ^ (n + 1) * galoisNumber q n + qWeightedSum q n := by
  rw [qWeightedSum, Finset.sum_range_succ' (fun k => q ^ k * gaussBinom q (n + 1) k) (n + 1)]
  have hterm : ∀ k ∈ Finset.range (n + 1),
      q ^ (k + 1) * gaussBinom q (n + 1) (k + 1)
        = q ^ (n + 1) * gaussBinom q n k + q ^ (k + 1) * gaussBinom q n (k + 1) := by
    intro k hk
    have hkn : k ≤ n := by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hpow : q ^ (k + 1) * q ^ (n - k) = q ^ (n + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [gaussBinom_pascal' hq n k, Nat.mul_add, ← mul_assoc, hpow]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
    qWeightedSum_eq_tail_add_one, galoisNumber]
  simp [pow_zero]
  omega

/-- **The three-term recursion for the Galois numbers**,
`G_q(n+2) = 2 G_q(n+1) + (q^{n+1} - 1) G_q(n)`, written without truncated subtraction. -/
theorem galoisNumber_recursion {q : ℕ} (hq : 2 ≤ q) (n : ℕ) :
    galoisNumber q (n + 2) + galoisNumber q n
      = 2 * galoisNumber q (n + 1) + q ^ (n + 1) * galoisNumber q n := by
  have h1 : galoisNumber q (n + 2) = galoisNumber q (n + 1) + qWeightedSum q (n + 1) := by
    simpa using galoisNumber_succ hq (n + 1)
  have h2 := galoisNumber_succ hq n
  have h3 := qWeightedSum_succ hq n
  omega

@[simp] theorem galoisNumber_zero (q : ℕ) : galoisNumber q 0 = 1 := by
  simp [galoisNumber]

theorem galoisNumber_one {q : ℕ} (hq : 2 ≤ q) : galoisNumber q 1 = 2 := by
  simp [galoisNumber, Finset.sum_range_succ, gaussBinom_self hq]

/-- `G_q(2) = q + 3`: the `q + 1` "lines", together with `0` and the whole plane.  This is the
Gaussian-binomial counterpart of the group-theoretic count
`SubgroupCount.card_subgroup_of_sq_prime_card` of `Catalog/Algebra/SubgroupCountFiniteAbelian.lean`,
which says that an elementary abelian group of order `p²` has `p + 3` subgroups. -/
theorem galoisNumber_two {q : ℕ} (hq : 2 ≤ q) : galoisNumber q 2 = q + 3 := by
  rw [galoisNumber, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, gaussBinom_zero, gaussBinom_one hq, gaussBinom_self hq]
  simp [Finset.sum_range_succ]
  omega

/-- The Galois numbers for `q = 2` are `1, 2, 5, 16, 67, 374` (OEIS A006116). -/
theorem galoisNumber_two_values :
    galoisNumber 2 0 = 1 ∧ galoisNumber 2 1 = 2 ∧ galoisNumber 2 2 = 5 ∧ galoisNumber 2 3 = 16 ∧
      galoisNumber 2 4 = 67 ∧ galoisNumber 2 5 = 374 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The `q = 3` Galois numbers `1, 2, 6, 28, 212` (OEIS A006117), obtained from the recursion
rather than by direct evaluation. -/
theorem galoisNumber_three_four : galoisNumber 3 4 = 212 := by
  have h := galoisNumber_recursion (q := 3) (by norm_num) 2
  have h2 : galoisNumber 3 2 = 6 := by decide
  have h3 : galoisNumber 3 3 = 28 := by decide
  norm_num [h2, h3] at h
  omega

end GaussPascal
section
open Finset
open GaussPascal
open GaussPascal

theorem solution {q : ℕ} (hq : 2 ≤ q) (n : ℕ) :
    qWeightedSum q (n + 1) = q ^ (n + 1) * galoisNumber q n + qWeightedSum q n :=
  @GaussPascal.qWeightedSum_succ q hq n

end
