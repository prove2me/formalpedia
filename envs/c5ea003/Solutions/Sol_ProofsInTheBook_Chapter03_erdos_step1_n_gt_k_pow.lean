-- Prove2me | solution 1 for ProofsInTheBook.Chapter03.erdos_step1_n_gt_k_pow
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T17:17:06.72883+00:00
-- url     : https://prove2.me/submissions/30d00944-930e-4f38-b2e5-2aee4d49decd

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
import Theorems.Thm_ProofsInTheBook_Chapter03_exists_large_prime_factor_choose_below_sq_of_9_le
import Theorems.Thm_ProofsInTheBook_Chapter03_exists_large_prime_factor_choose_of_pow_gap
import Theorems.Thm_ProofsInTheBook_Chapter03_exists_large_prime_factor_choose_of_sq_le_and_primeCounting_gap
import Theorems.Thm_ProofsInTheBook_Chapter03_pow_gap_small_k_tail
import Theorems.Thm_ProofsInTheBook_Chapter03_pow_l_dvd_one_factor_of_descFactorial
import Theorems.Thm_ProofsInTheBook_Chapter03_primeCounting_gap_of_120_le
import Theorems.Thm_ProofsInTheBook_Chapter03_primeCounting_gap_of_19_le


/-!
# Chapter 3: Binomial coefficients are (almost) never powers

From "Proofs from THE BOOK" (Aigner & Ziegler).

## Book content summary

The book states Sylvester's theorem (1892):

> If n ≥ 2k, then at least one of the numbers n, n - 1, ..., n - k + 1
> has a prime divisor p greater than k.

Equivalently, the binomial coefficient C(n,k) = n(n-1)...(n-k+1)/k!
always has a prime factor p > k when n ≥ 2k.

The central case n = 2k is precisely Bertrand's postulate (Chapter 2).

For the general case, the book notes (p. 13):

> In 1934, Erdős gave a short and elementary Book Proof of Sylvester's
> result, running along the lines of his proof of Bertrand's postulate.

The book does **not** reproduce this proof in full. It references:

> P. Erdős: A theorem of Sylvester and Schur,
> J. London Math. Soc. 9 (1934), 282-288.

The rest of Chapter 3 uses Sylvester's theorem as a lemma to prove the
"binomial coefficients are almost never powers" result.

## Formalization status

The central case (C(2k,k)) is fully proved below using Bertrand's postulate.

The general case (`sylvester_general`) currently takes `hsmooth` (that
n.descFactorial k is not (k+1)-smooth) as a premise. Eliminating this
premise requires a full formalization of Erdős's 1934 Sylvester-Schur
proof, which uses a refined analysis of how prime powers are distributed
among the k consecutive integers — more delicate than the Bertrand
chapter's global inequality bounding.

This is tracked in TODO.md as "Ch03: Sylvester smoothness core" —
difficulty: Medium-Hard, blocker: needs Erdős 1934 proof formalized.
-/

namespace ProofsInTheBook.Chapter03

open Nat





















































































theorem primeCounting_gap_9_120_cert :
    ∀ k : Fin 120, 9 ≤ k.val → 2 * Nat.primeCounting k.val < k.val := by
  intro k hk9
  by_cases hk19 : 19 ≤ k.val
  · exact primeCounting_gap_of_19_le hk19
  · have hklt19 : k.val < 19 := by omega
    interval_cases k.val <;> decide

theorem primeCounting_gap_of_9_le_lt_120 {k : ℕ} (hk9 : 9 ≤ k) (hk120 : k < 120) :
    2 * Nat.primeCounting k < k :=
  primeCounting_gap_9_120_cert ⟨k, hk120⟩ hk9

theorem primeCounting_gap_of_9_le {k : ℕ} (hk9 : 9 ≤ k) :
    2 * Nat.primeCounting k < k := by
  by_cases hk120 : k < 120
  · exact primeCounting_gap_of_9_le_lt_120 hk9 hk120
  · exact primeCounting_gap_of_120_le (by omega)































































































































theorem exists_large_prime_factor_choose_sq_le_of_9_le
    {n k : ℕ} (hk9 : 9 ≤ k) (hkn : k ≤ n) (hsq : k * k ≤ n) :
    HasPrimeFactorAbove k (n.choose k) :=
  exists_large_prime_factor_choose_of_sq_le_and_primeCounting_gap
    (by omega) hkn hsq (primeCounting_gap_of_9_le hk9)





theorem exists_large_prime_factor_choose_small_cert :
    ∀ k : Fin 9, ∀ n : Fin 94,
      0 < k.val → 2 * k.val ≤ n.val →
        ∃ p : Fin 94, k.val < p.val ∧ p.val.Prime ∧ p.val ∣ n.val.choose k.val := by
  set_option maxRecDepth 10000 in
  decide



theorem exists_large_prime_factor_choose_of_lt_9
    {n k : ℕ} (hkpos : 0 < k) (hk9 : k < 9) (hn2k : 2 * k ≤ n) :
    HasPrimeFactorAbove k (n.choose k) := by
  by_cases hn94 : n < 94
  · rcases exists_large_prime_factor_choose_small_cert ⟨k, hk9⟩ ⟨n, hn94⟩
      hkpos hn2k with ⟨p, hkp, hp, hpdvd⟩
    exact ⟨p.val, hkp, hp, hpdvd⟩
  · exact exists_large_prime_factor_choose_of_pow_gap (n := n) (k := k)
      hkpos (by omega) (by interval_cases k <;> decide)
      (pow_gap_small_k_tail hkpos hk9 (by omega))






































































































































theorem exists_large_prime_factor_choose_of_two_mul_le
    {n k : ℕ} (hkpos : 0 < k) (hn2k : 2 * k ≤ n) :
    HasPrimeFactorAbove k (n.choose k) := by
  by_cases hk9_lt : k < 9
  · exact exists_large_prime_factor_choose_of_lt_9 hkpos hk9_lt hn2k
  · have hk9 : 9 ≤ k := by omega
    by_cases hsq : k * k ≤ n
    · exact exists_large_prime_factor_choose_sq_le_of_9_le hk9 (by omega) hsq
    · have hbelow : n < k * k := by omega
      exact exists_large_prime_factor_choose_below_sq_of_9_le hk9 hn2k hbelow

/-!
### Central case of Sylvester's theorem

For the central binomial coefficient C(2k,k), we can give a clean proof
using Bertrand's postulate (Chapter 2):
- By Bertrand, ∃ prime p with k < p ≤ 2k.
- p divides (2k)! since p ≤ 2k.
- p does not divide k! since p > k.
- Since C(2k,k) · (k!)² = (2k)!, Euclid's lemma gives p | C(2k,k).
-/



/-!
### General Sylvester's theorem

For n ≥ 2k, the book extends the argument to C(n,k) by analyzing the
product n(n-1)···(n-k+1) = k! · C(n,k). For each of the k consecutive
integers n-j (0 ≤ j ≤ k-1), decompose n-j = q_j · r_j where q_j is
k-smooth and r_j has only prime factors > k. The q_j are bounded by
the prime factorization structure, forcing some r_j > 1.
-/

/--
The general Sylvester theorem: for n ≥ 2k and k ≥ 1, C(n,k) has a prime
divisor exceeding k. The proof reduces to showing the descending factorial
n(n-1)···(n-k+1) is not (k+1)-smooth; the existing infrastructure
(`exists_large_prime_dvd_choose_of_descFactorial_not_smooth`) then gives
the prime factor of C(n,k).
-/
theorem sylvester_general (n k : ℕ) (hn : 2 * k ≤ n) (hk : 0 < k) :
    ∃ p, k < p ∧ p.Prime ∧ p ∣ n.choose k :=
  exists_large_prime_factor_choose_of_two_mul_le hk hn









/-!
### Binomial coefficients are (almost) never powers

Erdős's theorem (1951): C(n,k) ≠ m^l for k ≥ 4, n ≥ 2k, l ≥ 2.
Reference: P. Erdős, On a diophantine equation,
J. London Math. Soc. 26 (1951), 176-178.

Below: Step 1 (concentration lemma + n > k²) is complete.
Steps 2–4 are pending (l-th-power-free decomposition, distinctness,
classification {aⱼ}={1,…,k}, and contradiction for l=2, l≥3).
-/

section Tier1

/-! ### Prime-divisibility helpers for Finset products -/





/-! ### Step 1: Concentration lemma → n > k² -/







/-! ### Step 2: l-th-power-free decomposition -/







/-! ### 2-power-free part: factorization mod 2 (Tier 2 building block for Ch03) -/





























































































/-! ### Interval count + Legendre / `padicValNat_factorial` helpers (Tier 2 building blocks for Ch03) -/



/-! ### Legendre / `padicValNat_factorial` helpers -/













/-! ### Erdős divisibility step (general l) -/



/-! ### Erdős divisibility step (l = 2 case): discharge of `hprod_l2` -/







/-! ### Main theorem assembly -/




end Tier1

end ProofsInTheBook.Chapter03

open ProofsInTheBook.Chapter03
open Nat

lemma solution {n k l m : ℕ} (hk : 4 ≤ k) (hn : 2 * k ≤ n)
    (hl : 2 ≤ l) (h_eq : n.choose k = m ^ l) : k ^ l < n := by
  have hk_pos : 0 < k := by omega
  have hk_le_n : k ≤ n := by omega
  obtain ⟨p, hkp, hp, hp_choose⟩ := sylvester_general n k hn hk_pos
  have hp_m : p ∣ m := hp.dvd_of_dvd_pow (h_eq ▸ hp_choose)
  have hp_l_dvd_choose : p ^ l ∣ n.choose k := by
    rw [h_eq]
    exact pow_dvd_pow_of_dvd hp_m l
  have hp_l_dvd_desc : p ^ l ∣ n.descFactorial k := by
    rw [Nat.descFactorial_eq_factorial_mul_choose n k]
    apply hp_l_dvd_choose.trans
    rw [mul_comm]
    exact dvd_mul_right _ _
  have hl_pos : 0 < l := by omega
  obtain ⟨i, hi, h_i_pow⟩ :=
    pow_l_dvd_one_factor_of_descFactorial hp hkp hl_pos hk_le_n hp_l_dvd_desc
  have h_n_minus_i_pos : 0 < n - i := Nat.sub_pos_of_lt (by omega)
  have h_ge : p ^ l ≤ n - i := Nat.le_of_dvd h_n_minus_i_pos h_i_pow
  have h_k_l_lt_p_l : k ^ l < p ^ l :=
    Nat.pow_lt_pow_left hkp (by omega : l ≠ 0)
  omega
