-- Prove2me | solution 1 for ProofsInTheBook.Chapter03.mul_log_sub_mul_log_le_log_choose
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T16:36:25.719513+00:00
-- url     : https://prove2.me/submissions/2b9311f6-6c7e-4214-85ef-2b318ae0fadd

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03


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









































theorem pow_mul_self_descFactorial_le_pow_mul_descFactorial {n k : ℕ} (hkn : k ≤ n) :
    n ^ k * k.descFactorial k ≤ k ^ k * n.descFactorial k := by
  have hnprod : n ^ k = ∏ _i ∈ Finset.range k, n := by
    rw [Finset.prod_const, Finset.card_range]
  have hkprod : k ^ k = ∏ _i ∈ Finset.range k, k := by
    rw [Finset.prod_const, Finset.card_range]
  rw [Nat.descFactorial_eq_prod_range k, Nat.descFactorial_eq_prod_range n,
    hnprod, hkprod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod' fun i hi => by
    rw [Finset.mem_range] at hi
    have hik : i ≤ k := le_of_lt hi
    have hki : k * i ≤ n * i := Nat.mul_le_mul_right i hkn
    rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib, Nat.mul_comm k n]
    exact Nat.sub_le_sub_left hki (n * k)

theorem pow_le_pow_mul_choose {n k : ℕ} (hkn : k ≤ n) :
    n ^ k ≤ k ^ k * n.choose k := by
  have h :=
    pow_mul_self_descFactorial_le_pow_mul_descFactorial (n := n) (k := k) hkn
  rw [Nat.descFactorial_self, Nat.descFactorial_eq_factorial_mul_choose] at h
  have hcancel : k ! * n ^ k ≤ k ! * (k ^ k * n.choose k) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  exact le_of_mul_le_mul_left hcancel (Nat.factorial_pos k)
































































































































































































































































































































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

open Nat
open ProofsInTheBook.Chapter03

theorem solution {n k : ℕ}
    (hkpos : 0 < k) (hkn : k ≤ n) :
    (k : ℝ) * Real.log n - (k : ℝ) * Real.log k ≤ Real.log (n.choose k) := by
  have hnpos : 0 < n := hkpos.trans_le hkn
  have hchoose_pos : 0 < n.choose k := Nat.choose_pos hkn
  have hnat : n ^ k ≤ k ^ k * n.choose k := pow_le_pow_mul_choose hkn
  have hlog :
      Real.log ((n : ℝ) ^ k) ≤ Real.log ((k : ℝ) ^ k * (n.choose k : ℝ)) := by
    exact Real.log_le_log
      (pow_pos (by exact_mod_cast hnpos) k)
      (by exact_mod_cast hnat)
  calc
    (k : ℝ) * Real.log n - (k : ℝ) * Real.log k
        = Real.log ((n : ℝ) ^ k) - Real.log ((k : ℝ) ^ k) := by
          rw [Real.log_pow, Real.log_pow]
    _ ≤ Real.log ((k : ℝ) ^ k * (n.choose k : ℝ)) - Real.log ((k : ℝ) ^ k) := by
      exact sub_le_sub_right hlog _
    _ = Real.log (n.choose k) := by
      rw [Real.log_mul
        (pow_ne_zero _ (by exact_mod_cast hkpos.ne' : (k : ℝ) ≠ 0))
        (by exact_mod_cast hchoose_pos.ne')]
      ring
