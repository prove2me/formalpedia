-- Prove2me | solution 1 for ProofsInTheBook.Chapter03.three_mul_primeCounting_le_of_33_le
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T16:37:01.874396+00:00
-- url     : https://prove2.me/submissions/703a2cd4-a082-4f8b-b500-fb5556ad0a15

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



























































































theorem three_mul_primeCounting_le_30_150_cert :
    ∀ k : Fin 150, 33 ≤ k.val → 3 * Nat.primeCounting k.val ≤ k.val := by
  intro k hk33
  rcases le_or_gt k.val 36 with hk36 | hk37
  · have hpi : Nat.primeCounting k.val ≤ 11 := by
      have hmono := Nat.monotone_primeCounting hk36
      have h36 : Nat.primeCounting 36 = 11 := by decide
      exact hmono.trans_eq h36
    omega
  rcases le_or_gt k.val 40 with hk40 | hk41
  · have hpi : Nat.primeCounting k.val ≤ 12 := by
      have hmono := Nat.monotone_primeCounting hk40
      have h40 : Nat.primeCounting 40 = 12 := by decide
      exact hmono.trans_eq h40
    omega
  rcases le_or_gt k.val 42 with hk42 | hk43
  · have hpi : Nat.primeCounting k.val ≤ 13 := by
      have hmono := Nat.monotone_primeCounting hk42
      have h42 : Nat.primeCounting 42 = 13 := by decide
      exact hmono.trans_eq h42
    omega
  rcases le_or_gt k.val 46 with hk46 | hk47
  · have hpi : Nat.primeCounting k.val ≤ 14 := by
      have hmono := Nat.monotone_primeCounting hk46
      have h46 : Nat.primeCounting 46 = 14 := by decide
      exact hmono.trans_eq h46
    omega
  rcases le_or_gt k.val 52 with hk52 | hk53
  · have hpi : Nat.primeCounting k.val ≤ 15 := by
      have hmono := Nat.monotone_primeCounting hk52
      have h52 : Nat.primeCounting 52 = 15 := by decide
      exact hmono.trans_eq h52
    omega
  rcases le_or_gt k.val 60 with hk60 | hk61
  · have hpi : Nat.primeCounting k.val ≤ 17 := by
      have hmono := Nat.monotone_primeCounting hk60
      have h60 : Nat.primeCounting 60 = 17 := by decide
      exact hmono.trans_eq h60
    omega
  rcases le_or_gt k.val 72 with hk72 | hk73
  · have hpi : Nat.primeCounting k.val ≤ 20 := by
      have hmono := Nat.monotone_primeCounting hk72
      have h72 : Nat.primeCounting 72 = 20 := by decide
      exact hmono.trans_eq h72
    omega
  rcases le_or_gt k.val 96 with hk96 | hk97
  · have hpi : Nat.primeCounting k.val ≤ 24 := by
      have hmono := Nat.monotone_primeCounting hk96
      have h96 : Nat.primeCounting 96 = 24 := by
        set_option maxRecDepth 10000 in
        decide
      exact hmono.trans_eq h96
    omega
  rcases le_or_gt k.val 136 with hk136 | hk137
  · have hpi : Nat.primeCounting k.val ≤ 32 := by
      have hmono := Nat.monotone_primeCounting hk136
      have h136 : Nat.primeCounting 136 = 32 := by
        set_option maxRecDepth 10000 in
        decide
      exact hmono.trans_eq h136
    omega
  · have hpi : Nat.primeCounting k.val ≤ 35 := by
      have hmono := Nat.monotone_primeCounting k.isLt.le
      have h149 : Nat.primeCounting 149 = 35 := by
        set_option maxRecDepth 10000 in
        decide
      set_option maxRecDepth 10000 in
      exact hmono.trans_eq h149
    omega
















































































































































































































































































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

theorem solution {k : ℕ} (hk33 : 33 ≤ k) :
    3 * Nat.primeCounting k ≤ k := by
  by_cases hk150 : k < 150
  · exact three_mul_primeCounting_le_30_150_cert ⟨k, hk150⟩ hk33
  · let m := k - 30
    have hk_eq : k = 30 + m := by omega
    have hbound0 := Nat.primeCounting_add_le
      (a := 30) (k := 30) (n := m) (by norm_num) (by norm_num : 30 ≤ 30)
    have hbound : Nat.primeCounting k ≤ Nat.primeCounting 30 + Nat.totient 30 * (m / 30 + 1) := by
      simpa [hk_eq] using hbound0
    have hcalc : Nat.primeCounting 30 = 10 := by decide
    have htot : Nat.totient 30 = 8 := by decide
    have hbound2 : Nat.primeCounting k ≤ 10 + 8 * (m / 30 + 1) := by
      simpa [hcalc, htot] using hbound
    have hm120 : 120 ≤ m := by omega
    have hq4 : 4 ≤ m / 30 := by
      exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 30)).mpr hm120
    have hmul : 30 * (m / 30) ≤ m := Nat.mul_div_le m 30
    omega
