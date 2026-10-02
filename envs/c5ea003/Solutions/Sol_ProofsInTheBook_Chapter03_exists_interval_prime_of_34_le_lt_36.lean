-- Prove2me | solution 1 for ProofsInTheBook.Chapter03.exists_interval_prime_of_34_le_lt_36
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T16:36:44.976458+00:00
-- url     : https://prove2.me/submissions/7b7939f0-78a2-4fa2-87fe-7bda796358e9

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

























































































































































































































































































theorem exists_prime_within_of_primeGapCoverWith {gap limit prev m : ℕ} {ps : List ℕ}
    (hcover : PrimeGapCoverWith gap limit prev ps) (hprev : prev ≤ m) (hm : m < limit) :
    ∃ p, m < p ∧ p ≤ m + gap ∧ p.Prime := by
  induction ps generalizing prev with
  | nil => cases hcover
  | cons p ps ih =>
      dsimp [PrimeGapCoverWith] at hcover
      rcases hcover with ⟨hpprime, hp_le, htail⟩
      by_cases hmp : m < p
      · exact ⟨p, hmp, by omega, hpprime⟩
      · have hp_m : p ≤ m := by omega
        rcases htail with hlimitp | hcover_tail
        · omega
        · exact ih hcover_tail hp_m















































theorem primeGapSmall34Cover_cert : PrimeGapCoverWith 34 1122 34 primeGapSmall34Cover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall34Cover]


theorem primeGapSmall35Cover_cert : PrimeGapCoverWith 35 1190 35 primeGapSmall35Cover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall35Cover]































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

theorem solution
    {n k : ℕ} (hk34 : 34 ≤ k) (hk36 : k < 36) (hn2k : 2 * k ≤ n)
    (hnsq : n < k * k) :
    ∃ p, k < p ∧ n - k < p ∧ p ≤ n ∧ p.Prime := by
  interval_cases k
  ·
    have hmlo : 34 ≤ n - 34 := by omega
    have hmlimit : n - 34 < 1122 := by omega
    obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
      primeGapSmall34Cover_cert hmlo hmlimit
    exact ⟨p, by omega, hmp, by omega, hpprime⟩
  ·
    have hmlo : 35 ≤ n - 35 := by omega
    have hmlimit : n - 35 < 1190 := by omega
    obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
      primeGapSmall35Cover_cert hmlo hmlimit
    exact ⟨p, by omega, hmp, by omega, hpprime⟩
