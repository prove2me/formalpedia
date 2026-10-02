-- Prove2me | solution 1 for ProofsInTheBook.Chapter03.exists_large_prime_factor_choose_below_sq_of_sqrt_lt_33
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T16:36:53.591074+00:00
-- url     : https://prove2.me/submissions/17dafe9b-7f18-45e4-9ca8-559c446df0b6

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











































































































































































































































/--
Factorial form of the standard binomial-divisibility argument: if a prime
divides `n!` but not the two factorial factors in
`C(n,k) * k! * (n-k)! = n!`, then it divides `C(n,k)`.
-/
theorem prime_dvd_choose_of_dvd_factorial_not_factorial_sides {n k p : ℕ}
    (hkn : k ≤ n) (hp : p.Prime) (hdvd : p ∣ n !)
    (hk : ¬ p ∣ k !) (hnk : ¬ p ∣ (n - k) !) : p ∣ n.choose k := by
  have h_eq : n.choose k * k ! * (n - k) ! = n ! :=
    choose_mul_factorial_mul_factorial hkn
  rw [← h_eq] at hdvd
  have hleft : p ∣ n.choose k * k ! := (hp.dvd_mul.mp hdvd).resolve_right hnk
  exact (hp.dvd_mul.mp hleft).resolve_right hk

theorem prime_not_dvd_factorial_of_lt {p k : ℕ} (hp : p.Prime) (hk : k < p) :
    ¬ p ∣ k ! := by
  rwa [hp.dvd_factorial, not_le]





























/--
If a prime divisor of `n!` is larger than both factorial factors
`k!` and `(n-k)!`, then it must appear in the binomial coefficient.
This is the form used by the central Bertrand-prime argument, and it is
also the local step needed in the general Sylvester proof.
-/
theorem prime_dvd_choose_of_interval_prime {n k p : ℕ} (hkn : k ≤ n)
    (hp : p.Prime) (hk : k < p) (hnk : n - k < p) (hpn : p ≤ n) :
    p ∣ n.choose k :=
  prime_dvd_choose_of_dvd_factorial_not_factorial_sides hkn hp
    (hp.dvd_factorial.mpr hpn)
    (prime_not_dvd_factorial_of_lt hp hk)
    (prime_not_dvd_factorial_of_lt hp hnk)

theorem hasPrimeFactorAbove_choose_of_interval_prime {n k p : ℕ} (hkn : k ≤ n)
    (hp : p.Prime) (hk : k < p) (hnk : n - k < p) (hpn : p ≤ n) :
    HasPrimeFactorAbove k (n.choose k) :=
  ⟨p, hk, hp, prime_dvd_choose_of_interval_prime hkn hp hk hnk hpn⟩

theorem exists_large_prime_factor_choose_125_12 :
    HasPrimeFactorAbove 12 ((125).choose 12) := by
  refine ⟨13, by norm_num, by norm_num, ?_⟩
  set_option maxRecDepth 10000 in
  decide

theorem exists_large_prime_factor_choose_126_12 :
    HasPrimeFactorAbove 12 ((126).choose 12) := by
  refine ⟨13, by norm_num, by norm_num, ?_⟩
  set_option maxRecDepth 10000 in
  decide

theorem exists_large_prime_factor_choose_126_13 :
    HasPrimeFactorAbove 13 ((126).choose 13) := by
  refine ⟨17, by norm_num, by norm_num, ?_⟩
  set_option maxRecDepth 10000 in
  decide





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



theorem primeGap20Cover_cert : PrimeGapCoverWith 20 1089 0 primeGap20Cover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGap20Cover]

theorem exists_prime_within_20_of_lt_1089 {m : ℕ} (hm : m < 1089) :
    ∃ p, m < p ∧ p ≤ m + 20 ∧ p.Prime :=
  exists_prime_within_of_primeGapCoverWith primeGap20Cover_cert (by omega) hm


theorem primeGapSmall9Cover_cert : PrimeGapCoverWith 9 72 9 primeGapSmall9Cover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall9Cover]


theorem primeGapSmall10Cover_cert : PrimeGapCoverWith 10 90 10 primeGapSmall10Cover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall10Cover]


theorem primeGapSmall11Cover_cert : PrimeGapCoverWith 11 110 11 primeGapSmall11Cover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall11Cover]


theorem primeGapSmall12_lowCover_cert : PrimeGapCoverWith 12 113 12 primeGapSmall12_lowCover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall12_lowCover]


theorem primeGapSmall12_highCover_cert : PrimeGapCoverWith 12 132 115 primeGapSmall12_highCover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall12_highCover]


theorem primeGapSmall13_lowCover_cert : PrimeGapCoverWith 13 113 13 primeGapSmall13_lowCover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall13_lowCover]


theorem primeGapSmall13_highCover_cert : PrimeGapCoverWith 13 156 114 primeGapSmall13_highCover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall13_highCover]


theorem primeGapSmall14Cover_cert : PrimeGapCoverWith 14 182 14 primeGapSmall14Cover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall14Cover]


theorem primeGapSmall15Cover_cert : PrimeGapCoverWith 15 210 15 primeGapSmall15Cover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall15Cover]


theorem primeGapSmall16Cover_cert : PrimeGapCoverWith 16 240 16 primeGapSmall16Cover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall16Cover]


theorem primeGapSmall17Cover_cert : PrimeGapCoverWith 17 272 17 primeGapSmall17Cover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall17Cover]


theorem primeGapSmall18Cover_cert : PrimeGapCoverWith 18 306 18 primeGapSmall18Cover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall18Cover]


theorem primeGapSmall19Cover_cert : PrimeGapCoverWith 19 342 19 primeGapSmall19Cover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall19Cover]







theorem exists_interval_prime_or_exception_of_9_le_lt_20
    {n k : ℕ} (hk9 : 9 ≤ k) (hk20 : k < 20) (hn2k : 2 * k ≤ n)
    (hnsq : n < k * k) :
    (∃ p, k < p ∧ n - k < p ∧ p ≤ n ∧ p.Prime)
      ∨ (n = 125 ∧ k = 12)
      ∨ (n = 126 ∧ k = 12)
      ∨ (n = 126 ∧ k = 13) := by
  interval_cases k
  ·
    have hmlo : 9 ≤ n - 9 := by omega
    have hmlimit : n - 9 < 72 := by omega
    obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
      primeGapSmall9Cover_cert hmlo hmlimit
    left
    exact ⟨p, by omega, hmp, by omega, hpprime⟩
  ·
    have hmlo : 10 ≤ n - 10 := by omega
    have hmlimit : n - 10 < 90 := by omega
    obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
      primeGapSmall10Cover_cert hmlo hmlimit
    left
    exact ⟨p, by omega, hmp, by omega, hpprime⟩
  ·
    have hmlo : 11 ≤ n - 11 := by omega
    have hmlimit : n - 11 < 110 := by omega
    obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
      primeGapSmall11Cover_cert hmlo hmlimit
    left
    exact ⟨p, by omega, hmp, by omega, hpprime⟩
  ·
    have hmlo : 12 ≤ n - 12 := by omega
    by_cases hm113 : n - 12 = 113
    · exact Or.inr (Or.inl ⟨by omega, rfl⟩)
    by_cases hm114 : n - 12 = 114
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, rfl⟩))
    by_cases hlow : n - 12 < 113
    · obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
        primeGapSmall12_lowCover_cert hmlo hlow
      left
      exact ⟨p, by omega, hmp, by omega, hpprime⟩
    · have hmhigh : 115 ≤ n - 12 := by omega
      have hmlimit : n - 12 < 132 := by omega
      obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
        primeGapSmall12_highCover_cert hmhigh hmlimit
      left
      exact ⟨p, by omega, hmp, by omega, hpprime⟩
  ·
    have hmlo : 13 ≤ n - 13 := by omega
    by_cases hm113 : n - 13 = 113
    · exact Or.inr (Or.inr (Or.inr ⟨by omega, rfl⟩))
    by_cases hlow : n - 13 < 113
    · obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
        primeGapSmall13_lowCover_cert hmlo hlow
      left
      exact ⟨p, by omega, hmp, by omega, hpprime⟩
    · have hmhigh : 114 ≤ n - 13 := by omega
      have hmlimit : n - 13 < 156 := by omega
      obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
        primeGapSmall13_highCover_cert hmhigh hmlimit
      left
      exact ⟨p, by omega, hmp, by omega, hpprime⟩
  ·
    have hmlo : 14 ≤ n - 14 := by omega
    have hmlimit : n - 14 < 182 := by omega
    obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
      primeGapSmall14Cover_cert hmlo hmlimit
    left
    exact ⟨p, by omega, hmp, by omega, hpprime⟩
  ·
    have hmlo : 15 ≤ n - 15 := by omega
    have hmlimit : n - 15 < 210 := by omega
    obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
      primeGapSmall15Cover_cert hmlo hmlimit
    left
    exact ⟨p, by omega, hmp, by omega, hpprime⟩
  ·
    have hmlo : 16 ≤ n - 16 := by omega
    have hmlimit : n - 16 < 240 := by omega
    obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
      primeGapSmall16Cover_cert hmlo hmlimit
    left
    exact ⟨p, by omega, hmp, by omega, hpprime⟩
  ·
    have hmlo : 17 ≤ n - 17 := by omega
    have hmlimit : n - 17 < 272 := by omega
    obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
      primeGapSmall17Cover_cert hmlo hmlimit
    left
    exact ⟨p, by omega, hmp, by omega, hpprime⟩
  ·
    have hmlo : 18 ≤ n - 18 := by omega
    have hmlimit : n - 18 < 306 := by omega
    obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
      primeGapSmall18Cover_cert hmlo hmlimit
    left
    exact ⟨p, by omega, hmp, by omega, hpprime⟩
  ·
    have hmlo : 19 ≤ n - 19 := by omega
    have hmlimit : n - 19 < 342 := by omega
    obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
      primeGapSmall19Cover_cert hmlo hmlimit
    left
    exact ⟨p, by omega, hmp, by omega, hpprime⟩



theorem nextPrimeAfter1089_below_sq_sqrt_lt_33_cert :
    ∀ k : Fin 545, ∀ n : Fin 1089,
      9 ≤ k.val → 2 * k.val ≤ n.val → n.val < k.val * k.val →
        (∃ p, k.val < p ∧ n.val - k.val < p ∧ p ≤ n.val ∧ p.Prime)
        ∨ (n.val = 125 ∧ k.val = 12)
        ∨ (n.val = 126 ∧ k.val = 12)
        ∨ (n.val = 126 ∧ k.val = 13) := by
  intro k n hk9 hn2k hnsq
  by_cases hk20 : 20 ≤ k.val
  · have hm_lt : n.val - k.val < 1089 := by omega
    obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_20_of_lt_1089 hm_lt
    left
    exact ⟨p, by omega, hmp, by omega, hpprime⟩
  · have hklt20 : k.val < 20 := by omega
    exact exists_interval_prime_or_exception_of_9_le_lt_20 hk9 hklt20 hn2k hnsq

























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
    {n k : ℕ} (hk9 : 9 ≤ k) (hn2k : 2 * k ≤ n)
    (hnsq : n < k * k) (hsqrt33 : sqrt n < 33) :
    HasPrimeFactorAbove k (n.choose k) := by
  have hn1089 : n < 1089 := by
    rw [Nat.sqrt_lt] at hsqrt33
    simpa using hsqrt33
  have hk545 : k < 545 := by nlinarith
  rcases nextPrimeAfter1089_below_sq_sqrt_lt_33_cert
      ⟨k, hk545⟩ ⟨n, hn1089⟩ hk9 hn2k hnsq with
    (⟨p, hkp, hnkp, hpn, hp⟩ | ⟨hn, hk⟩ | ⟨hn, hk⟩ | ⟨hn, hk⟩)
  · exact hasPrimeFactorAbove_choose_of_interval_prime (by omega : k ≤ n) hp hkp hnkp hpn
  · have hn' : n = 125 := by simpa using hn
    have hk' : k = 12 := by simpa using hk
    subst n
    subst k
    exact exists_large_prime_factor_choose_125_12
  · have hn' : n = 126 := by simpa using hn
    have hk' : k = 12 := by simpa using hk
    subst n
    subst k
    exact exists_large_prime_factor_choose_126_12
  · have hn' : n = 126 := by simpa using hn
    have hk' : k = 13 := by simpa using hk
    subst n
    subst k
    exact exists_large_prime_factor_choose_126_13
