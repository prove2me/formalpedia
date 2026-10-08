-- Prove2me | solution 1 for ProofsInTheBook.Chapter03.choose_le_pow_primeCounting_of_noLargePrimeFactor
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T16:26:33.208515+00:00
-- url     : https://prove2.me/submissions/1b52d19a-ddff-47b3-bef7-a86486632aba

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



























theorem factorization_choose_eq_zero_of_noLargePrimeFactor
    {n k p : ℕ} (hno : NoLargePrimeFactor k (n.choose k)) (hkp : k < p) :
    (n.choose k).factorization p = 0 := by
  by_cases hp : p.Prime
  · by_contra hne
    have hpdvd : p ∣ n.choose k := Nat.dvd_of_factorization_pos hne
    exact (not_lt_of_ge (hno p hp hpdvd)) hkp
  · exact Nat.factorization_eq_zero_of_not_prime (n.choose k) hp

theorem Finset.prod_le_pow_card_of_le {α : Type*} (s : Finset α) (f : α → ℕ) (N : ℕ)
    (h : ∀ a ∈ s, f a ≤ N) : (∏ a ∈ s, f a) ≤ N ^ s.card := by
  classical
  calc
    (∏ a ∈ s, f a) ≤ ∏ _a ∈ s, N := Finset.prod_le_prod' h
    _ = N ^ s.card := by rw [Finset.prod_const]














































































































































































































































































































































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
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k)) :
    n.choose k ≤ n ^ Nat.primeCounting k := by
  classical
  let s := (Finset.range (n + 1)).filter (fun p => p ∈ Nat.primesLE k)
  have hprod_filter :
      (∏ p ∈ Finset.range (n + 1), p ^ (n.choose k).factorization p)
        = ∏ p ∈ s, p ^ (n.choose k).factorization p := by
    symm
    refine Finset.prod_subset (Finset.filter_subset _ _) ?_
    intro p hp_range hp_not_s
    have hp_not_primes : p ∉ Nat.primesLE k := by
      intro hp_primes
      exact hp_not_s (Finset.mem_filter.mpr ⟨hp_range, hp_primes⟩)
    have hfac : (n.choose k).factorization p = 0 := by
      by_cases hpprime : p.Prime
      · have hkp : k < p := by
          by_contra hnot
          exact hp_not_primes (Nat.mem_primesLE.mpr ⟨le_of_not_gt hnot, hpprime⟩)
        exact factorization_choose_eq_zero_of_noLargePrimeFactor hno hkp
      · exact Nat.factorization_eq_zero_of_not_prime (n.choose k) hpprime
    simp [hfac]
  have hprod_le : (∏ p ∈ s, p ^ (n.choose k).factorization p) ≤ n ^ s.card :=
    Finset.prod_le_pow_card_of_le s (fun p => p ^ (n.choose k).factorization p) n
      (fun p _ => Nat.pow_factorization_choose_le hnpos)
  have hcard : s.card ≤ (Nat.primesLE k).card := by
    refine Finset.card_le_card ?_
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hpow_card : n ^ s.card ≤ n ^ Nat.primeCounting k := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact Nat.pow_le_pow_right hnpos hcard
  calc
    n.choose k = ∏ p ∈ Finset.range (n + 1), p ^ (n.choose k).factorization p := by
      exact (Nat.prod_pow_factorization_choose n k hkn).symm
    _ = ∏ p ∈ s, p ^ (n.choose k).factorization p := hprod_filter
    _ ≤ n ^ s.card := hprod_le
    _ ≤ n ^ Nat.primeCounting k := hpow_card
