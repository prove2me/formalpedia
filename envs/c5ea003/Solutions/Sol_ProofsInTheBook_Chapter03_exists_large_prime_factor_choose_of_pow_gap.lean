-- Prove2me | solution 1 for ProofsInTheBook.Chapter03.exists_large_prime_factor_choose_of_pow_gap
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T16:36:55.108727+00:00
-- url     : https://prove2.me/submissions/04bf3e3b-f951-4612-8295-adcdf36a73e9

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

























theorem not_hasPrimeFactorAbove_iff_noLargePrimeFactor {k m : ℕ} :
    ¬ HasPrimeFactorAbove k m ↔ NoLargePrimeFactor k m := by
  constructor
  · intro h p hp hpdvd
    by_contra hkp
    exact h ⟨p, by omega, hp, hpdvd⟩
  · rintro h ⟨p, hkp, hp, hpdvd⟩
    exact (not_lt_of_ge (h p hp hpdvd)) hkp

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

theorem choose_le_pow_primeCounting_of_noLargePrimeFactor
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











theorem mul_log_sub_mul_log_le_log_choose {n k : ℕ}
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









theorem log_choose_le_primeCounting_log_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k)) :
    Real.log (n.choose k) ≤ (Nat.primeCounting k : ℝ) * Real.log n := by
  have hnat : n.choose k ≤ n ^ Nat.primeCounting k :=
    choose_le_pow_primeCounting_of_noLargePrimeFactor hnpos hkn hno
  have hchoose_pos : 0 < n.choose k := Nat.choose_pos hkn
  calc
    Real.log (n.choose k) ≤ Real.log (n ^ Nat.primeCounting k) := by
      exact Real.log_le_log (by exact_mod_cast hchoose_pos) (by exact_mod_cast hnat)
    _ = (Nat.primeCounting k : ℝ) * Real.log n := by
      rw [show Real.log (n ^ Nat.primeCounting k) =
        Real.log ((n : ℝ) ^ Nat.primeCounting k) by norm_num [Nat.cast_pow],
        Real.log_pow]

theorem exists_large_prime_factor_choose_of_primeCounting_log_gap
    {n k : ℕ} (hkpos : 0 < k) (hnpos : 0 < n) (hkn : k ≤ n)
    (hgap :
      (Nat.primeCounting k : ℝ) * Real.log n <
        (k : ℝ) * Real.log n - (k : ℝ) * Real.log k) :
    HasPrimeFactorAbove k (n.choose k) := by
  by_contra hlarge
  have hno : NoLargePrimeFactor k (n.choose k) :=
    not_hasPrimeFactorAbove_iff_noLargePrimeFactor.mp hlarge
  have hlower := mul_log_sub_mul_log_le_log_choose (n := n) (k := k) hkpos hkn
  have hupper :=
    log_choose_le_primeCounting_log_of_noLargePrimeFactor
      (n := n) (k := k) hnpos hkn hno
  exact not_lt_of_ge (hlower.trans hupper) hgap








































































































































































































































































































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
    {n k : ℕ} (hkpos : 0 < k) (hkn : k ≤ n)
    (hpi : Nat.primeCounting k ≤ k)
    (hpow : k ^ k < n ^ (k - Nat.primeCounting k)) :
    HasPrimeFactorAbove k (n.choose k) := by
  have hnpos : 0 < n := hkpos.trans_le hkn
  refine exists_large_prime_factor_choose_of_primeCounting_log_gap
    (n := n) (k := k) hkpos hnpos hkn ?_
  have hkpow_pos : 0 < (k : ℝ) ^ k := pow_pos (by exact_mod_cast hkpos) k
  have hlogpow :
      (k : ℝ) * Real.log k <
        (k - Nat.primeCounting k : ℕ) * Real.log n := by
    have hlog : Real.log ((k : ℝ) ^ k) <
        Real.log ((n : ℝ) ^ (k - Nat.primeCounting k)) := by
      exact Real.log_lt_log hkpow_pos (by exact_mod_cast hpow)
    simpa [Real.log_pow] using hlog
  have hk_split :
      (k : ℝ) = (Nat.primeCounting k : ℝ) + (k - Nat.primeCounting k : ℕ) := by
    exact_mod_cast (Nat.add_sub_of_le hpi).symm
  calc
    (Nat.primeCounting k : ℝ) * Real.log n
        < (Nat.primeCounting k : ℝ) * Real.log n
            + (k - Nat.primeCounting k : ℕ) * Real.log n - (k : ℝ) * Real.log k := by
          linarith
    _ = ((Nat.primeCounting k : ℝ) + (k - Nat.primeCounting k : ℕ)) * Real.log n
            - (k : ℝ) * Real.log k := by
          ring
    _ = (k : ℝ) * Real.log n - (k : ℝ) * Real.log k := by
          rw [← hk_split]
