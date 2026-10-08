-- Prove2me | solution 1 for ProofsInTheBook.Chapter03.pow_l_dvd_one_factor_of_descFactorial
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T16:36:30.857481+00:00
-- url     : https://prove2.me/submissions/10562a6e-685b-49c0-94f5-cc96ab67e4c0

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

lemma nat_prime_dvd_finset_prod {p : ℕ} {α : Type _} [DecidableEq α] {s : Finset α}
    {f : α → ℕ} (hp : p.Prime) (h : p ∣ ∏ x ∈ s, f x) : ∃ x ∈ s, p ∣ f x := by
  induction' s using Finset.induction_on with a s' has ih
  · have : p ∣ 1 := by simpa using h
    have hp1 : ¬ p ∣ 1 := by
      intro h1; have := Nat.le_of_dvd (by norm_num) h1; have hpgt1 := hp.one_lt; omega
    exact absurd this hp1
  · rw [Finset.prod_insert has] at h
    rcases hp.dvd_or_dvd h with (hpa | hps')
    · exact ⟨a, Finset.mem_insert_self a s', hpa⟩
    · rcases ih hps' with ⟨x, hx, hpx⟩
      exact ⟨x, Finset.mem_insert_of_mem hx, hpx⟩

lemma nat_prime_not_dvd_finset_prod {p : ℕ} {α : Type _} [DecidableEq α] {s : Finset α}
    {f : α → ℕ} (hp : p.Prime) (h : ∀ x ∈ s, ¬ p ∣ f x) : ¬ p ∣ ∏ x ∈ s, f x := by
  intro hprod; rcases nat_prime_dvd_finset_prod hp hprod with ⟨x, hx, hpx⟩; exact h x hx hpx

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

lemma solution {n k l p : ℕ} (hp : p.Prime) (hkp : k < p)
    (hlp : 0 < l) (hk_le_n : k ≤ n) (hp_l_dvd : p ^ l ∣ n.descFactorial k) :
    ∃ i, i < k ∧ p ^ l ∣ n - i := by
  induction k generalizing n with
  | zero =>
      -- k = 0: n.descFactorial 0 = 1, p^l ∣ 1 impossible
      have hp_gt_1 : 1 < p ^ l := by
        calc
          1 = 1 ^ l := by simp
          _ < p ^ l := Nat.pow_lt_pow_left hp.one_lt hlp.ne.symm
      have h1 : p ^ l ∣ 1 := hp_l_dvd
      have hle_p : p ^ l ≤ 1 := Nat.le_of_dvd (by norm_num) h1
      omega
  | succ k ih =>
      -- k → k+1: n.descFactorial (k+1) = (n−k) * n.descFactorial k
      -- In this branch: hkp : k+1 < p, hk_le_n : k+1 ≤ n
      rw [Nat.descFactorial_succ] at hp_l_dvd
      by_cases hdiv_nk : p ∣ n - k
      · -- Case 1: p ∣ n−k. Show ∀ j < k, p ∤ n−j.
        have h_no_other : ∀ j, j < k → ¬ p ∣ n - j := by
          intro j hj
          by_contra! h
          have h_eq : n - j = (n - k) + (k - j) := by
            have : k ≤ n := by omega
            omega
          have h_dvd_sum : p ∣ (n - k) + (k - j) := by rwa [← h_eq]
          have hsub : p ∣ k - j := (Nat.dvd_add_right hdiv_nk).mp h_dvd_sum
          have hpos : 0 < k - j := Nat.sub_pos_of_lt hj
          have h_lt : k - j < p := by omega
          have hle_p : p ≤ k - j := Nat.le_of_dvd hpos hsub
          omega
        have h_not_dvd_desc : ¬ p ∣ n.descFactorial k := by
          rw [Nat.descFactorial_eq_prod_range]
          apply nat_prime_not_dvd_finset_prod hp
          intro x hx; exact h_no_other x (Finset.mem_range.mp hx)
        have h_cop_base : Nat.Coprime p (n.descFactorial k) :=
          hp.coprime_iff_not_dvd.mpr h_not_dvd_desc
        have h_cop : Nat.Coprime (p ^ l) (n.descFactorial k) := by
          rw [Nat.coprime_pow_left_iff hlp]; exact h_cop_base
        exact ⟨k, by omega, h_cop.dvd_of_dvd_mul_right hp_l_dvd⟩
      · -- Case 2: p ∤ n−k. Coprime, push through to n.descFactorial k, apply IH.
        have h_cop_nk : Nat.Coprime p (n - k) := hp.coprime_iff_not_dvd.mpr hdiv_nk
        have h_cop_nk_pow : Nat.Coprime (p ^ l) (n - k) := by
          rw [Nat.coprime_pow_left_iff hlp]; exact h_cop_nk
        rw [mul_comm] at hp_l_dvd
        have h_dvd_desc : p ^ l ∣ n.descFactorial k :=
          h_cop_nk_pow.dvd_of_dvd_mul_right hp_l_dvd
        -- ih: (k < p) → (k ≤ n) → (p^l ∣ n.descFactorial k) → ∃ i < k, p^l ∣ n - i
        rcases ih (by omega) (by omega) h_dvd_desc with ⟨i, hi, h_i_pow⟩
        exact ⟨i, by omega, h_i_pow⟩
