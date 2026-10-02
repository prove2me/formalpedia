-- Prove2me | solution 1 for ProofsInTheBook.Chapter02.chapter02_bertrand
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T16:52:46.955096+00:00
-- url     : https://prove2.me/submissions/62866dc0-cea9-4fb9-bea4-a2d956697b24

import Mathlib


/-!
# Chapter 2: Bertrand's Postulate

Following Erdős's proof from "Proofs from THE BOOK."

**Theorem.** For every n ≥ 1, there is a prime p with n < p ≤ 2n.

The proof has four main ingredients:
1. **Chebyshev's bound**: ∏(p ≤ n) p ≤ 4^n, proved by strong induction.
2. **Lower bound on C(2n,n)**: 4^n < n · C(2n,n) for n ≥ 4.
3. **Factorization analysis**: each prime power in C(2n,n) is ≤ 2n, and
   primes p with 2n/3 < p ≤ n don't divide C(2n,n) at all.
4. **Contradiction**: combining the bounds shows Bertrand must hold for
   large n; small cases are checked directly.
-/

namespace ProofsInTheBook.Chapter02

open Nat Finset

/-!
### Part 1: Chebyshev's bound on the primorial

*Book proof.* By strong induction on n.
- If n is even and > 2: n is composite, so ∏(p ≤ n) = ∏(p ≤ n-1) ≤ 4^{n-1} ≤ 4^n.
- If n = 2m+1 is odd: every prime p with m+1 < p ≤ 2m+1 divides C(2m+1, m),
  because p appears in (2m+1)! but not in m!(m+1)!. Their product divides
  C(2m+1, m) ≤ 4^m. By induction, ∏(p ≤ m+1) ≤ 4^{m+1}.
  Total: ≤ 4^{m+1} · 4^m = 4^{2m+1}.
-/



/-!
### Part 2: Lower bound on the central binomial coefficient

From (1+1)^{2n} = ∑ C(2n,k) and C(2n,n) being the largest among 2n+1 terms,
the book gets C(2n,n) ≥ 4^n/(2n+1). The tighter bound 4^n < n·C(2n,n) for n ≥ 4
follows from the recurrence (n+1)·C(2(n+1),n+1) = 2(2n+1)·C(2n,n).
-/

theorem chapter02_central_binom_lower (n : ℕ) (hn : 4 ≤ n) :
    4 ^ n < n * n.centralBinom :=
  four_pow_lt_mul_centralBinom n hn

/-!
### Part 3: Prime factorization analysis of C(2n,n)

Two key observations from the book:

1. **Prime power bound**: by Legendre's formula,
   v_p(C(2n,n)) = ∑_i (⌊2n/p^i⌋ - 2⌊n/p^i⌋), each term 0 or 1,
   so p^{v_p} ≤ p^{log_p(2n)} ≤ 2n.

2. **Medium primes vanish**: if 2n/3 < p ≤ n, then p² > 2n
   so v_p ≤ 1, and the single term is ⌊2n/p⌋ - 2⌊n/p⌋ = 2 - 2 = 0.
-/





/-!
### Part 4: Upper bound on C(2n,n) when Bertrand fails

If no prime exists in (n, 2n], split the prime factorization of C(2n,n) into:
1. **p ≤ √(2n)**: each p^{v_p} ≤ 2n, at most √(2n) primes → (2n)^{√(2n)}.
2. **√(2n) < p ≤ 2n/3**: p² > 2n so v_p ≤ 1, product ≤ primorial(2n/3) ≤ 4^{2n/3}.
3. **2n/3 < p ≤ n**: v_p = 0, nothing.
4. **n < p ≤ 2n**: assumed nonexistent.

Conclusion: C(2n,n) ≤ (2n)^{√(2n)} · 4^{2n/3}.
-/

theorem chapter02_upper_bound (n : ℕ) (hn : 2 < n)
    (no_prime : ∀ p : ℕ, p.Prime → n < p → 2 * n < p) :
    n.centralBinom ≤ (2 * n) ^ (2 * n).sqrt * 4 ^ (2 * n / 3) :=
  centralBinom_le_of_no_bertrand_prime n hn no_prime

/-!
### Part 5: Main inequality and Bertrand's Postulate

For n ≥ 512, the inequality n · (2n)^{√(2n)} · 4^{2n/3} ≤ 4^n
is verified by a concavity argument (real analysis at x = 512).
-/

theorem chapter02_main_ineq (n : ℕ) (hn : 512 ≤ n) :
    n * (2 * n) ^ (2 * n).sqrt * 4 ^ (2 * n / 3) ≤ 4 ^ n :=
  bertrand_main_inequality hn

/-!
### Main theorem

*Book proof.* Suppose no prime exists in (n, 2n] for some n ≥ 512.
By the lower bound, 4^n < n · C(2n,n).
By the upper bound, C(2n,n) ≤ (2n)^{√(2n)} · 4^{2n/3}.
So 4^n < n · (2n)^{√(2n)} · 4^{2n/3}, contradicting the main inequality.
For n < 512, check directly with the explicit prime chain
2, 3, 5, 7, 13, 23, 43, 83, 163, 317 (each ≤ twice the next).
-/







end ProofsInTheBook.Chapter02

open ProofsInTheBook.Chapter02
open Nat Finset

theorem solution (n : ℕ) (hn : n ≠ 0) :
    ∃ p, Prime p ∧ n < p ∧ p ≤ 2 * n := by
  rcases lt_or_ge 511 n with h_large | h_small
  · -- Large n (≥ 512): contradiction from combining upper and lower bounds
    by_contra h_no
    push Not at h_no
    have h_lower := chapter02_central_binom_lower n (by omega)
    have h_upper := chapter02_upper_bound n (by omega) h_no
    exact absurd (calc
      4 ^ n < n * n.centralBinom := h_lower
      _ ≤ n * ((2 * n) ^ (2 * n).sqrt * 4 ^ (2 * n / 3)) :=
          Nat.mul_le_mul_left n h_upper
      _ = n * (2 * n) ^ (2 * n).sqrt * 4 ^ (2 * n / 3) := by ring
      _ ≤ 4 ^ n := chapter02_main_ineq n (by omega)) (lt_irrefl _)
  · -- Small n (< 512): explicit prime chain covering all cases
    have h_bound : n < 521 := by omega
    revert h_bound
    refine exists_prime_lt_and_le_two_mul_succ 317 (by norm_num1) (by norm_num1) ?_
    refine exists_prime_lt_and_le_two_mul_succ 163 (by norm_num1) (by norm_num1) ?_
    refine exists_prime_lt_and_le_two_mul_succ 83 (by norm_num1) (by norm_num1) ?_
    refine exists_prime_lt_and_le_two_mul_succ 43 (by norm_num1) (by norm_num1) ?_
    refine exists_prime_lt_and_le_two_mul_succ 23 (by norm_num1) (by norm_num1) ?_
    refine exists_prime_lt_and_le_two_mul_succ 13 (by norm_num1) (by norm_num1) ?_
    refine exists_prime_lt_and_le_two_mul_succ 7 (by norm_num1) (by norm_num1) ?_
    refine exists_prime_lt_and_le_two_mul_succ 5 (by norm_num1) (by norm_num1) ?_
    refine exists_prime_lt_and_le_two_mul_succ 3 (by norm_num1) (by norm_num1) ?_
    refine exists_prime_lt_and_le_two_mul_succ 2 (by norm_num1) (by norm_num1) ?_
    exact fun h2 => ⟨2, prime_two, h2,
      Nat.mul_le_mul_left 2 (Nat.pos_of_ne_zero hn)⟩
