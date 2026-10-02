-- Prove2me | solution 1 for ProofsInTheBook.Chapter07.chapter07_sqrt_prime
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T14:43:35.933103+00:00
-- url     : https://prove2.me/submissions/00d49b85-20a2-4b14-9f91-a82f184f6119

import Mathlib


/-!
# Chapter 7: Some irrational numbers

From "Proofs from THE BOOK":

The book proves √2, e, and π are irrational using elementary arguments.

**√p is irrational** (for any prime p): The classic proof by contradiction.
If √p = a/b with gcd(a,b) = 1, then p·b² = a², so p | a. Writing a = pc,
we get p·b² = p²c², hence b² = pc², so p | b. But gcd(a,b) = 1, contradiction.

**e is irrational**: Using e = ∑ 1/k!, if e = a/b then
n!·(e - ∑_{k=0}^n 1/k!) is an integer strictly between 0 and 1 for n = |b|+2,
a contradiction.

**π² is irrational** (hence π is irrational): Niven's proof constructs
a polynomial integral that is simultaneously a positive integer and
tends to zero.
-/

set_option maxHeartbeats 800000

namespace ProofsInTheBook.Chapter07

open scoped BigOperators

/-!
### √p is irrational for prime p

*Book proof.* Suppose √p = a/b in lowest terms. Then a² = pb², so p | a².
Since p is prime, p | a. Write a = pc. Then p²c² = pb², so pc² = b²,
giving p | b. This contradicts gcd(a,b) = 1.
-/





/-!
### e is irrational

*Book proof.* Write e = ∑_{k=0}^∞ 1/k!. If e = a/b, pick n = |b|+2 > b and consider
  n! · (e - ∑_{k=0}^n 1/k!) = ∑_{j≥0} n!/(n+1+j)!
Each term ≤ (1/(n+1))^(j+1), so the sum ≤ 1/n ≤ 1/2 < 1.
This quantity is also a positive integer (n!·e is an integer since b|n!,
and n!·∑1/k! is an integer termwise), a contradiction.
-/













/-!
### π is irrational

*Book proof.* Niven's short proof: for π = a/b, define
  f(x) = x^n(a - bx)^n / n!
and F(x) = f(x) - f''(x) + f⁴(x) - ⋯. Then d/dx[F'sinx - Fcosx] = f(x)sinx,
so ∫₀^π f(x)sin(x) dx = F(0) + F(π) is a positive integer.
But 0 < ∫₀^π f(x)sin(x) dx < π·(πa)^n/n! → 0, contradiction for large n.
-/





end ProofsInTheBook.Chapter07

set_option maxHeartbeats 800000
open scoped BigOperators
open ProofsInTheBook.Chapter07

theorem solution (p : ℕ) (hp : p.Prime) : Irrational (√(p : ℝ)) := by
  rw [show (p : ℝ) = ((p : ℕ) : ℝ) from by simp]
  exact irrational_sqrt_natCast_iff.mpr hp.prime.not_isSquare
