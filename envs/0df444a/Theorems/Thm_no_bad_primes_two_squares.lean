-- Prove2me | Theorems.Thm_no_bad_primes_two_squares
-- name    : no_bad_primes_two_squares
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T17:47:36.277652+00:00
-- url     : https://prove2.me/theorems/151c2160-0d5d-4afb-b5e7-a665f4635c89
-- title:
--   Fermat two-squares: no bad prime factors implies a sum of two squares
-- statement:
--   **Fermat's two-squares theorem (backward direction).** If every prime factor of $n$ is not congruent to $3 \pmod{4}$, then $n$ is a sum of two perfect squares.
--
--   $$\left(\forall p \mid n:\ p \text{ prime} \wedge p \not\equiv 3 \pmod{4}\right) \implies \exists a, b \in \mathbb{N}:\ n = a^2 + b^2.$$
--
--   This is the "easy" half of Fermat's full characterization (the other half: if $n = a^2 + b^2$, then every prime $p \equiv 3 \pmod{4}$ appears to an even power). The proof combines two facts:
--
--   1. Every prime $p$ with $p \not\equiv 3 \pmod{4}$ is a sum of two squares (Fermat's Christmas theorem, Mathlib's `Nat.Prime.sq_add_sq`).
--   2. The Brahmagupta–Fibonacci identity: products of sums of two squares are sums of two squares, $(x^2 + y^2)(u^2 + v^2) = (xu + yv)^2 + (xv - yu)^2$ (Mathlib's `Nat.sq_add_sq_mul`).
--
--   The proof is by strong induction on $n$, extracting one prime factor at a time (via `Nat.minFac`) and combining with the identity.
--
--   **Formalization Note** The base cases $n = 0$ and $n = 1$ are handled by $0 = 0^2 + 0^2$ and $1 = 1^2 + 0^2$.
-- source:
--   P. de Fermat (1640, letter to Mersenne); see also Mathlib.NumberTheory.SumTwoSquares, theorems Nat.Prime.sq_add_sq and Nat.sq_add_sq_mul

import Mathlib

theorem no_bad_primes_two_squares (n : ℕ) (hn : ∀ p ∈ n.primeFactors, p % 4 ≠ 3) :
    ∃ a b : ℕ, n = a ^ 2 + b ^ 2 := by sorry
