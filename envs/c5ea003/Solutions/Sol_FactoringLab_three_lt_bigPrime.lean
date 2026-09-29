-- Prove2me | solution 1 for FactoringLab.three_lt_bigPrime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:41:54.170201+00:00
-- url     : https://prove2.me/submissions/88b19ec7-b4a2-4662-aa2a-9d09acdb6fc4

-- Sol generated from Probability/FactoringBarriers.lean
import Mathlib
import Definitions.Def_Probability_FactoringBarriers
/-
# Barriers I: the polynomial barrier, rational escape, holomorphic rigidity

Three of the eight barriers of the Factoring Lab framework, proved.

* `FactoringLab.polynomial_barrier` — no polynomial with rational coefficients
  computes the smaller prime factor of a semiprime.
* `FactoringLab.rational_escape_illusory` (WWW) — the same for *rational
  functions* `A/B`: passing from polynomials to quotients buys nothing.
* `FactoringLab.algebraic_barrier` — the strongest form: *no* nonzero
  polynomial relation `F(N, p) = 0` in two variables over `ℚ` holds for all
  semiprimes.  The polynomial and rational barriers are special cases.
* `FactoringLab.polynomial_barrier_counting` — a quantitative version: for a
  fixed small factor `p`, a polynomial of degree `d` can return the correct
  factor at no more than `d` semiprimes `pq`.
* `FactoringLab.holomorphic_rigidity` / `holomorphic_rigidity_barrier` (HRB) —
  an entire function that reproduces the reciprocal of the smaller prime factor
  at the reciprocals of semiprimes is forced by the identity theorem to be
  constant, which is impossible.

The proofs share one mechanism: fixing the small factor makes the sample set
accumulate (at infinity for polynomials, at `0` for the holomorphic version),
and rigidity of the function class then forces a constant, which two different
choices of the small factor contradict.
-/

open FactoringLab

open Polynomial Filter Set

/-! ### Arithmetic input: infinitely many primes above any bound -/



/-! ### The polynomial and rational barriers -/




/-! ### The algebraic barrier: no algebraic relation between `N` and `p` -/




/-! ### Holomorphic rigidity -/










open FactoringLab in
theorem solution(n : ℕ) : 3 < bigPrime n := by
  have h0 : 2 ≤ Nat.nth Nat.Prime 0 := (Nat.prime_nth_prime 0).two_le
  have h01 : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime 1 :=
    Nat.nth_strictMono Nat.infinite_setOf_prime (by omega)
  have h12 : Nat.nth Nat.Prime 1 < Nat.nth Nat.Prime 2 :=
    Nat.nth_strictMono Nat.infinite_setOf_prime (by omega)
  have h2n : Nat.nth Nat.Prime 2 ≤ bigPrime n := by
    unfold bigPrime
    exact Nat.nth_monotone Nat.infinite_setOf_prime (by omega)
  omega
