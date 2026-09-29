-- Prove2me | solution 1 for FactoringLab.polynomial_barrier_of_algebraic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:50:29.184966+00:00
-- url     : https://prove2.me/submissions/30255caa-68cb-4b68-84b4-0e4dc18e9b81

-- Sol generated from Probability/FactoringBarriers.lean
import Mathlib
import Definitions.Def_Probability_FactoringBarriers
import Theorems.Thm_FactoringLab_algebraic_barrier
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
theorem solution(P : Polynomial ℚ) :
    ¬ ∀ p q : ℕ, p.Prime → q.Prime → p < q → P.eval ((p * q : ℕ) : ℚ) = (p : ℚ) := by
  intro h
  set F : Polynomial (Polynomial ℚ) := Polynomial.C P - Polynomial.X with hF
  have hzero : F = 0 := by
    refine algebraic_barrier F ?_
    intro p q hp hq hpq
    simp only [hF, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_sub]
    rw [h p q hp hq hpq, sub_self]
  have hcoeff : F.coeff 1 = -1 := by
    simp [hF, Polynomial.coeff_X_one]
  rw [hzero] at hcoeff
  simp at hcoeff
