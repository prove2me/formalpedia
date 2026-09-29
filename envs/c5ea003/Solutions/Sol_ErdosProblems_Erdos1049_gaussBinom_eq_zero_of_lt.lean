-- Prove2me | solution 1 for ErdosProblems.Erdos1049.gaussBinom_eq_zero_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:20:16.467121+00:00
-- url     : https://prove2.me/submissions/6199fd3b-c6ef-44c6-a4c4-abf5915c2021

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_succ
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Erdős #1049: finite q-binomial algebra for the 2004 small-p unit

Zudilin, Acta Arith. 111 (2004), displays (8)–(11).  After the published
integrality exponent `M` is removed, the second source coefficient is a
unit at `p = 0`.  The new algebra is the finite q-binomial theorem, the
vanishing range for exponents that hit `1`, and the constant term of
`(q^α; q)_n` for `α ≥ 1`.  This module Lean-checks those identities.  It
does not construct the source sums `A(p), B(p)`, does not prove
irrationality of `F(3/2)`, and is not the 2016 Hankel family.

The Gaussian binomial uses the same Pascal recurrence as
`AdelicHeightBridge.zudilinQBinomialPS`, as a ring element rather than a
power series.
-/

open scoped BigOperators
open Finset Polynomial

namespace ErdosProblems.Erdos1049
variable {R : Type*} [CommRing R]

/-! ## q-Pochhammer and Gaussian binomials -/
end ErdosProblems.Erdos1049

variable {R : Type*} [CommRing R]
open ErdosProblems in
open ErdosProblems.Erdos1049 in
theorem solution (q : R) : ∀ {n k : ℕ}, n < k → gaussBinom q n k = 0
  | 0, 0, h => (Nat.lt_irrefl 0 h).elim
  | 0, k + 1, _ => rfl
  | n + 1, 0, h => (Nat.not_lt_zero _ h).elim
  | n + 1, k + 1, h => by
      have h1 : n < k + 1 := Nat.lt_of_succ_lt_succ (Nat.lt_succ_of_lt h)
      have h2 : ¬ k ≤ n := Nat.not_le.mpr (Nat.lt_of_succ_lt_succ h)
      rw [gaussBinom_succ, solution q h1, if_neg h2, add_zero]
