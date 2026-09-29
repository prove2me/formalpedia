-- Prove2me | solution 1 for ErdosProblems.Erdos1049.qPochhammer_q_add
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:50:31.654723+00:00
-- url     : https://prove2.me/submissions/a48639ec-105d-4f5b-9a5d-fc7c039862ef

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_succ
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_zero
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































/-! ## Finite q-binomial theorem -/













/-! ## Splitting `(q;q)_{m+k}` and the constant term at the small-p endpoint -/
end ErdosProblems.Erdos1049

variable {R : Type*} [CommRing R]
open ErdosProblems in
open ErdosProblems.Erdos1049 in
theorem solution (q : R) (m : ℕ) : ∀ k,
    qPochhammer q q (m + k) =
      qPochhammer q q m * qPochhammer q (q ^ (m + 1)) k
  | 0 => by simp [qPochhammer]
  | k + 1 => by
      rw [Nat.add_succ, qPochhammer, solution q m k, qPochhammer,
        mul_assoc]
      congr 1
      simp [pow_succ, pow_add, mul_assoc, mul_comm]
