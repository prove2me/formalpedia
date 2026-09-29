-- Prove2me | solution 1 for ErdosProblems.Erdos1049.qPochhammer_X_constantCoeff
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:48:55.510907+00:00
-- url     : https://prove2.me/submissions/1ffe2cd6-8ac0-4ac3-ab70-7a22d7fa2534

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
theorem solution :
    ∀ m, constantCoeff (qPochhammer (X : ℤ[X]) X m) = 1
  | 0 => by simp [qPochhammer]
  | m + 1 => by
      rw [qPochhammer, map_mul, solution m, one_mul]
      change ((1 - X * X ^ m : ℤ[X]).coeff 0) = 1
      have hpow : X * X ^ m = (X : ℤ[X]) ^ (m + 1) := (pow_succ' (X : ℤ[X]) m).symm
      rw [coeff_sub, coeff_one, hpow, coeff_X_pow]
      simp
