-- Prove2me | solution 1 for ErdosProblems.Erdos1049.gaussBinom_mul_qPochhammer_qPochhammer
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:48:54.805353+00:00
-- url     : https://prove2.me/submissions/29f6d3d5-3a36-430b-90f4-4f6b3fed2717

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_self
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_succ_of_le
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_right
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_succ
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_zero
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_succ
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









/-! ## Gaussian binomial times `(q;q)_k` -/
end ErdosProblems.Erdos1049

variable {R : Type*} [CommRing R]
open ErdosProblems in
open ErdosProblems.Erdos1049 in
theorem solution (q : R) :
    ∀ n k, k ≤ n →
      gaussBinom q n k * qPochhammer q q k * qPochhammer q q (n - k) =
        qPochhammer q q n
  | 0, k, hk => by
      have : k = 0 := Nat.le_zero.mp hk
      subst this
      simp [qPochhammer]
  | n + 1, 0, _hk => by simp [qPochhammer]
  | n + 1, k + 1, hk => by
      have hk' : k ≤ n := Nat.succ_le_succ_iff.mp hk
      by_cases hkn : k + 1 ≤ n
      · have ih1 := solution q n (k + 1) hkn
        have ih0 := solution q n k
            (Nat.le_of_succ_le hkn)
        have hrec := gaussBinom_succ_of_le q hk'
        have hnk : n + 1 - (k + 1) = n - k := Nat.succ_sub_succ n k
        have hright :
            qPochhammer q q (n - k) =
              qPochhammer q q (n - (k + 1)) * (1 - q ^ (n - k)) := by
          have hdecomp : n - k = n - (k + 1) + 1 := by omega
          rw [hdecomp, qPochhammer]
          congr 1
          rw [← pow_succ']
        rw [hrec, hnk, add_mul, add_mul]
        have h1 :
            gaussBinom q n (k + 1) * qPochhammer q q (k + 1) *
                qPochhammer q q (n - k) =
              qPochhammer q q n * (1 - q ^ (n - k)) := by
          rw [hright]
          calc
            gaussBinom q n (k + 1) * qPochhammer q q (k + 1) *
                  (qPochhammer q q (n - (k + 1)) * (1 - q ^ (n - k))) =
                gaussBinom q n (k + 1) * qPochhammer q q (k + 1) *
                    qPochhammer q q (n - (k + 1)) * (1 - q ^ (n - k)) := by
              ring
            _ = qPochhammer q q n * (1 - q ^ (n - k)) := by
              rw [ih1]
        have h2 :
            q ^ (n - k) * gaussBinom q n k * qPochhammer q q (k + 1) *
                qPochhammer q q (n - k) =
              q ^ (n - k) * (1 - q ^ (k + 1)) * qPochhammer q q n := by
          rw [qPochhammer_succ, ← pow_succ']
          calc
            q ^ (n - k) * gaussBinom q n k *
                  (qPochhammer q q k * (1 - q ^ (k + 1))) *
                  qPochhammer q q (n - k) =
                q ^ (n - k) * (1 - q ^ (k + 1)) *
                  (gaussBinom q n k * qPochhammer q q k *
                    qPochhammer q q (n - k)) := by
              ring
            _ = q ^ (n - k) * (1 - q ^ (k + 1)) * qPochhammer q q n := by
              rw [ih0]
        rw [h1, h2, qPochhammer]
        have hpow : q ^ (n - k) * q ^ (k + 1) = q ^ (n + 1) := by
          rw [← pow_add]
          congr 1
          omega
        have hq1 : q * q ^ n = q ^ (n + 1) := (pow_succ' q n).symm
        rw [hq1, ← hpow]
        ring
      · have hkEq : k = n := le_antisymm hk' (by omega)
        subst hkEq
        simp [gaussBinom_self, qPochhammer]
