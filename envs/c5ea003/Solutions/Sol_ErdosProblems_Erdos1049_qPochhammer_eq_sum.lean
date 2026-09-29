-- Prove2me | solution 1 for ErdosProblems.Erdos1049.qPochhammer_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:53:15.152202+00:00
-- url     : https://prove2.me/submissions/fb3371cc-9a77-4cdb-8326-6dfb4e8accd5

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Theorems.Thm_ErdosProblems_Erdos1049_choose_two_succ
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_eq_zero_of_lt
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_succ_of_le
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_right
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_succ
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_zero
import Theorems.Thm_ErdosProblems_Erdos1049_qBinomialTerm_zero
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





























lemma sum_range_zero_add {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ∑ k ∈ range (n + 1), f k = f 0 + ∑ j ∈ range n, f (j + 1)
  | 0 => by simp
  | n + 1 => by
      rw [sum_range_succ, sum_range_zero_add f n, sum_range_succ, add_assoc]

/-! ## Finite q-binomial theorem -/





theorem qBinomialTerm_of_lt (q z : R) {n k : ℕ} (h : n < k) :
    qBinomialTerm q z n k = 0 := by
  simp [qBinomialTerm, gaussBinom_eq_zero_of_lt q h]

theorem qBinomialTerm_succ_split (q z : R) {n j : ℕ} (hj : j ≤ n) :
    qBinomialTerm q z (n + 1) (j + 1) =
      qBinomialTerm q z n (j + 1) +
        gaussBinom q n j * (-1 : R) ^ (j + 1) * q ^ (n - j) *
          q ^ (j + 1).choose 2 * z ^ (j + 1) := by
  rw [qBinomialTerm, qBinomialTerm, gaussBinom_succ_of_le q hj]
  ring

theorem qBinomialTerm_shift_eq (q z : R) {n j : ℕ} (hj : j ≤ n) :
    gaussBinom q n j * (-1 : R) ^ (j + 1) * q ^ (n - j) *
        q ^ (j + 1).choose 2 * z ^ (j + 1) =
      -z * q ^ n * qBinomialTerm q z n j := by
  have hpow : q ^ (n - j) * q ^ (j.choose 2 + j) = q ^ n * q ^ j.choose 2 := by
    rw [← pow_add, ← pow_add]
    congr 1
    have : n - j + j = n := Nat.sub_add_cancel hj
    omega
  simp only [qBinomialTerm, choose_two_succ, pow_succ]
  calc
    gaussBinom q n j * ((-1 : R) ^ j * -1) * q ^ (n - j) *
          q ^ (j.choose 2 + j) * (z ^ j * z) =
        gaussBinom q n j * (-1 : R) ^ j *
          (q ^ (n - j) * q ^ (j.choose 2 + j)) * z ^ j * -z := by
      ring
    _ = gaussBinom q n j * (-1 : R) ^ j * (q ^ n * q ^ j.choose 2) * z ^ j * -z := by
      rw [hpow]
    _ = -z * q ^ n * (gaussBinom q n j * (-1 : R) ^ j * q ^ j.choose 2 * z ^ j) := by
      ring
end ErdosProblems.Erdos1049

variable {R : Type*} [CommRing R]
open ErdosProblems in
open ErdosProblems.Erdos1049 in
set_option maxHeartbeats 400000 in

theorem solution (q z : R) : ∀ n,
    qPochhammer q z n = ∑ k ∈ range (n + 1), qBinomialTerm q z n k
  | 0 => by
      simp [qPochhammer, qBinomialTerm]
  | n + 1 => by
      have ih := solution q z n
      have hA :
          ∑ j ∈ range (n + 1), qBinomialTerm q z n (j + 1) =
            qPochhammer q z n - 1 := by
        have hshift := sum_range_zero_add (qBinomialTerm q z n) (n + 1)
        have hlast : qBinomialTerm q z n (n + 1) = 0 :=
          qBinomialTerm_of_lt q z (Nat.lt_succ_self n)
        have hsum :
            ∑ k ∈ range (n + 2), qBinomialTerm q z n k =
              ∑ k ∈ range (n + 1), qBinomialTerm q z n k := by
          rw [sum_range_succ, hlast, add_zero]
        have hn2 : n + 1 + 1 = n + 2 := by omega
        have hshift' :
            ∑ k ∈ range (n + 2), qBinomialTerm q z n k =
              qBinomialTerm q z n 0 +
                ∑ j ∈ range (n + 1), qBinomialTerm q z n (j + 1) := by
          simpa [hn2] using hshift
        have h : qPochhammer q z n =
            1 + ∑ j ∈ range (n + 1), qBinomialTerm q z n (j + 1) := by
          rw [ih, ← hsum, hshift', qBinomialTerm_zero]
        exact eq_sub_of_add_eq (by simpa [add_comm] using h.symm)
      have hB :
          ∑ j ∈ range (n + 1),
              gaussBinom q n j * (-1 : R) ^ (j + 1) * q ^ (n - j) *
                q ^ (j + 1).choose 2 * z ^ (j + 1) =
            -z * q ^ n * qPochhammer q z n := by
        have hcong :
            ∑ j ∈ range (n + 1),
                gaussBinom q n j * (-1 : R) ^ (j + 1) * q ^ (n - j) *
                  q ^ (j + 1).choose 2 * z ^ (j + 1) =
              ∑ j ∈ range (n + 1), -z * q ^ n * qBinomialTerm q z n j := by
          refine sum_congr rfl ?_
          intro j hj
          exact qBinomialTerm_shift_eq q z (Nat.lt_succ_iff.mp (mem_range.mp hj))
        rw [hcong, ← mul_sum, ih]
      have hsucc :
          ∑ j ∈ range (n + 1), qBinomialTerm q z (n + 1) (j + 1) =
            ∑ j ∈ range (n + 1), qBinomialTerm q z n (j + 1) +
              ∑ j ∈ range (n + 1),
                gaussBinom q n j * (-1 : R) ^ (j + 1) * q ^ (n - j) *
                  q ^ (j + 1).choose 2 * z ^ (j + 1) := by
        have hcong :
            ∑ j ∈ range (n + 1), qBinomialTerm q z (n + 1) (j + 1) =
              ∑ j ∈ range (n + 1),
                (qBinomialTerm q z n (j + 1) +
                  gaussBinom q n j * (-1 : R) ^ (j + 1) * q ^ (n - j) *
                    q ^ (j + 1).choose 2 * z ^ (j + 1)) := by
          refine sum_congr rfl ?_
          intro j hj
          exact qBinomialTerm_succ_split q z (Nat.lt_succ_iff.mp (mem_range.mp hj))
        rw [hcong, sum_add_distrib]
      rw [qPochhammer]
      calc
        qPochhammer q z n * (1 - z * q ^ n) =
            qPochhammer q z n - z * q ^ n * qPochhammer q z n := by ring
        _ = 1 + ((qPochhammer q z n - 1) + -z * q ^ n * qPochhammer q z n) := by
            ring
        _ = qBinomialTerm q z (n + 1) 0 +
              (∑ j ∈ range (n + 1), qBinomialTerm q z n (j + 1) +
                ∑ j ∈ range (n + 1),
                  gaussBinom q n j * (-1 : R) ^ (j + 1) * q ^ (n - j) *
                    q ^ (j + 1).choose 2 * z ^ (j + 1)) := by
            rw [qBinomialTerm_zero, hA, hB]
        _ = qBinomialTerm q z (n + 1) 0 +
              ∑ j ∈ range (n + 1), qBinomialTerm q z (n + 1) (j + 1) := by
            rw [hsucc]
        _ = ∑ k ∈ range (n + 2), qBinomialTerm q z (n + 1) k := by
            have hn2 : n + 1 + 1 = n + 2 := by omega
            simpa [hn2] using
              (sum_range_zero_add (qBinomialTerm q z (n + 1)) (n + 1)).symm
