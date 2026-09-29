-- Prove2me | solution 1 for ErdosProblems.Erdos1049.gaussBinom_mul_qPochhammer
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:51:38.889668+00:00
-- url     : https://prove2.me/submissions/0235e221-cdd8-4ff0-ace7-5900cda0b9c2

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_succ
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_succ
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_zero
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_mul_qPochhammer_qPochhammer
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_X_ne_zero
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_q_add
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

section
open scoped BigOperators
open Finset Polynomial
namespace ErdosProblems.Erdos1049
variable {R : Type*} [CommRing R]
lemma eval₂_gaussBinom (q : R) : ∀ n k,
    eval₂ (Int.castRingHom R) q (gaussBinom (X : ℤ[X]) n k) = gaussBinom q n k
  | 0, 0 => by simp [gaussBinom]
  | 0, k + 1 => by simp [gaussBinom]
  | n + 1, 0 => by simp [gaussBinom]
  | n + 1, k + 1 => by
      rw [gaussBinom_succ, gaussBinom_succ, eval₂_add]
      split_ifs with h
      · rw [eval₂_mul, eval₂_pow, eval₂_X, eval₂_gaussBinom q n (k + 1),
          eval₂_gaussBinom q n k]
      · rw [eval₂_zero, eval₂_gaussBinom q n (k + 1)]
end ErdosProblems.Erdos1049
end

section
open scoped BigOperators
open Finset Polynomial
namespace ErdosProblems.Erdos1049
variable {R : Type*} [CommRing R]
lemma eval₂_qPochhammer_Xpow (q : R) (m : ℕ) : ∀ n,
    eval₂ (Int.castRingHom R) q (qPochhammer X (X ^ m) n) =
      qPochhammer q (q ^ m) n
  | 0 => by simp [qPochhammer]
  | n + 1 => by
      rw [qPochhammer, qPochhammer, eval₂_mul, eval₂_sub, eval₂_one, eval₂_mul,
        eval₂_X_pow, eval₂_X_pow, eval₂_qPochhammer_Xpow q m n]
end ErdosProblems.Erdos1049
end

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



theorem gaussBinom_mul_qPochhammer_X {n k : ℕ} (h : k ≤ n) :
    gaussBinom (X : ℤ[X]) n k * qPochhammer X X k =
      qPochhammer X (X ^ (n - k + 1)) k := by
  have hfac := gaussBinom_mul_qPochhammer_qPochhammer (X : ℤ[X]) n k h
  have hsplit := qPochhammer_q_add (X : ℤ[X]) (n - k) k
  have hn : n - k + k = n := Nat.sub_add_cancel h
  apply mul_right_cancel₀ (qPochhammer_X_ne_zero (n - k))
  calc
    gaussBinom (X : ℤ[X]) n k * qPochhammer X X k * qPochhammer X X (n - k) =
        qPochhammer X X n := hfac
    _ = qPochhammer X X (n - k + k) := by rw [hn]
    _ = qPochhammer X X (n - k) * qPochhammer X (X ^ (n - k + 1)) k := hsplit
    _ = qPochhammer X (X ^ (n - k + 1)) k * qPochhammer X X (n - k) := mul_comm _ _



lemma eval₂_qPochhammer_X (q : R) : ∀ n,
    eval₂ (Int.castRingHom R) q (qPochhammer (X : ℤ[X]) X n) = qPochhammer q q n
  | 0 => by simp [qPochhammer]
  | n + 1 => by
      rw [qPochhammer, qPochhammer, eval₂_mul, eval₂_sub, eval₂_one, eval₂_mul,
        eval₂_pow, eval₂_X, eval₂_qPochhammer_X q n]
end ErdosProblems.Erdos1049

variable {R : Type*} [CommRing R]
open ErdosProblems in
open ErdosProblems.Erdos1049 in
theorem solution (q : R) {n k : ℕ} (h : k ≤ n) :
    gaussBinom q n k * qPochhammer q q k =
      qPochhammer q (q ^ (n - k + 1)) k := by
  have hp := gaussBinom_mul_qPochhammer_X h
  have := congrArg (eval₂ (Int.castRingHom R) q) hp
  simpa [eval₂_mul, eval₂_gaussBinom, eval₂_qPochhammer_X,
    eval₂_qPochhammer_Xpow] using this
