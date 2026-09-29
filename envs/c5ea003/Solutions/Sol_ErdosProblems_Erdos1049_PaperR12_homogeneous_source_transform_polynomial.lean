-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.homogeneous_source_transform_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:57:34.629852+00:00
-- url     : https://prove2.me/submissions/57dccb86-5671-47d6-9434-fcc195f2a243

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_succ
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_right
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_succ
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_zero
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_succ
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_homogeneous_source_transform
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_rationalPolynomial_X_ne_zero
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic

/-!
# Homogeneous finite transform and monomial cancellation tools

Homogenisation removes the need to assert
that a Laurent expression is an integral polynomial. The identity is first
proved in a field, then pulled back through the injective fraction-field map.
The final displayed identity is entirely in Z[X].
-/

namespace ErdosProblems.Erdos1049.PaperR12
open Polynomial
open scoped BigOperators

lemma map_gaussian {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (q : R) (n k : ℕ) : f (gaussBinom q n k) = gaussBinom (f q) n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [gaussBinom]
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [gaussBinom_succ, gaussBinom_succ, map_add]
          split_ifs <;> simp only [map_mul, map_pow, map_zero, ih]

lemma map_finitePochhammer {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (q z : R) (n : ℕ) :
    f (qPochhammer q z n) = qPochhammer (f q) (f z) n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [qPochhammer_succ, map_mul, map_sub, map_one, map_pow, ih]
end ErdosProblems.Erdos1049.PaperR12

open Polynomial
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR12 in
theorem solution (u : ℕ) {a d v : ℕ}
    (ha : 1 ≤ a) (hv : 1 ≤ v) :
    qPochhammer (X : ℤ[X]) X (a - 1) *
        homogeneousSourceInner X (X ^ u) a d v =
      ∑ h ∈ Finset.range a, (-1 : ℤ[X]) ^ h * X ^ (h * (d + 1) + h.choose 2) *
        gaussBinom X (a - 1) h * homogeneousPochhammer X (X ^ u) h (v - 1) := by
  let f : ℤ[X] →+* RatFunc ℤ := algebraMap ℤ[X] (RatFunc ℤ)
  have hy : (f X) ^ u ≠ 0 := pow_ne_zero _ rationalPolynomial_X_ne_zero
  have ht := homogeneous_source_transform (f X) ((f X) ^ u) hy
    (a := a) (d := d) (v := v) ha hv
  have hm : f (qPochhammer (X : ℤ[X]) X (a - 1) *
        homogeneousSourceInner X (X ^ u) a d v -
      ∑ h ∈ Finset.range a, (-1 : ℤ[X]) ^ h * X ^ (h * (d + 1) + h.choose 2) *
        gaussBinom X (a - 1) h * homogeneousPochhammer X (X ^ u) h (v - 1)) = 0 := by
    simp only [map_sub, map_mul, map_sum, map_pow, map_neg, map_one,
      map_gaussian, map_finitePochhammer, homogeneousSourceInner,
      homogeneousPochhammer, map_prod] at ht ⊢
    exact sub_eq_zero.mpr ht
  change algebraMap ℤ[X] (RatFunc ℤ) _ = 0 at hm
  rw [IsFractionRing.to_map_eq_zero_iff] at hm
  exact sub_eq_zero.mp hm
