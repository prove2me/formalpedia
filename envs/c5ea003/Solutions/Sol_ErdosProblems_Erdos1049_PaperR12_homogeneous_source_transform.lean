-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.homogeneous_source_transform
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:55:38.458208+00:00
-- url     : https://prove2.me/submissions/7d0f60a5-6ae9-44da-922f-c01b0781172d

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_succ
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_zero
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_succ
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceInnerZ_qPochhammer
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









lemma pow_mul_inverse_power {K : Type*} [Field K] (y : K) (hy : y ≠ 0)
    (N s : ℕ) (hs : s ≤ N) : y ^ N * (y⁻¹) ^ s = y ^ (N - s) := by
  calc
    _ = (y ^ (N - s) * y ^ s) * (y⁻¹) ^ s := by
      rw [← pow_add, Nat.sub_add_cancel hs]
    _ = y ^ (N - s) := by
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hy, one_pow, mul_one]

lemma homogeneousPochhammer_clearing {K : Type*} [Field K]
    (q y : K) (hy : y ≠ 0) (h N : ℕ) :
    y ^ N * qPochhammer q (y⁻¹ * q ^ h) N = homogeneousPochhammer q y h N := by
  induction N with
  | zero => simp [homogeneousPochhammer]
  | succ N ih =>
      rw [qPochhammer_succ, pow_succ]
      have hf : y * (1 - y⁻¹ * q ^ h * q ^ N) = y - q ^ (h + N) := by
        rw [pow_add]
        field_simp [hy]
        <;> ring
      calc
        _ = (y ^ N * qPochhammer q (y⁻¹ * q ^ h) N) *
            (y * (1 - y⁻¹ * q ^ h * q ^ N)) := by ring
        _ = homogeneousPochhammer q y h N * (y - q ^ (h + N)) := by rw [ih, hf]
        _ = homogeneousPochhammer q y h (N + 1) := by
          simp only [homogeneousPochhammer, Finset.prod_range_succ]

lemma homogeneousSourceInner_clearing {K : Type*} [Field K]
    (q y : K) (hy : y ≠ 0) (a d v : ℕ) :
    y ^ (v - 1) * sourceInnerZ q y⁻¹ a d v = homogeneousSourceInner q y a d v := by
  unfold sourceInnerZ homogeneousSourceInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s ≤ v - 1 := by have hh := Finset.mem_range.mp hs; omega
  calc
    _ = (-1 : K) ^ s * q ^ s.choose 2 *
        (y ^ (v - 1) * (y⁻¹) ^ s) *
        gaussBinom q (v - 1) s * gaussBinom q (a + d + s - 1) (a - 1) := by ring
    _ = _ := by rw [pow_mul_inverse_power y hy (v - 1) s hs']
end ErdosProblems.Erdos1049.PaperR12

open Polynomial
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR12 in
theorem solution {K : Type*} [Field K]
    (q y : K) (hy : y ≠ 0) {a d v : ℕ} (ha : 1 ≤ a) (hv : 1 ≤ v) :
    qPochhammer q q (a - 1) * homogeneousSourceInner q y a d v =
      ∑ h ∈ Finset.range a, (-1 : K) ^ h * q ^ (h * (d + 1) + h.choose 2) *
        gaussBinom q (a - 1) h * homogeneousPochhammer q y h (v - 1) := by
  rw [← homogeneousSourceInner_clearing q y hy]
  calc
    _ = y ^ (v - 1) * (qPochhammer q q (a - 1) * sourceInnerZ q y⁻¹ a d v) := by ring
    _ = y ^ (v - 1) * (∑ h ∈ Finset.range a,
        (-1 : K) ^ h * q ^ (h * (d + 1) + h.choose 2) *
          gaussBinom q (a - 1) h * qPochhammer q (y⁻¹ * q ^ h) (v - 1)) := by
      rw [sourceInnerZ_qPochhammer q y⁻¹ ha hv]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      calc
        _ = ((-1 : K) ^ h * q ^ (h * (d + 1) + h.choose 2) *
            gaussBinom q (a - 1) h) *
              (y ^ (v - 1) * qPochhammer q (y⁻¹ * q ^ h) (v - 1)) := by ring
        _ = _ := by rw [homogeneousPochhammer_clearing q y hy]
