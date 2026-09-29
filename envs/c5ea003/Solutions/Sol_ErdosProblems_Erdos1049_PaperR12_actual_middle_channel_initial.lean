-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.actual_middle_channel_initial
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:14:38.87491+00:00
-- url     : https://prove2.me/submissions/b0d8dbe2-28fc-4d63-a78f-971411c0bae3

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBMonomialR12
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_succ
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_zero
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_X_power_dvd_signed_summand
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_mul_qPochhammer_qPochhammer
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_X_constantCoeff
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceDQuotient_constant_coefficient
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

namespace PaperR11
end PaperR11

/-!
# Exact initial coefficient of the actual B numerator


The numerator is divisible by X^M but not X^(M+1): at every n>=1 its
coefficient at M is exactly 1. This is proved by isolating the actual j=n,
s=0 channel. No finite reconstruction or initial-order hypothesis is used.
-/

namespace ErdosProblems.Erdos1049.PaperR12
open Polynomial PaperR11
open scoped BigOperators

theorem gaussian_constant_coefficient (n k : ℕ) (hk : k ≤ n) :
    (gaussBinom (X : ℤ[X]) n k).coeff 0 = 1 := by
  have h := congrArg (constantCoeff : ℤ[X] →+* ℤ)
    (gaussBinom_mul_qPochhammer_qPochhammer (X : ℤ[X]) n k hk)
  simpa only [map_mul, qPochhammer_X_constantCoeff, mul_one] using h

theorem sourceGaussianProduct_constant_coefficient (n s : ℕ) (hs : s ≤ 13 * n) :
    (sourceGaussianProduct n s).coeff 0 = 1 := by
  change constantCoeff (sourceGaussianProduct n s) = 1
  unfold sourceGaussianProduct
  rw [map_mul]
  change (gaussBinom (X : ℤ[X]) (14 * n + s) (12 * n)).coeff 0 *
    (gaussBinom (X : ℤ[X]) (13 * n) (13 * n - s)).coeff 0 = 1
  rw [gaussian_constant_coefficient _ _ (by omega),
    gaussian_constant_coefficient _ _ (by omega), one_mul]



lemma coefficient_zero_of_X_power_dvd (p : ℤ[X]) (m : ℕ)
    (h : (X : ℤ[X]) ^ (m + 1) ∣ p) : p.coeff m = 0 :=
  Polynomial.X_pow_dvd_iff.mp h m (by omega)





lemma sourceShiftedASummand_middle_exponent (n s : ℕ) :
    sourceM n + sourceAExponent n s - n * (2 * n + s) =
      sourceM n + s + s.choose 2 := by
  have h : sourceM n + sourceAExponent n s =
      sourceM n + s + s.choose 2 + n * (2 * n + s) := by
    unfold sourceAExponent
    ring
  omega

lemma sourceShiftedASummand_middle_strict (n s : ℕ) (hs : 0 < s) :
    (X : ℤ[X]) ^ (sourceM n + 1) ∣ sourceShiftedASummand n s n := by
  unfold sourceShiftedASummand
  rw [sourceShiftedASummand_middle_exponent]
  apply X_power_dvd_signed_summand
  omega
end ErdosProblems.Erdos1049.PaperR12

open Polynomial PaperR11
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR12 in
open ErdosProblems.Erdos1049.PaperR11 in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    (sourceShiftedASum n n * sourceDQuotient n n).coeff (sourceM n) = 1 := by
  classical
  unfold sourceShiftedASum
  rw [Finset.sum_mul, finset_sum_coeff, Finset.sum_eq_single 0]
  · have hform : sourceShiftedASummand n 0 n =
        (X : ℤ[X]) ^ sourceM n * sourceGaussianProduct n 0 := by
      unfold sourceShiftedASummand
      rw [sourceShiftedASummand_middle_exponent]
      simp
    rw [hform, mul_assoc, coeff_X_pow_mul']
    simp only [le_refl, if_true, Nat.sub_self]
    change constantCoeff (sourceGaussianProduct n 0 * sourceDQuotient n n) = 1
    rw [map_mul]
    change (sourceGaussianProduct n 0).coeff 0 * (sourceDQuotient n n).coeff 0 = 1
    rw [sourceGaussianProduct_constant_coefficient n 0 (by omega),
      sourceDQuotient_constant_coefficient n n (by omega), one_mul]
  · intro s hs hsne
    exact coefficient_zero_of_X_power_dvd _ _
      (dvd_mul_of_dvd_left (sourceShiftedASummand_middle_strict n s (by omega)) _)
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (by omega))).elim
