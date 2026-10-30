-- Prove2me | solution 1 for AnalyticCombinatorics.Ch7.SingularityApp.RootedLTreeNS.rootedLTreeClass_count_eq_cayley
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T20:24:45.019984+00:00
-- url     : https://prove2.me/submissions/a2f32dc5-85d8-4044-bb78-e7e631b31edc

import Definitions.Def_AnalyticCombinatorics_Ch1_Lagrange_ImplicitSeries
import Definitions.Def_AnalyticCombinatorics_Ch1_Lagrange_Residue
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledProduct
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_RootedLTree
import Mathlib
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Implicit formal power series

This file constructs, coefficient by coefficient, the unique formal power
series `T` with zero constant term satisfying `T = X * φ.subst T`.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch1.Lagrange

open PowerSeries

variable {R : Type*} [CommRing R]

namespace ImplicitSeries

lemma trunc_eq_of_coeff_eq {f g : R⟦X⟧} {n : ℕ}
    (h : ∀ i, i < n → coeff i f = coeff i g) :
    trunc n f = trunc n g := by
  ext i
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
  split_ifs with hi
  · exact h i hi
  · rfl

lemma coeff_eq_coeff_trunc_pow (f : R⟦X⟧) (n d : ℕ) :
    coeff n (f ^ d) = coeff n (((trunc (n + 1) f : Polynomial R) : R⟦X⟧) ^ d) := by
  symm
  rw [← coeff_coe_trunc_of_lt (n := n) (m := n + 1)
    (f := (((trunc (n + 1) f : Polynomial R) : R⟦X⟧) ^ d)) (Nat.lt_succ_self n)]
  rw [PowerSeries.trunc_trunc_pow]
  rw [coeff_coe_trunc_of_lt (n := n) (m := n + 1) (f := f ^ d) (Nat.lt_succ_self n)]

lemma coeff_subst_eq_of_coeff_eq {f g : R⟦X⟧} (hf : PowerSeries.HasSubst f)
    (hg : PowerSeries.HasSubst g) (φ : R⟦X⟧) {n : ℕ}
    (h : ∀ i, i ≤ n → coeff i f = coeff i g) :
    coeff n (φ.subst f) = coeff n (φ.subst g) := by
  rw [PowerSeries.coeff_subst' hf φ n, PowerSeries.coeff_subst' hg φ n]
  apply finsum_congr
  intro d
  congr 1
  rw [coeff_eq_coeff_trunc_pow f n d, coeff_eq_coeff_trunc_pow g n d]
  congr 1
  exact congrArg (fun p : Polynomial R => ((p : R⟦X⟧) ^ d)) <|
    trunc_eq_of_coeff_eq (f := f) (g := g) (n := n + 1) fun i hi =>
      h i (Nat.le_of_lt_succ hi)

@[simp]
lemma coeff_partialSeries (a : ℕ → R) (n k : ℕ) :
    coeff k (partialSeries (R := R) a n) = if k < n then a k else 0 := by
  simp [partialSeries]

@[simp]
theorem coeff_implicitSeries (φ : R⟦X⟧) (n : ℕ) :
    coeff n (implicitSeries φ) = implicitCoeff φ n := by
  simp [implicitSeries]

@[simp]
theorem implicitCoeff_zero (φ : R⟦X⟧) :
    implicitCoeff φ 0 = 0 := by
  rw [implicitCoeff, Nat.strongRec_eq, implicitStep]

theorem implicitCoeff_succ (φ : R⟦X⟧) (n : ℕ) :
    implicitCoeff φ (n + 1) =
      coeff n (φ.subst (partialSeries (implicitCoeff φ) (n + 1))) := by
  rw [implicitCoeff, Nat.strongRec_eq, implicitStep]
  congr 2
  ext k
  by_cases hk : k < n + 1
  · simp only [coeff_partialSeries, hk, ↓reduceIte]
    rfl
  · simp only [coeff_partialSeries, hk, ↓reduceIte]

@[simp]
theorem constantCoeff_partialSeries_succ (a : ℕ → R) (n : ℕ) (h0 : a 0 = 0) :
    constantCoeff (partialSeries (R := R) a (n + 1)) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [h0]

@[simp]
theorem constantCoeff_implicitSeries (φ : R⟦X⟧) :
    constantCoeff (implicitSeries φ) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp

theorem hasSubst_implicitSeries (φ : R⟦X⟧) :
    PowerSeries.HasSubst (implicitSeries φ) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_implicitSeries φ)

theorem hasSubst_partialSeries_implicitCoeff_succ (φ : R⟦X⟧) (n : ℕ) :
    PowerSeries.HasSubst (partialSeries (implicitCoeff φ) (n + 1)) :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    (constantCoeff_partialSeries_succ (R := R) (implicitCoeff φ) n (implicitCoeff_zero φ))

theorem coeff_subst_partialSeries_implicitCoeff (φ : R⟦X⟧) (n : ℕ) :
    coeff n (φ.subst (partialSeries (implicitCoeff φ) (n + 1))) =
      coeff n (φ.subst (implicitSeries φ)) := by
  apply coeff_subst_eq_of_coeff_eq
      (hasSubst_partialSeries_implicitCoeff_succ φ n) (hasSubst_implicitSeries φ)
  intro i hi
  simp [coeff_implicitSeries, hi]

theorem implicitSeries_spec (φ : R⟦X⟧) :
    implicitSeries φ = X * φ.subst (implicitSeries φ) := by
  ext n
  cases n with
  | zero =>
      simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  | succ n =>
      rw [coeff_implicitSeries, implicitCoeff_succ, coeff_succ_X_mul]
      exact coeff_subst_partialSeries_implicitCoeff φ n

theorem implicitSeries_unique (φ T : R⟦X⟧)
    (hT : T = X * φ.subst T) (h0 : constantCoeff T = 0) :
    T = implicitSeries φ := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          rw [coeff_implicitSeries, implicitCoeff_zero, coeff_zero_eq_constantCoeff_apply, h0]
      | succ n =>
          have hsubst : coeff n (φ.subst T) =
              coeff n (φ.subst (partialSeries (implicitCoeff φ) (n + 1))) := by
            apply coeff_subst_eq_of_coeff_eq
              (PowerSeries.HasSubst.of_constantCoeff_zero' h0)
              (hasSubst_partialSeries_implicitCoeff_succ φ n)
            intro i hi
            have hlt : i < n + 1 := Nat.lt_succ_of_le hi
            have ih_i : coeff i T = coeff i (implicitSeries φ) := ih i hlt
            simp [coeff_implicitSeries, hlt, ih_i]
          have hcoeff := congrArg (coeff (n + 1)) hT
          rw [coeff_succ_X_mul] at hcoeff
          rw [coeff_implicitSeries, implicitCoeff_succ, ← hsubst, ← hcoeff]

end ImplicitSeries
end AnalyticCombinatorics.Ch1.Lagrange
end

/-!
# Formal residues for the Lagrange inversion proof

This file uses the lightweight Laurent representation `X^{-N} * F`, with
`F : R⟦X⟧`.  The residue is the coefficient of `X^{N-1}` in `F`.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch1.Lagrange.Residue

open PowerSeries

variable {R : Type*} [CommRing R]

@[simp]
theorem resShift_succ (N : ℕ) (F : R⟦X⟧) :
    resShift (N + 1) F = coeff N F := by
  simp [resShift]

theorem res_derivative_shift (N : ℕ) (F : R⟦X⟧) :
    resShift (N + 1) (shiftDerivNumer N F) = 0 := by
  unfold shiftDerivNumer
  cases N with
  | zero =>
      simp
  | succ N =>
      change coeff (N + 1) (X * d⁄dX R F - C ((N + 1 : ℕ) : R) * F) = 0
      rw [map_sub, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
        PowerSeries.coeff_C_mul]
      norm_num
      ring

theorem isUnit_natCast_of_ratAlgebra [Algebra ℚ R] {n : ℕ} (hn : n ≠ 0) :
    IsUnit (n : R) := by
  simpa only [map_natCast] using
    (IsUnit.map (algebraMap ℚ R) (IsUnit.mk0 (n : ℚ) (Nat.cast_ne_zero.mpr hn)))

theorem res_unitKernel_one (U : R⟦X⟧ˣ) :
    resShift 1 (unitKernel U 1) = 1 := by
  set_option backward.isDefEq.respectTransparency false in
    have hcoeff :
        constantCoeff (((U⁻¹ : R⟦X⟧ˣ) : R⟦X⟧)) * constantCoeff (U : R⟦X⟧) = 1 := by
      have hmul : (((U⁻¹ : R⟦X⟧ˣ) : R⟦X⟧) * (U : R⟦X⟧)) = 1 := by
        simp
      simp [← map_mul, hmul]
    simpa [resShift, unitKernel, unitSeries, unitInvSeries] using hcoeff

theorem shiftDerivNumer_unitInv_pow (U : R⟦X⟧ˣ) (m : ℕ) :
    shiftDerivNumer m (unitInvSeries U ^ m) =
      -C (m : R) * unitKernel U (m + 1) := by
  set_option backward.isDefEq.respectTransparency false in
    cases m with
    | zero =>
        simp [shiftDerivNumer, unitKernel, unitSeries, unitInvSeries]
    | succ m =>
        unfold shiftDerivNumer unitKernel unitSeries unitInvSeries
        rw [PowerSeries.derivative_pow]
        simp [pow_succ, mul_assoc, mul_comm, mul_left_comm, sub_eq_add_neg]
        have hcancel :
            (((U⁻¹ : R⟦X⟧ˣ) : R⟦X⟧) ^ 2 * ((U⁻¹ : R⟦X⟧ˣ) : R⟦X⟧) ^ m *
                (U : R⟦X⟧)) =
              ((U⁻¹ : R⟦X⟧ˣ) : R⟦X⟧) * ((U⁻¹ : R⟦X⟧ˣ) : R⟦X⟧) ^ m := by
          rw [pow_two]
          simp [mul_assoc, mul_comm]
        have hcancel_nat :
            (((U⁻¹ : R⟦X⟧ˣ) : R⟦X⟧) ^ 2 * ((U⁻¹ : R⟦X⟧ˣ) : R⟦X⟧) ^ m *
                (m : R⟦X⟧) * (U : R⟦X⟧)) =
              ((U⁻¹ : R⟦X⟧ˣ) : R⟦X⟧) * ((U⁻¹ : R⟦X⟧ˣ) : R⟦X⟧) ^ m *
                (m : R⟦X⟧) := by
          calc
            (((U⁻¹ : R⟦X⟧ˣ) : R⟦X⟧) ^ 2 * ((U⁻¹ : R⟦X⟧ˣ) : R⟦X⟧) ^ m *
                (m : R⟦X⟧) * (U : R⟦X⟧)) =
                (((U⁻¹ : R⟦X⟧ˣ) : R⟦X⟧) ^ 2 *
                  ((U⁻¹ : R⟦X⟧ˣ) : R⟦X⟧) ^ m * (U : R⟦X⟧)) * (m : R⟦X⟧) := by
              ring
            _ = ((U⁻¹ : R⟦X⟧ˣ) : R⟦X⟧) *
                  ((U⁻¹ : R⟦X⟧ˣ) : R⟦X⟧) ^ m * (m : R⟦X⟧) := by
              rw [hcancel]
        ring_nf
        rw [hcancel, hcancel_nat]
        ring

theorem res_unitKernel_succ_succ [Algebra ℚ R] (U : R⟦X⟧ˣ) (m : ℕ) :
    resShift (m + 2) (unitKernel U (m + 2)) = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    let q := m + 1
    have hder := res_derivative_shift (R := R) q (unitInvSeries U ^ q)
    have hshift := shiftDerivNumer_unitInv_pow (R := R) U q
    have hmul : (q : R) * resShift (q + 1) (unitKernel U (q + 1)) = 0 := by
      rw [hshift] at hder
      have hcoeff : coeff q (C (q : R) * unitKernel U (q + 1)) = 0 := by
        simpa [resShift] using hder
      rw [PowerSeries.coeff_C_mul] at hcoeff
      simpa [resShift] using hcoeff
    have hunit : IsUnit (q : R) := isUnit_natCast_of_ratAlgebra (R := R) (by simp [q])
    have hres : resShift (q + 1) (unitKernel U (q + 1)) = 0 :=
      (IsUnit.mul_right_eq_zero hunit).mp hmul
    simpa [q, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hres

theorem unitInv_pow_mul_unit_pow (U : R⟦X⟧ˣ) {N d : ℕ} (hd : d ≤ N) :
    unitInvSeries U ^ N * unitSeries U ^ d = unitInvSeries U ^ (N - d) := by
  have hunit : (U⁻¹ ^ N * U ^ d : R⟦X⟧ˣ) = U⁻¹ ^ (N - d) := by
    simpa [inv_pow, mul_comm] using (inv_pow_sub U hd).symm
  simpa [unitSeries, unitInvSeries] using congrArg (fun V : R⟦X⟧ˣ => (V : R⟦X⟧)) hunit

theorem coeff_unit_monomial_kernel [Algebra ℚ R] (U : R⟦X⟧ˣ) (n d : ℕ) :
    coeff n
        (unitInvSeries U ^ (n + 1) * ((X * unitSeries U) ^ d) *
          (unitSeries U + X * d⁄dX R (unitSeries U))) =
      if d = n then 1 else 0 := by
  set_option backward.isDefEq.respectTransparency false in
    have hrewrite :
        unitInvSeries U ^ (n + 1) * ((X * unitSeries U) ^ d) *
            (unitSeries U + X * d⁄dX R (unitSeries U)) =
          X ^ d * (unitInvSeries U ^ (n + 1) * unitSeries U ^ d *
            (unitSeries U + X * d⁄dX R (unitSeries U))) := by
      rw [mul_pow]
      ring
    rw [hrewrite, PowerSeries.coeff_X_pow_mul']
    by_cases hdn : d ≤ n
    · rw [if_pos hdn]
      have hcancel :
          unitInvSeries U ^ (n + 1) * unitSeries U ^ d = unitInvSeries U ^ (n + 1 - d) :=
        unitInv_pow_mul_unit_pow U (N := n + 1) (d := d) (Nat.le_trans hdn (Nat.le_succ n))
      rw [hcancel]
      by_cases hEq : d = n
      · subst d
        simpa [unitKernel, resShift] using res_unitKernel_one (R := R) U
      · have hlt : d < n := Nat.lt_of_le_of_ne hdn hEq
        have hzero :=
          res_unitKernel_succ_succ (R := R) U (n - d - 1)
        have hindex : n - d - 1 + 2 = n + 1 - d := by omega
        have hres :
            resShift (n + 1 - d) (unitKernel U (n + 1 - d)) = 0 := by
          simpa [hindex] using hzero
        have hcoeffIndex : n + 1 - d - 1 = n - d := by omega
        rw [if_neg hEq]
        simpa [resShift, unitKernel, hcoeffIndex] using hres
    · rw [if_neg hdn]
      rw [if_neg (fun hEq => hdn (by omega))]

theorem hasSubst_X_mul_unit (U : R⟦X⟧ˣ) :
    PowerSeries.HasSubst (X * unitSeries U) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [unitSeries])

theorem subst_coe_trunc_eq_sum_range (U : R⟦X⟧ˣ) (F : R⟦X⟧) (n : ℕ) :
    (((trunc (n + 1) F : Polynomial R) : R⟦X⟧).subst (X * unitSeries U)) =
      ∑ i ∈ Finset.range (n + 1), C (coeff i F) * (X * unitSeries U) ^ i := by
  rw [PowerSeries.subst_coe (hasSubst_X_mul_unit (R := R) U)]
  simpa [Polynomial.aeval_def] using
    (PowerSeries.eval₂_trunc_eq_sum_range
      (s := (X * unitSeries U : R⟦X⟧)) (G := C) (n := n + 1) (f := F))

theorem residue_subst_unit_trunc [Algebra ℚ R] (U : R⟦X⟧ˣ) (F : R⟦X⟧) (n : ℕ) :
    coeff n
        (unitInvSeries U ^ (n + 1) *
          (((trunc (n + 1) F : Polynomial R) : R⟦X⟧).subst (X * unitSeries U)) *
          (unitSeries U + X * d⁄dX R (unitSeries U))) =
      coeff n F := by
  set_option backward.isDefEq.respectTransparency false in
    rw [subst_coe_trunc_eq_sum_range (R := R) U F n]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [map_sum]
    have hterm (i : ℕ) :
          coeff n
              (unitInvSeries U ^ (n + 1) *
                (C (coeff i F) * (X * unitSeries U) ^ i) *
                (unitSeries U + X * d⁄dX R (unitSeries U))) =
            coeff i F * (if i = n then 1 else 0) := by
      calc
        coeff n
            (unitInvSeries U ^ (n + 1) *
              (C (coeff i F) * (X * unitSeries U) ^ i) *
              (unitSeries U + X * d⁄dX R (unitSeries U))) =
            coeff n
              (C (coeff i F) *
                (unitInvSeries U ^ (n + 1) * (X * unitSeries U) ^ i *
                  (unitSeries U + X * d⁄dX R (unitSeries U)))) := by
              congr 1
              ring
        _ = coeff i F *
            coeff n
              (unitInvSeries U ^ (n + 1) * (X * unitSeries U) ^ i *
                (unitSeries U + X * d⁄dX R (unitSeries U))) := by
              rw [PowerSeries.coeff_C_mul]
        _ = coeff i F * (if i = n then 1 else 0) := by
              rw [coeff_unit_monomial_kernel]
    calc
      ∑ x ∈ Finset.range (n + 1),
          coeff n
            (unitInvSeries U ^ (n + 1) *
              (C (coeff x F) * (X * unitSeries U) ^ x) *
              (unitSeries U + X * d⁄dX R (unitSeries U))) =
          coeff n
            (unitInvSeries U ^ (n + 1) *
              (C (coeff n F) * (X * unitSeries U) ^ n) *
              (unitSeries U + X * d⁄dX R (unitSeries U))) := by
        apply Finset.sum_eq_single n
        · intro i hi hne
          rw [hterm i, if_neg hne, mul_zero]
        · intro hnot
          exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_self n))).elim
      _ = coeff n F := by
        rw [hterm n]
        simp

theorem residue_subst_unit [Algebra ℚ R] (U : R⟦X⟧ˣ) (F : R⟦X⟧) (n : ℕ) :
    coeff n
        (unitInvSeries U ^ (n + 1) * F.subst (X * unitSeries U) *
          (unitSeries U + X * d⁄dX R (unitSeries U))) =
      coeff n F := by
  set_option backward.isDefEq.respectTransparency false in
    let G : R⟦X⟧ := X * unitSeries U
    let A : R⟦X⟧ := unitSeries U + X * d⁄dX R (unitSeries U)
    let tail : R⟦X⟧ := mk fun i => coeff (i + (n + 1)) F
    have hG : PowerSeries.HasSubst G := by
      simpa [G] using hasSubst_X_mul_unit (R := R) U
    have hsplit :
        F = X ^ (n + 1) * tail + ((trunc (n + 1) F : Polynomial R) : R⟦X⟧) := by
      simpa [tail] using PowerSeries.eq_X_pow_mul_shift_add_trunc (n + 1) F
    have hsubstF0 :
        F.subst G =
          (X ^ (n + 1) * tail +
              ((trunc (n + 1) F : Polynomial R) : R⟦X⟧)).subst G :=
      congrArg (fun H : R⟦X⟧ => H.subst G) hsplit
    have htail :
        coeff n (unitInvSeries U ^ (n + 1) * (X ^ (n + 1) * tail).subst G * A) = 0 := by
      rw [PowerSeries.subst_mul hG, PowerSeries.subst_pow hG, PowerSeries.subst_X hG]
      have hrewrite :
          unitInvSeries U ^ (n + 1) * (G ^ (n + 1) * tail.subst G) * A =
            X ^ (n + 1) *
              (unitInvSeries U ^ (n + 1) * unitSeries U ^ (n + 1) * tail.subst G * A) := by
        simp [G]
        rw [mul_pow]
        ring
      rw [hrewrite, PowerSeries.coeff_X_pow_mul']
      simp
    rw [hsubstF0, PowerSeries.subst_add hG]
    have hdist :
        unitInvSeries U ^ (n + 1) *
            ((X ^ (n + 1) * tail).subst G +
              (((trunc (n + 1) F : Polynomial R) : R⟦X⟧).subst G)) * A =
          unitInvSeries U ^ (n + 1) * (X ^ (n + 1) * tail).subst G * A +
            unitInvSeries U ^ (n + 1) *
              (((trunc (n + 1) F : Polynomial R) : R⟦X⟧).subst G) * A := by
      ring
    rw [hdist, map_add, htail]
    simp [G, A, residue_subst_unit_trunc (R := R) U F n]

theorem constantCoeff_subst_of_constantCoeff_zero (a f : R⟦X⟧)
    (ha : constantCoeff a = 0) :
    constantCoeff (f.subst a) = constantCoeff f := by
  have hSubst : PowerSeries.HasSubst a :=
    PowerSeries.HasSubst.of_constantCoeff_zero' ha
  rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst' hSubst f 0]
  rw [finsum_eq_single _ 0]
  · simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · intro d hd
    simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, ha, hd]

theorem lagrange_inversion [Algebra ℚ R] (φ : R⟦X⟧)
    (hφ : IsUnit (constantCoeff φ)) (n : ℕ) (hn : 0 < n) :
    (n : R) * coeff n (ImplicitSeries.implicitSeries φ) =
      coeff (n - 1) (φ ^ n) := by
  set_option backward.isDefEq.respectTransparency false in
    let T : R⟦X⟧ := ImplicitSeries.implicitSeries φ
    let V : R⟦X⟧ := φ.subst T
    have hT0 : constantCoeff T = 0 := by
      simp [T]
    have hVcc : constantCoeff V = constantCoeff φ := by
      simpa [V] using constantCoeff_subst_of_constantCoeff_zero (R := R) T φ hT0
    have hVunit : IsUnit V := by
      exact PowerSeries.isUnit_iff_constantCoeff.mpr (by simpa [hVcc] using hφ)
    let U : R⟦X⟧ˣ := hVunit.unit
    have hU : unitSeries U = V := by
      simp [U, unitSeries]
    have hTspec : T = X * V := by
      simpa [T, V] using ImplicitSeries.implicitSeries_spec (R := R) φ
    have hXU : X * unitSeries U = T := by
      rw [hU]
      exact hTspec.symm
    have hJac : unitSeries U + X * d⁄dX R (unitSeries U) = d⁄dX R T := by
      have h := congrArg (fun F : R⟦X⟧ => d⁄dX R F) hXU
      simpa [mul_assoc, mul_comm, mul_left_comm, add_comm] using h
    have hSubstT : PowerSeries.HasSubst T := by
      simpa [T] using ImplicitSeries.hasSubst_implicitSeries (R := R) φ
    have hsubstPowT : (φ ^ n).subst T = V ^ n := by
      simpa [T, V] using PowerSeries.subst_pow hSubstT φ n
    have hsubstPowU : (φ ^ n).subst (X * unitSeries U) = unitSeries U ^ n := by
      rw [hXU, hsubstPowT, ← hU]
    have hunitCancel : unitInvSeries U ^ n * unitSeries U ^ n = 1 := by
      simpa using unitInv_pow_mul_unit_pow (R := R) U (N := n) (d := n) le_rfl
    have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have hchange :=
      residue_subst_unit (R := R) U (φ ^ n) (n - 1)
    have hchange' : coeff (n - 1) (d⁄dX R T) = coeff (n - 1) (φ ^ n) := by
      simpa [hnsub, hsubstPowU, hJac, hunitCancel, mul_assoc] using hchange
    have hderCoeff : coeff (n - 1) (d⁄dX R T) = coeff n T * (n : R) := by
      have hcast : ((n - 1 : ℕ) : R) + 1 = (n : R) := by
        have hcastsum : ((n - 1 + 1 : ℕ) : R) = (n : R) := by
          exact congrArg (fun k : ℕ => (k : R)) hnsub
        simpa [Nat.cast_add] using hcastsum
      rw [PowerSeries.coeff_derivative, hnsub, hcast]
    calc
      (n : R) * coeff n (ImplicitSeries.implicitSeries φ) =
          coeff n T * (n : R) := by
        simp [T, mul_comm]
      _ = coeff (n - 1) (d⁄dX R T) := hderCoeff.symm
      _ = coeff (n - 1) (φ ^ n) := hchange'

theorem lagrange_inversion_divided [Algebra ℚ R] (φ : R⟦X⟧)
    (hφ : IsUnit (constantCoeff φ)) (n : ℕ) (hn : 0 < n) :
    coeff n (ImplicitSeries.implicitSeries φ) =
      algebraMap ℚ R ((n : ℚ)⁻¹) * coeff (n - 1) (φ ^ n) := by
  have hmain := lagrange_inversion (R := R) φ hφ n hn
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have hleftInv : algebraMap ℚ R ((n : ℚ)⁻¹) * (n : R) = 1 := by
    rw [← map_natCast (algebraMap ℚ R) n, ← map_mul]
    simp [hnq]
  calc
    coeff n (ImplicitSeries.implicitSeries φ) =
        (algebraMap ℚ R ((n : ℚ)⁻¹) * (n : R)) *
          coeff n (ImplicitSeries.implicitSeries φ) := by
      simp [hleftInv]
    _ = algebraMap ℚ R ((n : ℚ)⁻¹) *
        ((n : R) * coeff n (ImplicitSeries.implicitSeries φ)) := by
      ring
    _ = algebraMap ℚ R ((n : ℚ)⁻¹) * coeff (n - 1) (φ ^ n) := by
      rw [hmain]

end AnalyticCombinatorics.Ch1.Lagrange.Residue
end

/-!
# Applications of Lagrange inversion

This file records the Catalan and Cayley coefficient formulas obtained from
the formal Lagrange inversion theorem.
-/

noncomputable section

namespace Nat

export _root_ (catalan)

end Nat

namespace AnalyticCombinatorics.Ch1.Lagrange.Applications

open PowerSeries

private lemma coeff_exp_pow_rat (n k : ℕ) :
    coeff k ((PowerSeries.exp ℚ) ^ n) = (n : ℚ) ^ k / k.factorial := by
  rw [PowerSeries.exp_pow_eq_rescale_exp]
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  simp [div_eq_mul_inv]

private lemma inv_natCast_mul_pow_div_pred_factorial (n : ℕ) (hn : 0 < n) :
    (n : ℚ)⁻¹ * ((n : ℚ) ^ (n - 1) / (n - 1).factorial) =
      (n : ℚ) ^ (n - 1) / n.factorial := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hfact_nat : n.factorial = n * (n - 1).factorial := by
    calc
      n.factorial = ((n - 1) + 1).factorial := by rw [Nat.sub_add_cancel hn]
      _ = ((n - 1) + 1) * (n - 1).factorial := Nat.factorial_succ (n - 1)
      _ = n * (n - 1).factorial := by rw [Nat.sub_add_cancel hn]
  have hfact : (n.factorial : ℚ) = (n : ℚ) * ((n - 1).factorial : ℚ) := by
    exact_mod_cast hfact_nat
  rw [hfact]
  field_simp [hnq]

/--
The implicit solution of `T = X * exp T` has Cayley rooted-tree coefficients.
This matches the analytic coefficient formula in `TreeFunctionNS`.
-/
theorem coeff_implicitSeries_exp (n : ℕ) (hn : 0 < n) :
    coeff n (ImplicitSeries.implicitSeries (PowerSeries.exp ℚ)) =
      (n : ℚ) ^ (n - 1) / n.factorial := by
  have hunit : IsUnit (constantCoeff (PowerSeries.exp ℚ)) := by
    simp
  have hlag := Residue.lagrange_inversion_divided (R := ℚ)
    (PowerSeries.exp ℚ) hunit n hn
  have hcoeff : coeff (n - 1) ((PowerSeries.exp ℚ) ^ n) =
      (n : ℚ) ^ (n - 1) / (n - 1).factorial := by
    exact coeff_exp_pow_rat n (n - 1)
  rw [hcoeff] at hlag
  calc
    coeff n (ImplicitSeries.implicitSeries (PowerSeries.exp ℚ)) =
        (n : ℚ)⁻¹ * ((n : ℚ) ^ (n - 1) / (n - 1).factorial) := by
      simpa using hlag
    _ = (n : ℚ) ^ (n - 1) / n.factorial :=
      inv_natCast_mul_pow_div_pred_factorial n hn

end AnalyticCombinatorics.Ch1.Lagrange.Applications
end

/-!
# Ch2 §II.1 — Labelled structures and exponential generating functions

Flajolet & Sedgewick, Part A, Chapter II. A *labelled* class is again a graded
family of finite types (we reuse `CombClass`), but is enumerated by its
*exponential* generating function (EGF)

  `A(z) = ∑ₙ Aₙ zⁿ/n!`.

This file defines the EGF and two foundational flagships:
- permutations (`Perm (Fin n)`, `Aₙ = n!`) with EGF `1/(1 - z)`;
- the "set" class (one object of each size) with EGF `e^z`.

The labelled product (the defining feature of EGFs) is developed separately.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

@[simp] lemma coeff_egfSeq (a : ℕ → ℕ) (n : ℕ) :
    coeff n (egfSeq a) = (a n : ℚ) / (n.factorial : ℚ) := by
  rw [egfSeq, coeff_mk]

@[simp] lemma CombClass.coeff_egf (C : CombClass) (n : ℕ) :
    coeff n C.egf = (C.counts n : ℚ) / (n.factorial : ℚ) := by
  rw [CombClass.egf, coeff_egfSeq]

end AnalyticCombinatorics.Ch1

/-!
# Ch2 §II.1 — The labelled product

Flajolet & Sedgewick, Part A, Chapter II, the labelled (partitional) product, the
defining construction of the EGF framework. To form `A ⋆ B` on `n` labels, one
chooses which `k` of the labels go to the `A`-component (a `k`-subset) and puts an
`A`-structure on them and a `B`-structure on the remaining `n-k`. Hence

  `(A ⋆ B)ₙ = ∑_{k} C(n,k) · Aₖ · B_{n-k}`   (binomial convolution),

and therefore the EGFs multiply:

  **`(A ⋆ B)(z) = A(z) · B(z)`**   (F&S Theorem II.1).
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- Counting sequences convolve binomially: `(A ⋆ B)ₙ = ∑_k C(n,k)·Aₖ·B_{n-k}`. -/
@[simp] lemma CombClass.counts_lprod (A B : CombClass) (n : ℕ) :
    (A.lprod B).counts n
      = ∑ k : Fin (n + 1), n.choose k * A.counts k * B.counts (n - k) := by
  change Fintype.card
      (Σ k : Fin (n + 1), { S : Finset (Fin n) // S.card = k } × A.Obj k × B.Obj (n - k)) = _
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_finset_len, Fintype.card_fin]
  simp only [CombClass.counts]
  ring

/-- **Labelled product rule** (F&S Theorem II.1): `(A ⋆ B)(z) = A(z)·B(z)`. -/
theorem CombClass.egf_lprod (A B : CombClass) :
    (A.lprod B).egf = A.egf * B.egf := by
  ext n
  rw [CombClass.coeff_egf, CombClass.counts_lprod, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Fin.sum_univ_eq_sum_range
      (fun k => n.choose k * A.counts k * B.counts (n - k)) (n + 1),
    Nat.cast_sum, div_eq_iff (by exact_mod_cast Nat.factorial_ne_zero n), Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  have hk' : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hnk' : ((n - k).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - k)
  rw [CombClass.coeff_egf, CombClass.coeff_egf]
  field_simp
  rw [← Nat.choose_mul_factorial_mul_factorial hk]
  push_cast
  ring

end AnalyticCombinatorics.Ch1

/-!
# Ch2 §II.2 — The labelled set construction SET(C): counts layer

Flajolet & Sedgewick, Part A, Chapter II. `SET(C)` forms *sets* of labelled
C-objects (`C₀=∅`): a set partition of the `n` labels into blocks, each block
carrying a C-structure on its labels. Hence

  `SET(C)ₙ = ∑_{π : set partition of [n]} ∏_{B∈π} C_{|B|}`   (exponential formula),

and the EGF is `exp(C(z))`. This file builds the graded `Fintype` model and the
counting identity; the EGF identity is developed separately.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The counting identity for `SET(C)`: `SET(C)ₙ = ∑_π ∏_{B∈π} C_{|B|}`, from
`card_sigma`/`card_pi`. -/
lemma CombClass.counts_set (C : CombClass) (n : ℕ) :
    C.set.counts n
      = ∑ π : Finpartition (Finset.univ : Finset (Fin n)),
          ∏ B : π.parts, C.counts (B.val.card) := by
  classical
  change Fintype.card
      (Σ π : Finpartition (Finset.univ : Finset (Fin n)), ∀ B : π.parts, C.Obj (B.val.card)) = _
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Fintype.card_pi]
  rfl

end AnalyticCombinatorics.Ch1

/-!
# Ch2 §II.2 — ODE machinery for the labelled set construction

Toward the labelled set transfer `SET(C)(z) = exp(C(z))` (F&S §II.2). The strategy
(differential route): `exp(C(z))` and `SET(C)(z)` both satisfy the linear ODE
`F' = C'(z)·F` with constant term `1`, and that ODE has a unique solution. This file
proves the two *general* (combinatorics-free) ingredients:

* `subst_exp_ode` — `exp(C(z)) := (exp ℚ).subst C.egf` satisfies `F' = C'·F`
  (the chain rule `derivative_subst` + `derivative_exp`).
* `ode_unique` — a power series with `H' = G·H` and `H(0) = 0` is `0`.

The remaining (combinatorial) ingredient — that `SET(C).egf` satisfies the same ODE,
via a pointing bijection on set partitions — is developed separately.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- `exp(C(z))` (substituting `C.egf` for `X` in `e^X`) is a valid substitution when
`C₀ = ∅`. -/
lemma CombClass.hasSubst_egf {C : CombClass} (hC : C.counts 0 = 0) :
    HasSubst C.egf := by
  apply HasSubst.of_constantCoeff_zero'
  rw [← coeff_zero_eq_constantCoeff_apply, CombClass.coeff_egf, hC]
  simp

/-- `exp(C(z))` satisfies the linear ODE `F' = C'(z)·F`. -/
theorem CombClass.subst_exp_ode {C : CombClass} (hC : C.counts 0 = 0) :
    d⁄dX ℚ ((exp ℚ).subst C.egf) = d⁄dX ℚ C.egf * (exp ℚ).subst C.egf := by
  set_option backward.isDefEq.respectTransparency false in
    rw [derivative_subst (hg := CombClass.hasSubst_egf hC), derivative_exp]
    ring

/-- **ODE uniqueness**: a power series solving `H' = G·H` with vanishing constant term
is `0` (coefficient induction). -/
theorem ode_unique {R : Type*} [CommSemiring R] [Algebra ℚ R] {H G : R⟦X⟧}
    (hode : d⁄dX R H = G * H)
    (h0 : constantCoeff H = 0) : H = 0 := by
  have key : ∀ n, coeff n H = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      match n with
      | 0 => rw [coeff_zero_eq_constantCoeff_apply]; exact h0
      | m + 1 =>
        have hd := congrArg (coeff m) hode
        rw [coeff_derivative, coeff_mul,
          Finset.sum_eq_zero (fun p hp => ?_)] at hd
        · have hu : IsUnit ((m : R) + 1) := by
            simpa using
              (IsUnit.map (algebraMap ℚ R)
                (isUnit_iff_ne_zero.mpr (by positivity : ((m : ℚ) + 1) ≠ 0)))
          exact hu.mul_left_eq_zero.mp hd
        · rw [Finset.mem_antidiagonal] at hp
          rw [ih p.2 (by omega), mul_zero]
  ext n
  rw [key n, map_zero]

end AnalyticCombinatorics.Ch1

/-!
# Ch2 §II.2 — The labelled set ODE

This file contains the coefficient-level machinery for the differential equation
of the labelled set construction.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

lemma labelledSetObj_card (C : CombClass) (α : Type*) [Fintype α] [DecidableEq α] :
    Fintype.card (labelledSetObj C α) = C.set.counts (Fintype.card α) := by
  rw [← labelledSetObj_fin_card C (Fintype.card α)]
  exact Fintype.card_congr (labelledSetObjCongr C (Fintype.equivFin α))

lemma labelledSetObj_card_eq_setWeightFull (C : CombClass) (α : Type*) [Fintype α]
    [DecidableEq α] :
    Fintype.card (labelledSetObj C α) = setWeightFull C α := by
  change Fintype.card
      (Σ P : Finpartition (Finset.univ : Finset α), ∀ B : P.parts, C.Obj B.val.card) = _
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Fintype.card_pi]
  rfl

lemma setWeightFull_card (C : CombClass) (α : Type*) [Fintype α] [DecidableEq α] :
    setWeightFull C α = C.set.counts (Fintype.card α) := by
  rw [← labelledSetObj_card_eq_setWeightFull, labelledSetObj_card]

lemma prod_parts_sdiffSubtype (C : CombClass) {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) (Q : Finpartition ((Finset.univ : Finset α) \ B)) :
    (∏ A : (finpartitionSdiffSubtype B Q).parts, C.counts A.val.card) =
      ∏ A : Q.parts, C.counts A.val.card := by
  rw [Finset.prod_coe_sort (finpartitionSdiffSubtype B Q).parts
      (fun A : Finset {x : α // x ∉ B} => C.counts A.card),
    Finset.prod_coe_sort Q.parts (fun A : Finset α => C.counts A.card)]
  simp only [finpartitionSdiffSubtype, Finpartition.ofExistsUnique_parts]
  have hinj : ∀ A ∈ Q.parts, ∀ D ∈ Q.parts,
      A.subtype (fun x => x ∉ B) = D.subtype (fun x => x ∉ B) → A = D := by
    intro A hA D hD hsub
    ext x
    constructor
    · intro hx
      have hxnot : x ∉ B := by
        have hxcomp : x ∈ (Finset.univ : Finset α) \ B := Q.subset hA hx
        simpa using hxcomp
      have hxsub : (⟨x, hxnot⟩ : {x : α // x ∉ B}) ∈ A.subtype (fun x => x ∉ B) := by
        simpa using hx
      rw [hsub] at hxsub
      simpa using hxsub
    · intro hx
      have hxnot : x ∉ B := by
        have hxcomp : x ∈ (Finset.univ : Finset α) \ B := Q.subset hD hx
        simpa using hxcomp
      have hxsub : (⟨x, hxnot⟩ : {x : α // x ∉ B}) ∈ D.subtype (fun x => x ∉ B) := by
        simpa using hx
      rw [← hsub] at hxsub
      simpa using hxsub
  rw [Finset.prod_image hinj]
  refine Finset.prod_congr rfl fun A hA => ?_
  have hmap : (A.subtype (fun x => x ∉ B)).map
      (Function.Embedding.subtype fun x : α => x ∉ B) = A :=
    Finset.subtype_map_of_mem (fun x hx => by
      have hxcomp : x ∈ (Finset.univ : Finset α) \ B := Q.subset hA hx
      simpa using hxcomp)
  have hcard : (A.subtype (fun x => x ∉ B)).card = A.card := by
    rw [← Finset.card_map (Function.Embedding.subtype fun x : α => x ∉ B), hmap]
  rw [hcard]

lemma setWeightFinset_sdiff_eq_setWeightFull (C : CombClass) {α : Type*}
    [Fintype α] [DecidableEq α] (B : Finset α) :
    setWeightFinset C ((Finset.univ : Finset α) \ B) =
      setWeightFull C {x : α // x ∉ B} := by
  unfold setWeightFinset setWeightFull
  exact Fintype.sum_equiv (finpartitionSdiffSubtypeCongr B)
    (fun Q : Finpartition ((Finset.univ : Finset α) \ B) =>
      ∏ A : Q.parts, C.counts A.val.card)
    (fun Q : Finpartition (Finset.univ : Finset {x : α // x ∉ B}) =>
      ∏ A : Q.parts, C.counts A.val.card)
    (fun Q => (prod_parts_sdiffSubtype C B Q).symm)

lemma prod_parts_eq_root_mul_avoid (C : CombClass) {α : Type*} [DecidableEq α]
    {s B : Finset α} {P : Finpartition s} (hB : B ∈ P.parts) :
    (∏ A : P.parts, C.counts A.val.card) =
      C.counts B.card * ∏ A : (P.avoid B).parts, C.counts A.val.card := by
  rw [Finset.prod_coe_sort P.parts (fun A : Finset α => C.counts A.card),
    Finset.prod_coe_sort (P.avoid B).parts (fun A : Finset α => C.counts A.card)]
  have hparts : P.parts = insert B (P.avoid B).parts := by
    ext A
    by_cases hAB : A = B
    · subst hAB
      simp [Finpartition.mem_avoid_of_mem_part hB, hB]
    · simp [Finpartition.mem_avoid_of_mem_part hB, hAB]
  have hBnot : B ∉ (P.avoid B).parts := by
    simp [Finpartition.mem_avoid_of_mem_part hB]
  rw [hparts, Finset.prod_insert hBnot]

lemma setWeightFull_root (C : CombClass) {α : Type*} [Fintype α] [DecidableEq α]
    (r : α) :
    setWeightFull C α =
      ∑ B : {B : Finset α // r ∈ B},
        C.counts B.val.card * setWeightFull C {x : α // x ∉ B.val} := by
  classical
  unfold setWeightFull
  let block : Finpartition (Finset.univ : Finset α) → {B : Finset α // r ∈ B} :=
    fun P => ⟨P.part r, by simpa using P.mem_part (by simp)⟩
  let w : Finpartition (Finset.univ : Finset α) → ℕ :=
    fun P => ∏ A : P.parts, C.counts A.val.card
  have hsplit :
      ∑ P : Finpartition (Finset.univ : Finset α), w P =
        ∑ x : (Σ B : {B : Finset α // r ∈ B}, {P // block P = B}), w x.2.val := by
    symm
    exact Fintype.sum_equiv (Equiv.sigmaFiberEquiv block)
      (fun x : (Σ B : {B : Finset α // r ∈ B}, {P // block P = B}) => w x.2.val)
      w
      (by intro x; rfl)
  rw [hsplit, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun B _ => ?_
  let fiberEquiv :
      {P : Finpartition (Finset.univ : Finset α) // block P = B} ≃
        {P : Finpartition (Finset.univ : Finset α) // P.part r = B.val} :=
    { toFun := fun P => ⟨P.val, by
        have h := congrArg Subtype.val P.property
        exact h⟩
      invFun := fun P => ⟨P.val, by
        apply Subtype.ext
        exact P.property⟩
      left_inv := by
        intro P
        apply Subtype.ext
        rfl
      right_inv := by
        intro P
        apply Subtype.ext
        rfl }
  let rootEquiv := finpartitionRootFiberEquiv r B.property
  have hfiber :
      ∑ P : {P : Finpartition (Finset.univ : Finset α) // block P = B}, w P.val =
        ∑ Q : Finpartition ((Finset.univ : Finset α) \ B.val),
          C.counts B.val.card * ∏ A : Q.parts, C.counts A.val.card := by
    calc
      ∑ P : {P : Finpartition (Finset.univ : Finset α) // block P = B}, w P.val
          = ∑ P : {P : Finpartition (Finset.univ : Finset α) // P.part r = B.val},
              w P.val := by
            exact Fintype.sum_equiv fiberEquiv
              (fun P => w P.val) (fun P => w P.val) (by intro P; rfl)
      _ = ∑ Q : Finpartition ((Finset.univ : Finset α) \ B.val),
              w ((rootEquiv.symm Q).val) := by
            exact Fintype.sum_equiv rootEquiv
              (fun P => w P.val)
              (fun Q => w ((rootEquiv.symm Q).val))
              (by intro P; simp)
      _ = ∑ Q : Finpartition ((Finset.univ : Finset α) \ B.val),
              C.counts B.val.card * ∏ A : Q.parts, C.counts A.val.card := by
            refine Finset.sum_congr rfl fun Q _ => ?_
            have hruniv : r ∈ (Finset.univ : Finset α) := by simp
            have hBmem : B.val ∈ (rootEquiv.symm Q).val.parts := by
              have hprop := (rootEquiv.symm Q).property
              simpa [hprop] using (rootEquiv.symm Q).val.part_mem.2 hruniv
            change (∏ A : (rootEquiv.symm Q).val.parts, C.counts A.val.card) =
              C.counts B.val.card * ∏ A : Q.parts, C.counts A.val.card
            rw [prod_parts_eq_root_mul_avoid C hBmem]
            have havoid : (rootEquiv.symm Q).val.avoid B.val = Q := by
              exact Equiv.apply_symm_apply rootEquiv Q
            rw [havoid]
  rw [hfiber]
  rw [← Finset.mul_sum]
  change C.counts B.val.card * setWeightFinset C ((Finset.univ : Finset α) \ B.val) =
    C.counts B.val.card * setWeightFull C {x : α // x ∉ B.val}
  rw [setWeightFinset_sdiff_eq_setWeightFull]

@[simp] lemma rootBlockEquiv_card (n : ℕ) (S : Finset (Fin n)) :
    (rootBlockEquiv n S).val.card = S.card + 1 := by
  simp [rootBlockEquiv]

lemma rootBlockEquiv_compl_card (n : ℕ) (S : Finset (Fin n)) :
    Fintype.card {x : Fin (n + 1) // x ∉ (rootBlockEquiv n S).val} = n - S.card := by
  rw [Fintype.card_subtype]
  have hset : ({x | x ∉ (rootBlockEquiv n S).val} : Finset (Fin (n + 1))) =
      (Finset.univ : Finset (Fin (n + 1))) \ (rootBlockEquiv n S).val := by
    ext x
    simp
  rw [hset, Finset.card_sdiff_of_subset (by simp), Finset.card_univ, Fintype.card_fin,
    rootBlockEquiv_card]
  omega

lemma sum_finset_by_card (n : ℕ) (f : ℕ → ℕ) :
    (∑ S : Finset (Fin n), f S.card) =
      ∑ k : Fin (n + 1), n.choose (k : ℕ) * f (k : ℕ) := by
  classical
  let len : Finset (Fin n) → Fin (n + 1) := fun S =>
    ⟨S.card, by
      exact Nat.lt_succ_of_le (by simpa [Fintype.card_fin] using S.card_le_univ)⟩
  have hsplit :
      (∑ S : Finset (Fin n), f S.card) =
        ∑ x : (Σ k : Fin (n + 1), {S : Finset (Fin n) // len S = k}), f x.2.val.card := by
    symm
    exact Fintype.sum_equiv (Equiv.sigmaFiberEquiv len)
      (fun x : (Σ k : Fin (n + 1), {S : Finset (Fin n) // len S = k}) =>
        f x.2.val.card)
      (fun S : Finset (Fin n) => f S.card)
      (by intro x; rfl)
  rw [hsplit, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hcard :
      Fintype.card {S : Finset (Fin n) // len S = k} = n.choose (k : ℕ) := by
    have hcard' :
        Fintype.card {S : Finset (Fin n) // len S = k} =
          (Fintype.card (Fin n)).choose (k : ℕ) := by
      rw [← Fintype.card_finset_len (α := Fin n) (k := (k : ℕ))]
      exact Fintype.card_congr
        { toFun := fun S => ⟨S.val, by
            have h := congrArg Fin.val S.property
            exact h⟩
          invFun := fun S => ⟨S.val, by
            apply Fin.ext
            exact S.property⟩
          left_inv := by intro S; apply Subtype.ext; rfl
          right_inv := by intro S; apply Subtype.ext; rfl }
    simpa [Fintype.card_fin] using hcard'
  trans Fintype.card {S : Finset (Fin n) // len S = k} * f (k : ℕ)
  · rw [← Finset.card_univ, Finset.sum_eq_card_nsmul]
    · rw [nsmul_eq_mul]
      refine congrArg (fun m => m * f (k : ℕ)) rfl
    · intro S _hS
      have h := congrArg Fin.val S.property
      simpa using congrArg f h
  · rw [hcard]

lemma CombClass.counts_set_succ (C : CombClass) (n : ℕ) :
    C.set.counts (n + 1)
      = ∑ i : Fin (n + 1),
          n.choose (i : ℕ) * C.counts ((i : ℕ) + 1) *
            C.set.counts (n - (i : ℕ)) := by
  classical
  conv_lhs => rw [show n + 1 = Fintype.card (Fin (n + 1)) by simp]
  rw [← setWeightFull_card C (Fin (n + 1))]
  rw [setWeightFull_root C (Fin.last n)]
  have hblocks :
      (∑ B : {B : Finset (Fin (n + 1)) // Fin.last n ∈ B},
          C.counts B.val.card * setWeightFull C {x : Fin (n + 1) // x ∉ B.val})
        =
      ∑ S : Finset (Fin n),
        C.counts (S.card + 1) * C.set.counts (n - S.card) := by
    symm
    exact Fintype.sum_equiv (rootBlockEquiv n)
      (fun S : Finset (Fin n) =>
        C.counts (S.card + 1) * C.set.counts (n - S.card))
      (fun B : {B : Finset (Fin (n + 1)) // Fin.last n ∈ B} =>
        C.counts B.val.card * setWeightFull C {x : Fin (n + 1) // x ∉ B.val})
      (by
        intro S
        change C.counts (S.card + 1) * C.set.counts (n - S.card) =
          C.counts ((rootBlockEquiv n S).val.card) *
            setWeightFull C {x : Fin (n + 1) // x ∉ (rootBlockEquiv n S).val}
        rw [rootBlockEquiv_card, setWeightFull_card,
          rootBlockEquiv_compl_card])
  rw [hblocks]
  rw [sum_finset_by_card n (fun k => C.counts (k + 1) * C.set.counts (n - k))]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Nat.mul_assoc]

/-- The EGF of the derivative class is the formal derivative of the EGF. -/
theorem CombClass.egf_deriv (C : CombClass) :
    C.deriv.egf = d⁄dX ℚ C.egf := by
  ext n
  rw [CombClass.coeff_egf, CombClass.counts_deriv, coeff_derivative,
    CombClass.coeff_egf]
  have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hnf : ((n.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [Nat.factorial_succ, hn, hnf]
  rw [Nat.factorial_succ]
  push_cast
  ring_nf

/-- The pointed SET recurrence is exactly the labelled product `C' ⋆ SET(C)`. -/
theorem CombClass.egf_set_deriv_lprod (C : CombClass) :
    C.set.deriv.egf = (C.deriv.lprod C.set).egf := by
  ext n
  rw [CombClass.coeff_egf, CombClass.counts_deriv, CombClass.counts_set_succ,
    CombClass.coeff_egf, CombClass.counts_lprod]
  simp [CombClass.counts_deriv]

/-- The labelled SET construction satisfies `SET(C)' = C' * SET(C)`. -/
theorem CombClass.egf_set_ode (C : CombClass) :
    d⁄dX ℚ C.set.egf = d⁄dX ℚ C.egf * C.set.egf := by
  calc
    d⁄dX ℚ C.set.egf = C.set.deriv.egf := (CombClass.egf_deriv C.set).symm
    _ = (C.deriv.lprod C.set).egf := CombClass.egf_set_deriv_lprod C
    _ = C.deriv.egf * C.set.egf := CombClass.egf_lprod C.deriv C.set
    _ = d⁄dX ℚ C.egf * C.set.egf := by rw [CombClass.egf_deriv C]

end AnalyticCombinatorics.Ch1

/-!
# Ch2 §II.2 — The labelled set exponential formula

This file closes the labelled SET construction:
`SET(C)(z) = exp(C(z))` when `C` has no size-zero objects.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

lemma CombClass.counts_set_zero (C : CombClass) : C.set.counts 0 = 1 := by
  classical
  rw [CombClass.counts_set]
  have huniv : (Finset.univ : Finset (Fin 0)) = (⊥ : Finset (Fin 0)) := by
    simp
  rw [huniv]
  rw [Fintype.sum_unique]
  simp

theorem CombClass.egf_set (C : CombClass) (hC : C.counts 0 = 0) :
    C.set.egf = (PowerSeries.exp ℚ).subst C.egf := by
  let H : ℚ⟦X⟧ := C.set.egf - (PowerSeries.exp ℚ).subst C.egf
  have hode : d⁄dX ℚ H = d⁄dX ℚ C.egf * H := by
    dsimp [H]
    rw [map_sub, CombClass.egf_set_ode, CombClass.subst_exp_ode hC]
    set_option backward.isDefEq.respectTransparency false in
      ring
  have h0C : constantCoeff C.egf = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, CombClass.coeff_egf, hC]
    simp
  have h0set : constantCoeff C.set.egf = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, CombClass.coeff_egf,
      CombClass.counts_set_zero]
    simp
  have h0subst : constantCoeff ((PowerSeries.exp ℚ).subst C.egf) = 1 := by
    change MvPowerSeries.constantCoeff (PowerSeries.subst C.egf (PowerSeries.exp ℚ)) = 1
    rw [constantCoeff_subst (CombClass.hasSubst_egf hC)]
    rw [finsum_eq_single _ 0]
    · simp
    · intro d hd
      have hpow : MvPowerSeries.constantCoeff (C.egf ^ d) = 0 := by
        change constantCoeff (C.egf ^ d) = 0
        rw [map_pow, h0C, zero_pow hd]
      set_option backward.isDefEq.respectTransparency false in
        rw [hpow, smul_zero]
  have h0 : constantCoeff H = 0 := by
    dsimp [H]
    rw [map_sub, h0set, h0subst, sub_self]
  have hH : H = 0 := ode_unique hode h0
  exact sub_eq_zero.mp hH

end AnalyticCombinatorics.Ch1

/-!
# Rooted labelled trees as a recursive species, and Cayley's formula via Lagrange

We define a genuine recursive *rooted labelled tree* species object

  `RootedLTree n = root label + SET(rooted subtrees on a partition of the rest)`

and show its EGF satisfies `T = X · exp(T)`. By `implicitSeries_unique` and the
banked Lagrange coefficient `coeff_implicitSeries_exp`, the count is `n^{n-1}`,
matching the banked `cayleyRootedTree` (for `0 < n`).

This is the faithful species route to Cayley's coefficient — no Prüfer code.
-/

noncomputable section

open AnalyticCombinatorics.Ch1
open PowerSeries
open scoped BigOperators

namespace AnalyticCombinatorics.Ch7.SingularityApp.RootedLTreeNS

/-! ## The recursive Fintype (the one real engineering lemma) -/

/-! ## The species class and its functional equation -/

@[simp] lemma rootedLTreeClass_counts_zero :
    rootedLTreeClass.counts 0 = 0 := by
  rw [rootedLTreeClass_counts, Fintype.card_eq_zero_iff]
  exact ⟨fun t => rootedLTreeZeroEquiv t |>.elim⟩

/-- `counts (n+1) = (n+1) · (SET rootedLTreeClass).counts n`. -/
lemma rootedLTreeClass_counts_succ (n : ℕ) :
    rootedLTreeClass.counts (n + 1) =
      (n + 1) * rootedLTreeClass.set.counts n := by
  classical
  rw [rootedLTreeClass_counts, Fintype.card_congr (decompEquiv n), Fintype.card_sigma]
  have hterm : ∀ r : Fin (n + 1),
      Fintype.card (labelledSetObj rootedLTreeClass {x : Fin (n + 1) // x ≠ r})
        = rootedLTreeClass.set.counts n := by
    intro r
    rw [labelledSetObj_card rootedLTreeClass {x : Fin (n + 1) // x ≠ r},
      fin_compl_ne_card n r]
  rw [Finset.sum_congr rfl (fun r _ => hterm r)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- The rooted-tree EGF is `X` times the EGF of its SET-of-subtrees. -/
lemma rootedLTreeClass_egf_eq_X_mul_set :
    rootedLTreeClass.egf = X * rootedLTreeClass.set.egf := by
  ext n
  cases n with
  | zero =>
      rw [CombClass.coeff_egf, rootedLTreeClass_counts_zero]
      simp
  | succ m =>
      rw [CombClass.coeff_egf, rootedLTreeClass_counts_succ,
        PowerSeries.coeff_succ_X_mul, CombClass.coeff_egf]
      rw [Nat.factorial_succ]
      push_cast
      have hm : ((m.factorial : ℚ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
      have hm1 : ((m : ℚ) + 1) ≠ 0 := by positivity
      field_simp

/-- Functional equation: `T = X · exp(T)`. -/
lemma rootedLTreeClass_egf_spec :
    rootedLTreeClass.egf = X * (PowerSeries.exp ℚ).subst rootedLTreeClass.egf := by
  conv_lhs => rw [rootedLTreeClass_egf_eq_X_mul_set]
  rw [CombClass.egf_set rootedLTreeClass rootedLTreeClass_counts_zero]

lemma constantCoeff_rootedLTreeClass_egf :
    constantCoeff rootedLTreeClass.egf = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, CombClass.coeff_egf,
    rootedLTreeClass_counts_zero]
  simp

/-! ## Cayley's coefficient via Lagrange inversion -/

lemma rootedLTreeClass_egf_eq_implicitSeries_exp :
    rootedLTreeClass.egf =
      AnalyticCombinatorics.Ch1.Lagrange.ImplicitSeries.implicitSeries
        (PowerSeries.exp ℚ) :=
  AnalyticCombinatorics.Ch1.Lagrange.ImplicitSeries.implicitSeries_unique
    (PowerSeries.exp ℚ) rootedLTreeClass.egf
    rootedLTreeClass_egf_spec constantCoeff_rootedLTreeClass_egf

lemma rootedLTreeClass_coeff_eq_cayley (n : ℕ) (hn : 0 < n) :
    coeff n rootedLTreeClass.egf = (n : ℚ) ^ (n - 1) / n.factorial := by
  rw [rootedLTreeClass_egf_eq_implicitSeries_exp]
  exact AnalyticCombinatorics.Ch1.Lagrange.Applications.coeff_implicitSeries_exp n hn

end AnalyticCombinatorics.Ch7.SingularityApp.RootedLTreeNS
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch7 AnalyticCombinatorics.Ch7.SingularityApp AnalyticCombinatorics.Ch7.SingularityApp.RootedLTreeNS
open AnalyticCombinatorics.Ch1
open PowerSeries
open scoped BigOperators
theorem solution (n : ℕ) (hn : 0 < n) :
    rootedLTreeClass.counts n = n ^ (n - 1) := by
  have h := rootedLTreeClass_coeff_eq_cayley n hn
  rw [CombClass.coeff_egf] at h
  have hfac : ((n.factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hmul : (rootedLTreeClass.counts n : ℚ) = (n : ℚ) ^ (n - 1) := by
    field_simp at h
    linarith [h]
  exact_mod_cast hmul
