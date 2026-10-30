-- Prove2me | solution 1 for AnalyticCombinatorics.Ch1.Lagrange.Applications.coeff_implicitSeries_one_add_X_sq
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T11:36:43.312545+00:00
-- url     : https://prove2.me/submissions/d3088ff7-57a3-499d-ba99-0336731cdb3e

import Definitions.Def_AnalyticCombinatorics_Ch1_Lagrange_ImplicitSeries
import Definitions.Def_AnalyticCombinatorics_Ch1_Lagrange_Residue
import Mathlib

namespace AnalyticCombinatorics.Ch1.Lagrange.Applications end AnalyticCombinatorics.Ch1.Lagrange.Applications

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

private lemma nat_mul_catalan_eq_choose_pred (n : ℕ) (hn : 0 < n) :
    n * Nat.catalan n = (2 * n).choose (n - 1) := by
  apply Nat.mul_left_cancel (Nat.succ_pos n)
  calc
    (n + 1) * (n * Nat.catalan n) = n * ((n + 1) * Nat.catalan n) := by ring
    _ = n * n.centralBinom := by rw [succ_mul_catalan_eq_centralBinom]
    _ = (2 * n).choose (n - 1) * (n + 1) := by
      have hchoose := Nat.choose_succ_right_eq (2 * n) (n - 1)
      have hsucc : n - 1 + 1 = n := Nat.sub_add_cancel hn
      have hsub : 2 * n - (n - 1) = n + 1 := by omega
      rw [hsucc, hsub] at hchoose
      simpa [Nat.centralBinom, mul_comm, mul_left_comm, mul_assoc] using hchoose
    _ = (n + 1) * ((2 * n).choose (n - 1)) := by ring

private lemma inv_natCast_mul_choose_pred_eq_catalan (n : ℕ) (hn : 0 < n) :
    (n : ℚ)⁻¹ * (((2 * n).choose (n - 1) : ℕ) : ℚ) = (Nat.catalan n : ℚ) := by
  have hnat := nat_mul_catalan_eq_choose_pred n hn
  have hq : (n : ℚ) * (Nat.catalan n : ℚ) =
      (((2 * n).choose (n - 1) : ℕ) : ℚ) := by
    exact_mod_cast hnat
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  calc
    (n : ℚ)⁻¹ * (((2 * n).choose (n - 1) : ℕ) : ℚ) =
        (n : ℚ)⁻¹ * ((n : ℚ) * (Nat.catalan n : ℚ)) := by rw [← hq]
    _ = (Nat.catalan n : ℚ) := by field_simp [hnq]

private lemma coeff_one_add_X_pow_rat (m k : ℕ) :
    coeff k ((1 + X : ℚ⟦X⟧) ^ m) = (((m.choose k : ℕ) : ℚ)) := by
  set_option backward.isDefEq.respectTransparency false in
    have hright : ((1 + X : ℚ⟦X⟧) ^ m) =
        ((((1 : Polynomial ℚ) + Polynomial.X) ^ m : Polynomial ℚ) : ℚ⟦X⟧) := by
      simp
    rw [hright, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

end AnalyticCombinatorics.Ch1.Lagrange.Applications
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch1 AnalyticCombinatorics.Ch1.Lagrange AnalyticCombinatorics.Ch1.Lagrange.Applications
open PowerSeries
theorem solution (n : ℕ) (hn : 0 < n) :
    coeff n (ImplicitSeries.implicitSeries ((1 + X)^2 : ℚ⟦X⟧)) = Nat.catalan n := by
  have hunit : IsUnit (constantCoeff (((1 + X) ^ 2 : ℚ⟦X⟧))) := by
    simp
  have hlag := Residue.lagrange_inversion_divided (R := ℚ)
    (((1 + X) ^ 2 : ℚ⟦X⟧)) hunit n hn
  have hcoeff : coeff (n - 1) ((((1 + X) ^ 2 : ℚ⟦X⟧) ^ n)) =
      (((2 * n).choose (n - 1) : ℕ) : ℚ) := by
    have hpow : ((((1 + X) ^ 2 : ℚ⟦X⟧) ^ n) = (1 + X : ℚ⟦X⟧) ^ (2 * n)) := by
      rw [pow_mul]
    rw [hpow]
    exact coeff_one_add_X_pow_rat (2 * n) (n - 1)
  rw [hcoeff] at hlag
  calc
    coeff n (ImplicitSeries.implicitSeries ((1 + X)^2 : ℚ⟦X⟧)) =
        (n : ℚ)⁻¹ * (((2 * n).choose (n - 1) : ℕ) : ℚ) := by
      simpa using hlag
    _ = (Nat.catalan n : ℚ) := inv_natCast_mul_choose_pred_eq_catalan n hn
