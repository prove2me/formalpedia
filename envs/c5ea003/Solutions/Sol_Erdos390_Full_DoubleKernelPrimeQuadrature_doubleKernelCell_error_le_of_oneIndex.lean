-- Prove2me | solution 1 for Erdos390.Full.DoubleKernelPrimeQuadrature.doubleKernelCell_error_le_of_oneIndex
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T14:54:32.878643+00:00
-- url     : https://prove2.me/submissions/5dc9348d-fce9-4466-94b1-f92d15f7eaa9

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_004

/- Source module: Erdos390.Full.ConditionedPoissonLimit -/
section


/-!
# Exact analytic identities for the Poisson--Dickman bridge

This file continues the explicit finite-cutoff construction in
`ConditionedPoisson`.  The first layer below isolates the identities which
are needed by the covariance operator and proves them directly from the
method-of-steps Dickman equation.  In particular, the fact that the scale
function `t` is a null direction is not postulated.

The probability-theoretic exact-total projective limit is kept separate from
these analytic identities: this prevents a choice of a regular conditional
law on a null fibre from silently entering the operator calculation.
-/

open Filter Set
open scoped Interval BigOperators ENNReal NNReal

noncomputable section

namespace Erdos390.Full.ConditionedPoissonLimit

open MeasureTheory ProbabilityTheory Real
open DickmanBasic

/-! ## A global method-of-steps Dickman function -/













































































lemma covarianceKernel_comm (s t : ℝ) :
    covarianceKernel s t = covarianceKernel t s := by
  unfold covarianceKernel
  rw [add_comm]
  ring

















/-! ## Density-weighted Palm moments and covariance -/



lemma continuous_covarianceKernel :
    Continuous (Function.uncurry covarianceKernel) := by
  unfold covarianceKernel Function.uncurry
  exact (continuous_F.comp (continuous_fst.add continuous_snd)).sub
    ((continuous_F.comp continuous_fst).mul (continuous_F.comp continuous_snd))

/-! ## The removable axis singularity and a continuous kernel representative -/

















































/-! ## The measurable Cauchy endpoint of the kernel argument -/





/-! The Palm argument produces additivity first on the positive triangle.
The following deterministic lemma records that no global Cauchy equation is
needed: continuity on the closed unit interval and local additivity already
force one common slope. -/







end Erdos390.Full.ConditionedPoissonLimit

end

/- Source module: Erdos390.Full.KernelPrimeQuadrature -/
section


/-!
# Weighted prime quadrature for the Poisson--Dickman kernel

This file generalizes the scalar Abel summation used for `H_j` to a smooth
test function on logarithmic prime coordinates.  The first layer is an exact
finite identity for the actual primes; later declarations specialize it to
the Poisson--Dickman covariance kernel and its compact derivative bounds.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.KernelPrimeQuadrature

open MeasureTheory
open ArithmeticModel PrimeSums PrimeBandQuadrature
open DickmanBasic ConditionedPoissonLimit













lemma continuous_covarianceKernel_left (s : ℝ) :
    Continuous (covarianceKernel s) := by
  exact continuous_covarianceKernel.comp
    (continuous_const.prodMk continuous_id)





lemma realLogCoordinate_mem_unit {z x : ℝ}
    (hz : 1 < z) (hx : 1 ≤ x) (hxz : x ≤ z) :
    realLogCoordinate z x ∈ Icc (0 : ℝ) 1 := by
  have hlogzpos : 0 < Real.log z := Real.log_pos hz
  have hlogxnonneg : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlogxz : Real.log x ≤ Real.log z :=
    Real.log_le_log (zero_lt_one.trans_le hx) hxz
  unfold realLogCoordinate
  constructor
  · exact div_nonneg hlogxnonneg hlogzpos.le
  · exact (div_le_one hlogzpos).2 hlogxz





































































end Erdos390.Full.KernelPrimeQuadrature

end

/- Source module: Erdos390.Full.DoubleKernelPrimeQuadrature -/
section


/-!
# Double-index prime quadrature for the Poisson--Dickman kernel

This module performs the two prime-index quadratures needed in the
positive-cell part of Lemma 8.4.  The constants are chosen once, before the
kernel coordinate, ambient scale, or moving endpoints.  The moving-low-cell
estimates are kept for the next layer; no lower endpoint tending to zero is
hidden in the positive-cell theorem below.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.DoubleKernelPrimeQuadrature

open MeasureTheory
open ArithmeticModel PrimeSums PrimeBandQuadrature
open DickmanBasic ConditionedPoissonLimit
open KernelPrimeQuadrature
open PoissonDickmanKernelBounds
open PositiveCellTransfer







lemma mem_intervalPrimes_iff {A Y p : ℕ} :
    p ∈ intervalPrimes A Y ↔ p.Prime ∧ A < p ∧ p ≤ Y := by
  unfold intervalPrimes
  rw [Finset.mem_sdiff]
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨_hpzero, hpY⟩, hpPrime⟩, hpNotA⟩
    refine ⟨hpPrime, ?_, hpY⟩
    by_contra hnot
    exact hpNotA ⟨⟨Nat.zero_le p, Nat.le_of_not_gt hnot⟩, hpPrime⟩
  · rintro ⟨hpPrime, hpA, hpY⟩
    refine ⟨⟨⟨Nat.zero_le p, hpY⟩, hpPrime⟩, ?_⟩
    rintro ⟨⟨_hpzero, hpA'⟩, _hpPrime⟩
    exact (Nat.not_lt_of_ge hpA') hpA

private lemma primesUpTo_mono {A Y : ℕ} (hAY : A ≤ Y) :
    primesUpTo A ⊆ primesUpTo Y := by
  intro p hp
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.trans hAY⟩, hp.2⟩

lemma primeCellOperator_eq_sum (z : ℝ) {A Y : ℕ} (hAY : A ≤ Y)
    (f : ℝ → ℝ) :
    primeCellOperator z A Y f =
      ∑ p ∈ intervalPrimes A Y,
        f (realLogCoordinate z (p : ℝ)) / (p : ℝ) := by
  have hsub := primesUpTo_mono hAY
  have hsum := Finset.sum_sdiff hsub
    (f := fun p : ℕ => f (realLogCoordinate z (p : ℝ)) / (p : ℝ))
  unfold primeCellOperator fullWeightedReciprocalSum intervalPrimes
  exact ((eq_sub_iff_add_eq).2 hsum).symm

lemma intervalPrime_pos {A Y p : ℕ} (hp : p ∈ intervalPrimes A Y) :
    0 < p := by
  exact (mem_intervalPrimes_iff.mp hp).1.pos

lemma primeCellOperator_sub (z : ℝ) {A Y : ℕ} (hAY : A ≤ Y)
    (f g : ℝ → ℝ) :
    primeCellOperator z A Y (fun t => f t - g t) =
      primeCellOperator z A Y f - primeCellOperator z A Y g := by
  rw [primeCellOperator_eq_sum z hAY,
    primeCellOperator_eq_sum z hAY,
    primeCellOperator_eq_sum z hAY]
  simp_rw [sub_div]
  simp only [Finset.sum_sub_distrib]

/-- A uniform pointwise bound controls the actual prime-cell operator by
the exact harmonic mass of that cell. -/
lemma abs_primeCellOperator_le (z : ℝ) {A Y : ℕ} (hAY : A ≤ Y)
    (f : ℝ → ℝ) {e : ℝ}
    (hbound : ∀ p ∈ intervalPrimes A Y,
      |f (realLogCoordinate z (p : ℝ))| ≤ e) :
    |primeCellOperator z A Y f| ≤
      e * (fullReciprocalSum Y - fullReciprocalSum A) := by
  rw [primeCellOperator_eq_sum z hAY]
  calc
    |∑ p ∈ intervalPrimes A Y,
        f (realLogCoordinate z (p : ℝ)) / (p : ℝ)| ≤
      ∑ p ∈ intervalPrimes A Y,
        |f (realLogCoordinate z (p : ℝ)) / (p : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ intervalPrimes A Y, e / (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpR : (0 : ℝ) < p := by exact_mod_cast intervalPrime_pos hp
      rw [abs_div, abs_of_pos hpR]
      exact div_le_div_of_nonneg_right (hbound p hp) hpR.le
    _ = e * (fullReciprocalSum Y - fullReciprocalSum A) := by
      have hsub := primesUpTo_mono hAY
      have hsum := Finset.sum_sdiff hsub (f := fun p : ℕ => 1 / (p : ℝ))
      have hcell :
          (∑ p ∈ intervalPrimes A Y, 1 / (p : ℝ)) =
            fullReciprocalSum Y - fullReciprocalSum A := by
        unfold intervalPrimes fullReciprocalSum
        exact (eq_sub_iff_add_eq).2 hsum
      calc
        (∑ p ∈ intervalPrimes A Y, e / (p : ℝ)) =
            e * ∑ p ∈ intervalPrimes A Y, 1 / (p : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          ring
        _ = e * (fullReciprocalSum Y - fullReciprocalSum A) := by
          rw [hcell]

/-- Finite prime summation commutes exactly with a parameter integral. -/
lemma primeCellOperator_intervalIntegral
    (z : ℝ) {A Y : ℕ} (hAY : A ≤ Y)
    {a b : ℝ} (g : ℝ → ℝ → ℝ)
    (hint : ∀ p ∈ intervalPrimes A Y,
      IntervalIntegrable (g (realLogCoordinate z (p : ℝ))) volume a b) :
    primeCellOperator z A Y (fun s => ∫ t in a..b, g s t) =
      ∫ t in a..b, primeCellOperator z A Y (fun s => g s t) := by
  rw [primeCellOperator_eq_sum z hAY]
  calc
    (∑ p ∈ intervalPrimes A Y,
        (∫ t in a..b, g (realLogCoordinate z (p : ℝ)) t) / (p : ℝ)) =
      ∑ p ∈ intervalPrimes A Y,
        ∫ t in a..b, g (realLogCoordinate z (p : ℝ)) t / (p : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [intervalIntegral.integral_div]
    _ = ∫ t in a..b,
        ∑ p ∈ intervalPrimes A Y,
          g (realLogCoordinate z (p : ℝ)) t / (p : ℝ) := by
      symm
      apply intervalIntegral.integral_finset_sum
      intro p hp
      exact (hint p hp).div_const (p : ℝ)
    _ = ∫ t in a..b, primeCellOperator z A Y (fun s => g s t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      change (∑ p ∈ intervalPrimes A Y,
        g (realLogCoordinate z (p : ℝ)) t / (p : ℝ)) =
          primeCellOperator z A Y (fun s => g s t)
      rw [primeCellOperator_eq_sum z hAY]





/-- A pointwise bound on a continuum cell gives the exact harmonic-coordinate
length as its operator norm. -/
lemma abs_continuumCellOperator_le
    (z : ℝ) {A Y : ℕ} (hz : 1 < z) (hA : 2 ≤ A) (hAY : A ≤ Y)
    (f : ℝ → ℝ) {e : ℝ}
    (hint : IntervalIntegrable (fun t => f t / t) volume
      (realLogCoordinate z (A : ℝ)) (realLogCoordinate z (Y : ℝ)))
    (hbound : ∀ t ∈ Icc (realLogCoordinate z (A : ℝ))
      (realLogCoordinate z (Y : ℝ)), |f t| ≤ e) :
    |continuumCellOperator z A Y f| ≤
      e * (Real.log (realLogCoordinate z (Y : ℝ)) -
        Real.log (realLogCoordinate z (A : ℝ))) := by
  let a := realLogCoordinate z (A : ℝ)
  let b := realLogCoordinate z (Y : ℝ)
  have ha : 0 < a := realLogCoordinate_pos_nat hz hA
  have hb : 0 < b := realLogCoordinate_pos_nat hz (hA.trans hAY)
  have hab : a ≤ b := realLogCoordinate_mono_nat hz hA hAY
  have hmajorInt : IntervalIntegrable (fun t : ℝ => e / t) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    exact continuousAt_const.div continuousAt_id
      (ne_of_gt (ha.trans_le ht.1)) |>.continuousWithinAt
  unfold continuumCellOperator
  change |∫ t in a..b, f t / t| ≤
    e * (Real.log b - Real.log a)
  calc
    |∫ t in a..b, f t / t| ≤ ∫ t in a..b, |f t / t| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, e / t := by
      exact intervalIntegral.integral_mono_on hab hint.abs hmajorInt
        (fun t ht => by
          have htpos : 0 < t := ha.trans_le ht.1
          rw [abs_div, abs_of_pos htpos]
          exact div_le_div_of_nonneg_right (hbound t ht) htpos.le)
    _ = e * (Real.log b - Real.log a) := by
      have heq : (fun t : ℝ => e / t) = fun t => e * (1 / t) := by
        funext t
        ring
      rw [heq, intervalIntegral.integral_const_mul,
        integral_one_div_of_pos ha hb, Real.log_div hb.ne' ha.ne']





/-- The outer prime-cell operator commutes with the inner continuum kernel
integral.  Kernel symmetry puts the surviving prime sum in the orientation
required by the one-index theorem. -/
lemma primeCellOperator_continuumKernel_commute
    {z : ℝ} (hz : 1 < z)
    {A₁ Y₁ A₂ Y₂ : ℕ}
    (hA₁Y₁ : A₁ ≤ Y₁)
    (hA₂ : 2 ≤ A₂) (hA₂Y₂ : A₂ ≤ Y₂) :
    primeCellOperator z A₁ Y₁ (fun s =>
        continuumCellOperator z A₂ Y₂ (covarianceKernel s)) =
      continuumCellOperator z A₂ Y₂ (fun t =>
        primeCellOperator z A₁ Y₁ (covarianceKernel t)) := by
  let a := realLogCoordinate z (A₂ : ℝ)
  let b := realLogCoordinate z (Y₂ : ℝ)
  have ha : 0 < a := realLogCoordinate_pos_nat hz hA₂
  have hab : a ≤ b := realLogCoordinate_mono_nat hz hA₂ hA₂Y₂
  have hcommute := primeCellOperator_intervalIntegral z hA₁Y₁
    (a := a) (b := b) (fun s t => covarianceKernel s t / t)
    (fun p hp => by
      apply ContinuousOn.intervalIntegrable_of_Icc hab
      intro t ht
      exact (continuous_covarianceKernel_left
        (realLogCoordinate z (p : ℝ))).continuousAt.div continuousAt_id
          (ne_of_gt (ha.trans_le ht.1)) |>.continuousWithinAt)
  unfold continuumCellOperator
  change primeCellOperator z A₁ Y₁
      (fun s => ∫ t in a..b, covarianceKernel s t / t) =
    ∫ t in a..b, primeCellOperator z A₁ Y₁ (covarianceKernel t) / t
  rw [hcommute]
  apply intervalIntegral.integral_congr
  intro t ht
  change primeCellOperator z A₁ Y₁ (fun s => covarianceKernel s t / t) =
    primeCellOperator z A₁ Y₁ (covarianceKernel t) / t
  rw [primeCellOperator_eq_sum z hA₁Y₁,
    primeCellOperator_eq_sum z hA₁Y₁]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  rw [covarianceKernel_comm]
  ring

lemma coordinateCell_mem_unit {z : ℝ} (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y) (hYz : (Y : ℝ) ≤ z)
    {t : ℝ}
    (ht : t ∈ Icc (realLogCoordinate z (A : ℝ))
      (realLogCoordinate z (Y : ℝ))) :
    t ∈ Icc (0 : ℝ) 1 := by
  have hlow := realLogCoordinate_mem_unit hz
    (show (1 : ℝ) ≤ (A : ℝ) by exact_mod_cast (show 1 ≤ A by omega))
    ((show (A : ℝ) ≤ (Y : ℝ) by exact_mod_cast hAY).trans hYz)
  have hupp := realLogCoordinate_mem_unit hz
    (show (1 : ℝ) ≤ (Y : ℝ) by exact_mod_cast (show 1 ≤ Y by omega)) hYz
  exact ⟨hlow.1.trans ht.1, ht.2.trans hupp.2⟩



lemma continuumCellOperator_kernel_eq_regularized
    {s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y) (hYz : (Y : ℝ) ≤ z) :
    continuumCellOperator z A Y (covarianceKernel s) =
      regularizedContinuumKernelCell z A Y s := by
  unfold continuumCellOperator regularizedContinuumKernelCell
  apply intervalIntegral.integral_congr
  intro t ht
  have htIcc : t ∈ Icc (realLogCoordinate z (A : ℝ))
      (realLogCoordinate z (Y : ℝ)) := by
    simpa [uIcc_of_le (realLogCoordinate_mono_nat hz hA hAY)] using ht
  have htUnit := coordinateCell_mem_unit hz hA hAY hYz htIcc
  have htpos : 0 < t :=
    (realLogCoordinate_pos_nat hz hA).trans_le htIcc.1
  have hmul := mul_covarianceKernelQuotient_eq_kernel hs htUnit
  field_simp [ne_of_gt htpos]
  linarith

lemma continuous_regularizedContinuumKernelCell
    (z : ℝ) (A Y : ℕ) :
    Continuous (regularizedContinuumKernelCell z A Y) := by
  unfold regularizedContinuumKernelCell
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (a₀ := realLogCoordinate z (A : ℝ))
    (b₀ := realLogCoordinate z (Y : ℝ))
  exact continuous_uncurry_covarianceKernelQuotient

lemma continuous_primeCellKernel
    (z : ℝ) {A Y : ℕ} (hAY : A ≤ Y) :
    Continuous (fun s => primeCellOperator z A Y (covarianceKernel s)) := by
  rw [show (fun s => primeCellOperator z A Y (covarianceKernel s)) =
      fun s => ∑ p ∈ intervalPrimes A Y,
        covarianceKernel s (realLogCoordinate z (p : ℝ)) / (p : ℝ) by
    funext s
    rw [primeCellOperator_eq_sum z hAY] ]
  apply continuous_finset_sum _
  intro p hp
  exact (continuous_covarianceKernel.comp
    (continuous_id.prodMk continuous_const)).div_const (p : ℝ)

lemma intervalIntegrable_div_of_continuous
    {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    IntervalIntegrable (fun t => f t / t) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro t ht
  exact hf.continuousAt.div continuousAt_id
    (ne_of_gt (ha.trans_le ht.1)) |>.continuousWithinAt

lemma continuumCellOperator_sub
    (z : ℝ) (A Y : ℕ) (f g : ℝ → ℝ)
    (hf : IntervalIntegrable (fun t => f t / t) volume
      (realLogCoordinate z (A : ℝ)) (realLogCoordinate z (Y : ℝ)))
    (hg : IntervalIntegrable (fun t => g t / t) volume
      (realLogCoordinate z (A : ℝ)) (realLogCoordinate z (Y : ℝ))) :
    continuumCellOperator z A Y (fun t => f t - g t) =
      continuumCellOperator z A Y f - continuumCellOperator z A Y g := by
  unfold continuumCellOperator
  simp_rw [sub_div]
  exact intervalIntegral.integral_sub hf hg

/-- Deterministic two-index transfer.  One-index error `e₂` is averaged
over the actual first prime cell, while `e₁` is averaged over the exact
continuum harmonic length of the second cell. -/
theorem doubleKernelCell_error_le_of_oneIndex
    {z : ℝ} (hz : 1 < z)
    {A₁ Y₁ A₂ Y₂ : ℕ}
    (hA₁ : 2 ≤ A₁) (hA₁Y₁ : A₁ ≤ Y₁) (hY₁z : (Y₁ : ℝ) ≤ z)
    (hA₂ : 2 ≤ A₂) (hA₂Y₂ : A₂ ≤ Y₂) (hY₂z : (Y₂ : ℝ) ≤ z)
    {e₁ e₂ : ℝ}
    (hquad₁ : ∀ t ∈ Icc (0 : ℝ) 1,
      |primeCellOperator z A₁ Y₁ (covarianceKernel t) -
        continuumCellOperator z A₁ Y₁ (covarianceKernel t)| ≤ e₁)
    (hquad₂ : ∀ s ∈ Icc (0 : ℝ) 1,
      |primeCellOperator z A₂ Y₂ (covarianceKernel s) -
        continuumCellOperator z A₂ Y₂ (covarianceKernel s)| ≤ e₂) :
    |doublePrimeKernelCell z A₁ Y₁ A₂ Y₂ -
        doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂| ≤
      e₂ * (fullReciprocalSum Y₁ - fullReciprocalSum A₁) +
        e₁ * (Real.log (realLogCoordinate z (Y₂ : ℝ)) -
          Real.log (realLogCoordinate z (A₂ : ℝ))) := by
  let P₁ : (ℝ → ℝ) → ℝ := primeCellOperator z A₁ Y₁
  let C₁ : (ℝ → ℝ) → ℝ := continuumCellOperator z A₁ Y₁
  let P₂ : (ℝ → ℝ) → ℝ := primeCellOperator z A₂ Y₂
  let C₂ : (ℝ → ℝ) → ℝ := continuumCellOperator z A₂ Y₂
  let mixed : ℝ := P₁ (fun s => C₂ (covarianceKernel s))
  have hfirst :
      |doublePrimeKernelCell z A₁ Y₁ A₂ Y₂ - mixed| ≤
        e₂ * (fullReciprocalSum Y₁ - fullReciprocalSum A₁) := by
    have heq :
        doublePrimeKernelCell z A₁ Y₁ A₂ Y₂ - mixed =
          P₁ (fun s => P₂ (covarianceKernel s) - C₂ (covarianceKernel s)) := by
      dsimp only [doublePrimeKernelCell, mixed, P₁, P₂, C₂]
      rw [primeCellOperator_sub z hA₁Y₁]
    rw [heq]
    apply abs_primeCellOperator_le z hA₁Y₁
    intro p hp
    have hpData := mem_intervalPrimes_iff.mp hp
    have hpUnit : realLogCoordinate z (p : ℝ) ∈ Icc (0 : ℝ) 1 := by
      apply realLogCoordinate_mem_unit hz
      · exact_mod_cast (show 1 ≤ p by omega)
      · exact (show (p : ℝ) ≤ (Y₁ : ℝ) by exact_mod_cast hpData.2.2).trans hY₁z
    exact hquad₂ _ hpUnit
  have hmixed : mixed = C₂ (fun t => P₁ (covarianceKernel t)) := by
    dsimp only [mixed, P₁, C₂]
    exact primeCellOperator_continuumKernel_commute hz hA₁Y₁
      hA₂ hA₂Y₂
  let R₁ : ℝ → ℝ := regularizedContinuumKernelCell z A₁ Y₁
  have hC₁eq : C₂ (fun t => C₁ (covarianceKernel t)) = C₂ R₁ := by
    unfold C₂ continuumCellOperator
    apply intervalIntegral.integral_congr
    intro t ht
    have htCell : t ∈ Icc (realLogCoordinate z (A₂ : ℝ))
        (realLogCoordinate z (Y₂ : ℝ)) := by
      simpa [uIcc_of_le (realLogCoordinate_mono_nat hz hA₂ hA₂Y₂)] using ht
    have htUnit := coordinateCell_mem_unit hz hA₂ hA₂Y₂ hY₂z htCell
    change C₁ (covarianceKernel t) / t = R₁ t / t
    congr 1
    dsimp only [C₁, R₁]
    exact continuumCellOperator_kernel_eq_regularized htUnit hz
      hA₁ hA₁Y₁ hY₁z
  have ha₂ : 0 < realLogCoordinate z (A₂ : ℝ) :=
    realLogCoordinate_pos_nat hz hA₂
  have hab₂ : realLogCoordinate z (A₂ : ℝ) ≤
      realLogCoordinate z (Y₂ : ℝ) :=
    realLogCoordinate_mono_nat hz hA₂ hA₂Y₂
  have hPint : IntervalIntegrable
      (fun t => P₁ (covarianceKernel t) / t) volume
      (realLogCoordinate z (A₂ : ℝ)) (realLogCoordinate z (Y₂ : ℝ)) := by
    apply intervalIntegrable_div_of_continuous
      (continuous_primeCellKernel z hA₁Y₁) ha₂ hab₂
  have hRint : IntervalIntegrable (fun t => R₁ t / t) volume
      (realLogCoordinate z (A₂ : ℝ)) (realLogCoordinate z (Y₂ : ℝ)) := by
    apply intervalIntegrable_div_of_continuous
      (continuous_regularizedContinuumKernelCell z A₁ Y₁) ha₂ hab₂
  have hsecond :
      |mixed - doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂| ≤
        e₁ * (Real.log (realLogCoordinate z (Y₂ : ℝ)) -
          Real.log (realLogCoordinate z (A₂ : ℝ))) := by
    have heq : mixed - doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂ =
        C₂ (fun t => P₁ (covarianceKernel t) - R₁ t) := by
      rw [hmixed]
      dsimp only [doubleContinuumKernelCell]
      change C₂ (fun t => P₁ (covarianceKernel t)) -
          C₂ (fun t => C₁ (covarianceKernel t)) = _
      rw [hC₁eq]
      symm
      exact continuumCellOperator_sub z A₂ Y₂ _ _ hPint hRint
    rw [heq]
    apply abs_continuumCellOperator_le z hz hA₂ hA₂Y₂
      (fun t => P₁ (covarianceKernel t) - R₁ t)
    · apply (hPint.sub hRint).congr
      intro t ht
      ring
    · intro t ht
      have htUnit := coordinateCell_mem_unit hz hA₂ hA₂Y₂ hY₂z ht
      have hreg : R₁ t = C₁ (covarianceKernel t) := by
        dsimp only [R₁, C₁]
        exact (continuumCellOperator_kernel_eq_regularized htUnit hz
          hA₁ hA₁Y₁ hY₁z).symm
      rw [hreg]
      exact hquad₁ t htUnit
  calc
    |doublePrimeKernelCell z A₁ Y₁ A₂ Y₂ -
        doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂| ≤
      |doublePrimeKernelCell z A₁ Y₁ A₂ Y₂ - mixed| +
        |mixed - doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂| := by
      have hsplit :
          doublePrimeKernelCell z A₁ Y₁ A₂ Y₂ -
              doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂ =
            (doublePrimeKernelCell z A₁ Y₁ A₂ Y₂ - mixed) +
              (mixed - doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂) := by ring
      rw [hsplit]
      exact abs_add_le _ _
    _ ≤ e₂ * (fullReciprocalSum Y₁ - fullReciprocalSum A₁) +
        e₁ * (Real.log (realLogCoordinate z (Y₂ : ℝ)) -
          Real.log (realLogCoordinate z (A₂ : ℝ))) :=
      add_le_add hfirst hsecond



/-! ## Moving-low input cell -/































end Erdos390.Full.DoubleKernelPrimeQuadrature

end

theorem solution :
∀ {z : Real},
  LT.lt.{0} (1 : Real) z →
    ∀ {A₁ Y₁ A₂ Y₂ : Nat},
      LE.le.{0} (2 : Nat) A₁ →
        LE.le.{0} A₁ Y₁ →
          LE.le.{0} (↑Y₁) z →
            LE.le.{0} (2 : Nat) A₂ →
              LE.le.{0} A₂ Y₂ →
                LE.le.{0} (↑Y₂) z →
                  ∀ {e₁ e₂ : Real},
                    (∀ (t : Real),
                        Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) t →
                          LE.le.{0}
                            (abs.{0}
                              (HSub.hSub.{0, 0, 0}
                                (Erdos390.Full.DoubleKernelPrimeQuadrature.primeCellOperator z A₁ Y₁
                                  (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel t))
                                (Erdos390.Full.DoubleKernelPrimeQuadrature.continuumCellOperator z A₁ Y₁
                                  (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel t))))
                            e₁) →
                      (∀ (s : Real),
                          Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) s →
                            LE.le.{0}
                              (abs.{0}
                                (HSub.hSub.{0, 0, 0}
                                  (Erdos390.Full.DoubleKernelPrimeQuadrature.primeCellOperator z A₂ Y₂
                                    (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel s))
                                  (Erdos390.Full.DoubleKernelPrimeQuadrature.continuumCellOperator z A₂ Y₂
                                    (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel s))))
                              e₂) →
                        LE.le.{0}
                          (abs.{0}
                            (HSub.hSub.{0, 0, 0}
                              (Erdos390.Full.DoubleKernelPrimeQuadrature.doublePrimeKernelCell z A₁ Y₁ A₂ Y₂)
                              (Erdos390.Full.DoubleKernelPrimeQuadrature.doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂)))
                          (HAdd.hAdd.{0, 0, 0}
                            (HMul.hMul.{0, 0, 0} e₂
                              (HSub.hSub.{0, 0, 0} (Erdos390.Full.PrimeSums.fullReciprocalSum Y₁)
                                (Erdos390.Full.PrimeSums.fullReciprocalSum A₁)))
                            (HMul.hMul.{0, 0, 0} e₁
                              (HSub.hSub.{0, 0, 0}
                                (Real.log (Erdos390.Full.KernelPrimeQuadrature.realLogCoordinate z ↑Y₂))
                                (Real.log (Erdos390.Full.KernelPrimeQuadrature.realLogCoordinate z ↑A₂))))) := by
  exact @Erdos390.Full.DoubleKernelPrimeQuadrature.doubleKernelCell_error_le_of_oneIndex
