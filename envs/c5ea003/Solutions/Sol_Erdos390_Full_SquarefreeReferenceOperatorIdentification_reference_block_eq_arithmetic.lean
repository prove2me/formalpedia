-- Prove2me | solution 1 for Erdos390.Full.SquarefreeReferenceOperatorIdentification.reference_block_eq_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:31:03.690101+00:00
-- url     : https://prove2.me/submissions/f7093a71-20ec-4c28-a590-a6dd0809c0e0

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

/- Source module: Erdos390.Full.PositiveCellTransfer -/
section


/-!
# Actual positive-cell prime-band transfer

This file connects the exact arithmetic band geometry to the unconditional
two-endpoint PNT quadrature.  A certificate records that each finite band is
literally a prime interval `(A_j,Y_j]` inside the actual moving prime band.
From that elementary membership statement we derive, rather than assume,

* `H_j = sum_{A_j < p <= Y_j} 1/p`, and
* `H_j * alpha_j = (sum_{A_j < p <= Y_j} log p / p) / log y`.

The final theorems then import the uniform constants and threshold from
`PrimeBandQuadrature`; no Mertens constant or moving-cell asymptotic appears
as a structure field.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PositiveCellTransfer

open ArithmeticModel PrimeSums PrimeBandQuadrature
open ArithmeticBandGeometry

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]







namespace IntervalCertificate

variable {P : Partition n W Band} (E : IntervalCertificate P)









omit [DecidableEq Band] in
lemma mem_cellPrimes_iff {j : Band} {p : ℕ} :
    p ∈ E.cellPrimes j ↔
      p.Prime ∧ E.lower j < p ∧ p ≤ E.upper j := by
  rw [cellPrimes, Finset.mem_sdiff]
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨_hzero, hpUpper⟩, hpPrime⟩, hpLower⟩
    refine ⟨hpPrime, ?_, hpUpper⟩
    by_contra hnot
    apply hpLower
    exact ⟨⟨Nat.zero_le p, Nat.le_of_not_gt hnot⟩, hpPrime⟩
  · rintro ⟨hpPrime, hpLower, hpUpper⟩
    refine ⟨⟨⟨Nat.zero_le p, hpUpper⟩, hpPrime⟩, ?_⟩
    rintro ⟨⟨_hzero, hpLower'⟩, _hpPrime⟩
    exact (Nat.not_lt_of_ge hpLower') hpLower

private lemma primesUpTo_mono {A Y : ℕ} (hAY : A ≤ Y) :
    primesUpTo A ⊆ primesUpTo Y := by
  intro p hp
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.trans hAY⟩, hp.2⟩

omit [DecidableEq Band] in
lemma cellReciprocalSum_eq_sub (j : Band) :
    (∑ p ∈ E.cellPrimes j, 1 / (p : ℝ)) =
      fullReciprocalSum (E.upper j) - fullReciprocalSum (E.lower j) := by
  have hsub := primesUpTo_mono (E.lower_le_upper j)
  have hsum := Finset.sum_sdiff hsub (f := fun p : ℕ => 1 / (p : ℝ))
  change (∑ p ∈ primesUpTo (E.upper j) \ primesUpTo (E.lower j),
      1 / (p : ℝ)) =
    (∑ p ∈ primesUpTo (E.upper j), 1 / (p : ℝ)) -
      ∑ p ∈ primesUpTo (E.lower j), 1 / (p : ℝ)
  exact eq_sub_of_add_eq hsum



lemma fiber_reciprocalSum_eq_cell (j : Band) :
    (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ)) =
      ∑ q ∈ E.cellPrimes j, 1 / (q : ℝ) := by
  apply Finset.sum_bij (fun p _hp => p.1)
  · intro p hp
    have hpBand : P.band p = j := by
      simpa only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff] using hp
    exact E.mem_cellPrimes_iff.mpr
      ⟨prime_of_mem_primeBand p.2, (E.band_eq_iff p j).mp hpBand⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    exact Subtype.ext heq
  · intro q hq
    have hqData := E.mem_cellPrimes_iff.mp hq
    have hqBand : q ∈ primeBand n W := by
      exact mem_primeBand.mpr
        ⟨hqData.1,
          (E.cutoff_le_lower j).trans_lt hqData.2.1,
          hqData.2.2.trans (E.upper_le_yNat j)⟩
    let p : ArithmeticBandGeometry.BandPrime n W := ⟨q, hqBand⟩
    have hpFiber : p ∈ P.data.fiber j := by
      simp only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff]
      exact (E.band_eq_iff p j).mpr hqData.2
    exact ⟨p, hpFiber, rfl⟩
  · intro p hp
    rfl



/-- Exact arithmetic identification of the harmonic cell mass. -/
theorem mass_eq_fullReciprocalSum_sub (j : Band) :
    P.mass j = fullReciprocalSum (E.upper j) -
      fullReciprocalSum (E.lower j) := by
  change (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ)) = _
  rw [E.fiber_reciprocalSum_eq_cell, E.cellReciprocalSum_eq_sub]













end IntervalCertificate

end Erdos390.Full.PositiveCellTransfer

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







































/-! ## Moving-low input cell -/































end Erdos390.Full.DoubleKernelPrimeQuadrature

end

/- Source module: Erdos390.Full.SquarefreeReferenceOperatorIdentification -/
section


/-!
# Exact identification of the signed squarefree reference operator

The signed reference covariance used in the arithmetic part of paper
Lemma 8.4 is defined prime by prime in
`SquarefreeCovarianceReference`.  The moving-low inverse, on the other
hand, is proved for the endpoint matrix called `arithmeticDiagonal` plus
`arithmeticKernel`.  This file proves that these are literally the same
finite operator for every certified prime partition.  No limit, row bound,
covariance estimate, or inverse is assumed.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.SquarefreeReferenceOperatorIdentification

open ArithmeticModel ArithmeticBandGeometry
open SquarefreeCovarianceReference SquarefreeSharpBandTransfer
open PositiveCellTransfer
open DoubleKernelPrimeQuadrature DiagonalPrimeQuadrature
open CompressedArithmeticOperator
open ConditionedPoissonLimit DickmanBasic

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
variable {P : Partition n W Band}

/-- A certified band fiber and its natural-number prime cell have identical
weighted sums.  This is the reusable bijection behind both the diagonal and
the two-index identifications below. -/
theorem sum_fiber_eq_sum_cell
    (E : IntervalCertificate P) (j : Band) (f : ℕ → ℝ) :
    (∑ p ∈ P.data.fiber j, f p.1) =
      ∑ q ∈ E.cellPrimes j, f q := by
  apply Finset.sum_bij (fun p _hp ↦ p.1)
  · intro p hp
    have hpBand : P.band p = j := by
      simpa only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff] using hp
    exact E.mem_cellPrimes_iff.mpr
      ⟨prime_of_mem_primeBand p.2, (E.band_eq_iff p j).mp hpBand⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    exact Subtype.ext heq
  · intro q hq
    have hqData := E.mem_cellPrimes_iff.mp hq
    have hqBand : q ∈ primeBand n W := by
      exact mem_primeBand.mpr
        ⟨hqData.1, (E.cutoff_le_lower j).trans_lt hqData.2.1,
          hqData.2.2.trans (E.upper_le_yNat j)⟩
    let p : BandPrime n W := ⟨q, hqBand⟩
    have hpFiber : p ∈ P.data.fiber j := by
      simp only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff]
      exact (E.band_eq_iff p j).mpr hqData.2
    exact ⟨p, hpFiber, rfl⟩
  · intro p hp
    rfl

/-- The diagonal `F(t_p)/p` part of the signed reference is exactly the
prime-cell diagonal numerator used in the canonical arithmetic matrix. -/
theorem diagonal_fiber_sum_eq_diagonalPrimeCell
    (E : IntervalCertificate P) (i : Band) :
    (∑ p ∈ P.data.fiber i,
        F (tPrime n p.1) / (p.1 : ℝ)) =
      diagonalPrimeCell (y n) (E.lower i) (E.upper i) := by
  rw [diagonalPrimeCell,
    primeCellOperator_eq_sum (y n) (E.lower_le_upper i)]
  rw [sum_fiber_eq_sum_cell E i
    (fun p ↦ F (tPrime n p) / (p : ℝ))]
  apply Finset.sum_congr
  · rfl
  · intro p hp
    unfold tPrime KernelPrimeQuadrature.realLogCoordinate
    rfl

/-- On two certified fibers the signed kernel entries sum to the exact
double-prime kernel cell. -/
theorem kernel_fiber_sum_eq_doublePrimeKernelCell
    (E : IntervalCertificate P) (i j : Band) :
    (∑ p ∈ P.data.fiber i,
        ∑ q ∈ P.data.fiber j,
          squarefreeKernelEntry n p.1 q.1) =
      doublePrimeKernelCell (y n)
        (E.lower i) (E.upper i) (E.lower j) (E.upper j) := by
  rw [doublePrimeKernelCell,
    primeCellOperator_eq_sum (y n) (E.lower_le_upper i)]
  rw [sum_fiber_eq_sum_cell E i (fun p ↦
    ∑ q ∈ P.data.fiber j, squarefreeKernelEntry n p q.1)]
  apply Finset.sum_congr
  · rfl
  · intro p hp
    rw [primeCellOperator_eq_sum (y n) (E.lower_le_upper j)]
    rw [sum_fiber_eq_sum_cell E j
      (fun q ↦ squarefreeKernelEntry n p q)]
    rw [show E.cellPrimes j =
        intervalPrimes (E.lower j) (E.upper j) by rfl]
    rw [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr
    · rfl
    · intro q hq
      unfold squarefreeKernelEntry tPrime
        KernelPrimeQuadrature.realLogCoordinate
      ring

/-- The reference entry is the kernel entry plus a Kronecker diagonal
multiplier. -/
theorem squarefreeReferenceEntry_eq_kernel_add_diagonal
    (p q : ℕ) :
    squarefreeReferenceEntry n p q =
      squarefreeKernelEntry n p q +
        if p = q then F (tPrime n p) / (p : ℝ) else 0 := by
  by_cases hpq : p = q
  · subst q
    simp [squarefreeReferenceEntry]
    ring
  · simp [squarefreeReferenceEntry, hpq]

/-- The normalized reference block entry is exactly the canonical arithmetic
kernel entry, with the diagonal multiplier added when the two bands agree. -/
theorem reference_block_eq_arithmetic
    (E : IntervalCertificate P) (i j : Band) :
    (1 / P.mass i) *
        (∑ p ∈ P.data.fiber i,
          ∑ q ∈ P.data.fiber j,
            squarefreeReferenceEntry n p.1 q.1) =
      arithmeticKernel (y n) E.lower E.upper i j +
        if i = j then arithmeticDiagonal (y n) E.lower E.upper i else 0 := by
  have hmass : P.mass i ≠ 0 := ne_of_gt (P.data.mass_pos i)
  have hmassCell :
      DoubleKernelPrimeQuadrature.actualCellMass (E.lower i) (E.upper i) =
        P.mass i := by
    unfold DoubleKernelPrimeQuadrature.actualCellMass
    exact (E.mass_eq_fullReciprocalSum_sub i).symm
  have hkernel :
      (1 / P.mass i) *
          (∑ p ∈ P.data.fiber i,
            ∑ q ∈ P.data.fiber j,
              squarefreeKernelEntry n p.1 q.1) =
        arithmeticKernel (y n) E.lower E.upper i j := by
    rw [kernel_fiber_sum_eq_doublePrimeKernelCell E i j]
    unfold arithmeticKernel normalizedDoublePrimeKernelCell
    rw [hmassCell]
    ring
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    have hdiagInner (p : BandPrime n W) (hp : p ∈ P.data.fiber i) :
        (∑ q ∈ P.data.fiber i,
          if p.1 = q.1 then F (tPrime n p.1) / (p.1 : ℝ) else 0) =
          F (tPrime n p.1) / (p.1 : ℝ) := by
      calc
        (∑ q ∈ P.data.fiber i,
          if p.1 = q.1 then F (tPrime n p.1) / (p.1 : ℝ) else 0) =
            ∑ q ∈ P.data.fiber i,
              if q = p then F (tPrime n p.1) / (p.1 : ℝ) else 0 := by
                apply Finset.sum_congr rfl
                intro q hq
                by_cases hqp : q = p
                · subst q; simp
                · have hv : q.1 ≠ p.1 := by
                    intro hv
                    exact hqp (Subtype.ext hv)
                  simp [hqp, Ne.symm hv]
        _ = F (tPrime n p.1) / (p.1 : ℝ) := by
          simp [hp]
    have hsplit :
        (∑ p ∈ P.data.fiber i,
          ∑ q ∈ P.data.fiber i,
            squarefreeReferenceEntry n p.1 q.1) =
          (∑ p ∈ P.data.fiber i,
            ∑ q ∈ P.data.fiber i,
              squarefreeKernelEntry n p.1 q.1) +
          ∑ p ∈ P.data.fiber i,
            F (tPrime n p.1) / (p.1 : ℝ) := by
      simp_rw [squarefreeReferenceEntry_eq_kernel_add_diagonal,
        Finset.sum_add_distrib]
      apply congrArg₂ (fun x y : ℝ ↦ x + y) rfl
      apply Finset.sum_congr rfl
      intro p hp
      exact hdiagInner p hp
    rw [hsplit, mul_add, hkernel,
      diagonal_fiber_sum_eq_diagonalPrimeCell E i]
    unfold arithmeticDiagonal normalizedDiagonalPrimeCell
    rw [hmassCell]
    ring
  · rw [if_neg hij]
    have hdiagZero (p : BandPrime n W) (hp : p ∈ P.data.fiber i) :
        (∑ q ∈ P.data.fiber j,
          if p.1 = q.1 then F (tPrime n p.1) / (p.1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      have hpi : P.band p = i := by
        simpa only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff] using hp
      have hqj : P.band q = j := by
        simpa only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff] using hq
      have hpq : p.1 ≠ q.1 := by
        intro hpq
        have hpqSub : p = q := Subtype.ext hpq
        subst q
        exact hij (hpi.symm.trans hqj)
      simp [hpq]
    have hsplit :
        (∑ p ∈ P.data.fiber i,
          ∑ q ∈ P.data.fiber j,
            squarefreeReferenceEntry n p.1 q.1) =
          ∑ p ∈ P.data.fiber i,
            ∑ q ∈ P.data.fiber j,
              squarefreeKernelEntry n p.1 q.1 := by
      simp_rw [squarefreeReferenceEntry_eq_kernel_add_diagonal,
        Finset.sum_add_distrib]
      rw [show (∑ p ∈ P.data.fiber i,
          ∑ q ∈ P.data.fiber j,
            if p.1 = q.1 then F (tPrime n p.1) / (p.1 : ℝ) else 0) = 0 by
        apply Finset.sum_eq_zero
        intro p hp
        exact hdiagZero p hp]
      ring
    rw [hsplit, hkernel]
    ring





section MarkedProfileApplication

variable {Cell : Type*} [Fintype Cell]
variable {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]
variable {M : ℕ}



end MarkedProfileApplication

end Erdos390.Full.SquarefreeReferenceOperatorIdentification

end

universe u_1
theorem solution :
∀ {n W : Nat} {Band : Type u_1} [inst : Fintype.{u_1} Band] [inst_1 : DecidableEq.{u_1 + 1} Band]
  {P : Erdos390.Full.ArithmeticBandGeometry.Partition.{u_1} n W Band}
  (E : Erdos390.Full.PositiveCellTransfer.IntervalCertificate.{u_1} P) (i j : Band),
  Eq.{1}
    (HMul.hMul.{0, 0, 0}
      (HDiv.hDiv.{0, 0, 0} (1 : Real) (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_1} P i))
      (∑
        p ∈
          Erdos390.Lemma84.WeightedBandData.fiber.{0, u_1} (Erdos390.Full.ArithmeticBandGeometry.Partition.data.{u_1} P)
            i,
        ∑
          q ∈
            Erdos390.Lemma84.WeightedBandData.fiber.{0, u_1}
              (Erdos390.Full.ArithmeticBandGeometry.Partition.data.{u_1} P) j,
          Erdos390.Full.SquarefreeCovarianceReference.squarefreeReferenceEntry n ↑p ↑q))
    (HAdd.hAdd.{0, 0, 0}
      (Erdos390.Full.CompressedArithmeticOperator.arithmeticKernel.{u_1} (Erdos390.Full.ArithmeticModel.y n)
        (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.lower.{u_1} E)
        (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.upper.{u_1} E) i j)
      (ite.{1} (Eq.{u_1 + 1} i j)
        (Erdos390.Full.CompressedArithmeticOperator.arithmeticDiagonal.{u_1} (Erdos390.Full.ArithmeticModel.y n)
          (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.lower.{u_1} E)
          (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.upper.{u_1} E) i)
        (0 : Real))) := by
  exact @Erdos390.Full.SquarefreeReferenceOperatorIdentification.reference_block_eq_arithmetic
