-- Prove2me | solution 1 for Erdos390.Full.SquarefreeReferenceOperatorIdentification.referenceBandRow_eq_rawOperator
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:13:13.094629+00:00
-- url     : https://prove2.me/submissions/7e9947fe-d4a7-4058-b655-9689cd19a2c5

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
import Theorems.Thm_Erdos390_Full_SquarefreeReferenceOperatorIdentification_reference_block_eq_arithmetic

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











/-- Exact row-level identification. -/
theorem referenceBandRow_eq_rawOperator
    (E : IntervalCertificate P) (b : Band → ℝ) (i : Band) :
    referenceBandRow P b i =
      PaperWeightedInverseExport.rawOperator
        (arithmeticDiagonal (y n) E.lower E.upper)
        (arithmeticKernel (y n) E.lower E.upper) b i := by
  unfold referenceBandRow
  rw [show (∑ p ∈ P.data.fiber i,
      ∑ q : BandPrime n W,
        b (P.band q) * squarefreeReferenceEntry n p.1 q.1) =
      ∑ j : Band, b j *
        (∑ p ∈ P.data.fiber i,
          ∑ q ∈ P.data.fiber j,
            squarefreeReferenceEntry n p.1 q.1) by
    calc
      (∑ p ∈ P.data.fiber i,
          ∑ q : BandPrime n W,
            b (P.band q) * squarefreeReferenceEntry n p.1 q.1) =
        ∑ q : BandPrime n W,
          b (P.band q) *
            (∑ p ∈ P.data.fiber i,
              squarefreeReferenceEntry n p.1 q.1) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro q hq
          rw [Finset.mul_sum]
      _ = ∑ j : Band,
          ∑ q ∈ P.data.fiber j,
            b (P.band q) *
              (∑ p ∈ P.data.fiber i,
                squarefreeReferenceEntry n p.1 q.1) := by
          rw [← Finset.sum_fiberwise Finset.univ P.band
            (fun q : BandPrime n W ↦
              b (P.band q) *
                (∑ p ∈ P.data.fiber i,
                  squarefreeReferenceEntry n p.1 q.1))]
          rfl
      _ = ∑ j : Band, b j *
          (∑ p ∈ P.data.fiber i,
            ∑ q ∈ P.data.fiber j,
              squarefreeReferenceEntry n p.1 q.1) := by
          apply Finset.sum_congr rfl
          intro j hj
          calc
            (∑ q ∈ P.data.fiber j,
                b (P.band q) *
                  (∑ p ∈ P.data.fiber i,
                    squarefreeReferenceEntry n p.1 q.1)) =
              ∑ q ∈ P.data.fiber j,
                b j *
                  (∑ p ∈ P.data.fiber i,
                    squarefreeReferenceEntry n p.1 q.1) := by
                apply Finset.sum_congr rfl
                intro q hq
                have hqj : P.band q = j := by
                  simpa only
                    [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff]
                    using hq
                rw [hqj]
            _ = b j *
                (∑ q ∈ P.data.fiber j,
                  ∑ p ∈ P.data.fiber i,
                    squarefreeReferenceEntry n p.1 q.1) := by
                rw [Finset.mul_sum]
            _ = b j *
                (∑ p ∈ P.data.fiber i,
                  ∑ q ∈ P.data.fiber j,
                    squarefreeReferenceEntry n p.1 q.1) := by
                rw [Finset.sum_comm]]
  unfold PaperWeightedInverseExport.rawOperator
  have hmass : P.mass i ≠ 0 := ne_of_gt (P.data.mass_pos i)
  rw [Finset.mul_sum]
  have hblocks (j : Band) := reference_block_eq_arithmetic E i j
  calc
    ∑ j : Band, (1 / P.mass i) *
        (b j *
          (∑ p ∈ P.data.fiber i,
            ∑ q ∈ P.data.fiber j,
              squarefreeReferenceEntry n p.1 q.1)) =
      ∑ j : Band, b j *
        (arithmeticKernel (y n) E.lower E.upper i j +
          if i = j then arithmeticDiagonal (y n) E.lower E.upper i else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [show (1 / P.mass i) *
          (b j *
            (∑ p ∈ P.data.fiber i,
              ∑ q ∈ P.data.fiber j,
                squarefreeReferenceEntry n p.1 q.1)) =
          b j * ((1 / P.mass i) *
            (∑ p ∈ P.data.fiber i,
              ∑ q ∈ P.data.fiber j,
                squarefreeReferenceEntry n p.1 q.1)) by ring,
        hblocks]
    _ = arithmeticDiagonal (y n) E.lower E.upper i * b i +
        ∑ j : Band, arithmeticKernel (y n) E.lower E.upper i j * b j := by
      rw [show (∑ j : Band, b j *
          (arithmeticKernel (y n) E.lower E.upper i j +
            if i = j then arithmeticDiagonal (y n) E.lower E.upper i else 0)) =
        (∑ j : Band, arithmeticKernel (y n) E.lower E.upper i j * b j) +
          ∑ j : Band,
            if j = i then arithmeticDiagonal (y n) E.lower E.upper i * b j
            else 0 by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro j hj
              by_cases hji : j = i
              · subst j; simp; ring
              · have hij : i ≠ j := Ne.symm hji
                simp [hji, hij]
                ring]
      rw [Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ i)]
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
  (E : Erdos390.Full.PositiveCellTransfer.IntervalCertificate.{u_1} P) (b : Band → Real) (i : Band),
  Eq.{1} (Erdos390.Full.SquarefreeSharpBandTransfer.referenceBandRow.{u_1} P b i)
    (Erdos390.Full.PaperWeightedInverseExport.rawOperator.{u_1}
      (Erdos390.Full.CompressedArithmeticOperator.arithmeticDiagonal.{u_1} (Erdos390.Full.ArithmeticModel.y n)
        (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.lower.{u_1} E)
        (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.upper.{u_1} E))
      (Erdos390.Full.CompressedArithmeticOperator.arithmeticKernel.{u_1} (Erdos390.Full.ArithmeticModel.y n)
        (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.lower.{u_1} E)
        (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.upper.{u_1} E))
      b i) := by
  exact @Erdos390.Full.SquarefreeReferenceOperatorIdentification.referenceBandRow_eq_rawOperator
