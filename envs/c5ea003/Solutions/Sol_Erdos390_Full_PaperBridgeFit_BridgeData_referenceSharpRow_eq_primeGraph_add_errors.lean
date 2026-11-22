-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.referenceSharpRow_eq_primeGraph_add_errors
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:20:52.74028+00:00
-- url     : https://prove2.me/submissions/5fc1aa10-719b-45fb-8b57-0db624ddbabe

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







section MarkedProfileApplication

variable {Cell : Type*} [Fintype Cell]
variable {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]
variable {M : ℕ}



end MarkedProfileApplication

end Erdos390.Full.SquarefreeReferenceOperatorIdentification

end

/- Source module: Erdos390.Full.PaperReferenceSharpPrimeGraph -/
section


/-!
# Prime-graph model for the literal sharp reference band operator

The endpoint double-quadrature route loses a factor depending on the first
cell width.  This file instead performs the comparison before band
quadrature.  A band coefficient `alpha_j x_j` is split exactly as

`t_p x_j + (alpha_j - t_p) x_j`.

The first term is a compression of the literal finite prime graph.  The
second is controlled by exact arithmetic centering.  Consequently the
constants below do not involve a least band centre, the number of bands, or
the low-cell width.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open SquarefreeSharpBandTransfer SquarefreeCovarianceReference
open SquarefreeReferenceOperatorIdentification
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic FiniteGraphQuotientInverse
open ConditionedPoissonLimit DickmanBasic
open PoissonDickmanDirichlet
open PaperCanonicalSlowKappa

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)













/-- Exact decomposition of the literal signed reference sharp row into the
compressed prime graph, its finite row defect, and the two arithmetic
centering errors. -/
theorem referenceSharpRow_eq_primeGraph_add_errors
    (x : Band → ℝ) (i : Band) :
    referenceSharpRow B.partition x i =
      graphOperator B.compressedPrimeGraphEdge x i +
        B.referenceResidualError x i +
        B.referenceCenteringDiagonal x i +
        B.referenceCenteringKernel x i := by
  let H := B.harmonicMass i
  let alpha := B.bandCenter i
  have hH : 0 < H := by simpa only [H] using B.harmonicMass_pos i
  have halpha : 0 < alpha := by
    simpa only [alpha] using B.bandCenter_pos i
  have hband (p : BandPrime B.sampleData.n B.sampleData.W)
      (hp : p ∈ B.partition.data.fiber i) : B.partition.band p = i := by
    simpa only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff] using hp
  have hcenter (q : BandPrime B.sampleData.n B.sampleData.W) :
      B.bandCenter (B.partition.band q) =
        tPrime B.sampleData.n q.1 + B.primeDeviation q := by
    unfold primeDeviation
    ring
  have hinner (p : BandPrime B.sampleData.n B.sampleData.W)
      (hp : p ∈ B.partition.data.fiber i) :
      (∑ q : BandPrime B.sampleData.n B.sampleData.W,
        (B.bandCenter (B.partition.band q) * x (B.partition.band q)) *
          squarefreeReferenceEntry B.sampleData.n p.1 q.1) =
        (1 / (p.1 : ℝ)) *
            rowResidual
              (primeWeight B.sampleData.n)
              (primeDiagonal B.sampleData.n)
              (primeKernel B.sampleData.n) p * x i +
          (1 / (p.1 : ℝ)) *
            (∑ q : BandPrime B.sampleData.n B.sampleData.W,
              (-(primeWeight B.sampleData.n q *
                    primeKernel B.sampleData.n p q)) *
                (x i - x (B.partition.band q))) +
          (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)) *
            B.primeDeviation p * x i +
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            B.primeDeviation q * x (B.partition.band q) *
              covarianceKernel
                (tPrime B.sampleData.n p.1)
                (tPrime B.sampleData.n q.1) /
                  ((p.1 : ℝ) * (q.1 : ℝ)) := by
    have hdiag :
        (∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (B.bandCenter (B.partition.band q) * x (B.partition.band q)) *
            (if p.1 = q.1 then
              F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)
            else 0)) =
          (B.bandCenter (B.partition.band p) * x (B.partition.band p)) *
            (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)) := by
      rw [Finset.sum_eq_single p]
      · simp
      · intro q hq hqp
        have hpqVal : p.1 ≠ q.1 := by
          intro hpq
          exact hqp (Subtype.ext hpq.symm)
        simp [hpqVal]
      · simp
    let a : BandPrime B.sampleData.n B.sampleData.W → ℝ :=
      fun q ↦ primeWeight B.sampleData.n q *
        primeKernel B.sampleData.n p q
    have hkernelT :
        (∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (tPrime B.sampleData.n q.1 * x (B.partition.band q)) *
            squarefreeKernelEntry B.sampleData.n p.1 q.1) =
          (1 / (p.1 : ℝ)) *
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              a q * x (B.partition.band q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      unfold a primeWeight primeKernel squarefreeKernelEntry
      ring
    have hkernelG :
        (∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (B.primeDeviation q * x (B.partition.band q)) *
            squarefreeKernelEntry B.sampleData.n p.1 q.1) =
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            B.primeDeviation q * x (B.partition.band q) *
              covarianceKernel
                (tPrime B.sampleData.n p.1)
                (tPrime B.sampleData.n q.1) /
                  ((p.1 : ℝ) * (q.1 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro q hq
      unfold squarefreeKernelEntry
      ring
    have hkernelSplit :
        (∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (B.bandCenter (B.partition.band q) * x (B.partition.band q)) *
            squarefreeKernelEntry B.sampleData.n p.1 q.1) =
          (1 / (p.1 : ℝ)) *
              ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                a q * x (B.partition.band q) +
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q * x (B.partition.band q) *
                covarianceKernel
                  (tPrime B.sampleData.n p.1)
                  (tPrime B.sampleData.n q.1) /
                    ((p.1 : ℝ) * (q.1 : ℝ)) := by
      calc
        _ = ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            ((tPrime B.sampleData.n q.1 + B.primeDeviation q) *
              x (B.partition.band q)) *
                squarefreeKernelEntry B.sampleData.n p.1 q.1 := by
              apply Finset.sum_congr rfl
              intro q hq
              rw [← hcenter q]
        _ = (∑ q : BandPrime B.sampleData.n B.sampleData.W,
              (tPrime B.sampleData.n q.1 * x (B.partition.band q)) *
                squarefreeKernelEntry B.sampleData.n p.1 q.1) +
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              (B.primeDeviation q * x (B.partition.band q)) *
                squarefreeKernelEntry B.sampleData.n p.1 q.1 := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro q hq
              ring
        _ = _ := by rw [hkernelT, hkernelG]
    have hdiagSplit :
        (B.bandCenter (B.partition.band p) * x (B.partition.band p)) *
            (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)) =
          (1 / (p.1 : ℝ)) *
              (F (tPrime B.sampleData.n p.1) *
                tPrime B.sampleData.n p.1) * x i +
            (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)) *
              B.primeDeviation p * x i := by
      rw [hcenter p, hband p hp]
      ring
    have hgraphExpand :
        (∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (-(a q)) * (x i - x (B.partition.band q))) =
          -(∑ q : BandPrime B.sampleData.n B.sampleData.W, a q) * x i +
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              a q * x (B.partition.band q) := by
      calc
        _ = ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            ((-(a q)) * x i + a q * x (B.partition.band q)) := by
              apply Finset.sum_congr rfl
              intro q hq
              ring
        _ = (∑ q : BandPrime B.sampleData.n B.sampleData.W,
              (-(a q)) * x i) +
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              a q * x (B.partition.band q) := Finset.sum_add_distrib
        _ = _ := by
              rw [← Finset.sum_mul, Finset.sum_neg_distrib]
    simp_rw [squarefreeReferenceEntry_eq_kernel_add_diagonal, mul_add]
    rw [Finset.sum_add_distrib, hdiag, hkernelSplit, hdiagSplit]
    unfold rowResidual primeDiagonal
    have hgraphExpand' :
        (∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (-(primeWeight B.sampleData.n q *
              primeKernel B.sampleData.n p q)) *
            (x i - x (B.partition.band q))) =
          -(∑ q : BandPrime B.sampleData.n B.sampleData.W,
              primeWeight B.sampleData.n q *
                primeKernel B.sampleData.n p q) * x i +
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              (primeWeight B.sampleData.n q *
                primeKernel B.sampleData.n p q) *
                  x (B.partition.band q) := by
      simpa only [a] using hgraphExpand
    rw [hgraphExpand']
    ring
  unfold referenceSharpRow referenceBandRow
    compressedPrimeGraphEdge referenceResidualError
    referenceCenteringDiagonal referenceCenteringKernel graphOperator
  simp only
  change ((1 / B.harmonicMass i) *
      (∑ p ∈ B.partition.data.fiber i,
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (B.bandCenter (B.partition.band q) * x (B.partition.band q)) *
            squarefreeReferenceEntry B.sampleData.n p.1 q.1)) /
      B.bandCenter i = _
  rw [show (∑ p ∈ B.partition.data.fiber i,
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        (B.bandCenter (B.partition.band q) * x (B.partition.band q)) *
          squarefreeReferenceEntry B.sampleData.n p.1 q.1) =
      ∑ p ∈ B.partition.data.fiber i,
        ((1 / (p.1 : ℝ)) *
            rowResidual
              (primeWeight B.sampleData.n)
              (primeDiagonal B.sampleData.n)
              (primeKernel B.sampleData.n) p * x i +
          (1 / (p.1 : ℝ)) *
            (∑ q : BandPrime B.sampleData.n B.sampleData.W,
              (-(primeWeight B.sampleData.n q *
                    primeKernel B.sampleData.n p q)) *
                (x i - x (B.partition.band q))) +
          (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)) *
            B.primeDeviation p * x i +
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            B.primeDeviation q * x (B.partition.band q) *
              covarianceKernel
                (tPrime B.sampleData.n p.1)
                (tPrime B.sampleData.n q.1) /
                  ((p.1 : ℝ) * (q.1 : ℝ))) by
    apply Finset.sum_congr rfl
    intro p hp
    exact hinner p hp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have hqsplit (p : BandPrime B.sampleData.n B.sampleData.W) :
      (∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (-(primeWeight B.sampleData.n q *
              primeKernel B.sampleData.n p q)) *
            (x i - x (B.partition.band q))) =
        ∑ j : Band, ∑ q ∈ B.partition.data.fiber j,
          (-(primeWeight B.sampleData.n q *
              primeKernel B.sampleData.n p q)) * (x i - x j) := by
    rw [← Finset.sum_fiberwise Finset.univ B.partition.band
      (fun q : BandPrime B.sampleData.n B.sampleData.W ↦
        (-(primeWeight B.sampleData.n q *
            primeKernel B.sampleData.n p q)) *
          (x i - x (B.partition.band q)))]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro q hq
    have hqj : B.partition.band q = j := by
      simpa [Erdos390.Lemma84.WeightedBandData.fiber] using hq
    rw [hqj]
  rw [show (∑ p ∈ B.partition.data.fiber i,
      (1 / (p.1 : ℝ)) *
        (∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (-(primeWeight B.sampleData.n q *
              primeKernel B.sampleData.n p q)) *
            (x i - x (B.partition.band q)))) =
      ∑ j : Band,
        (∑ p ∈ B.partition.data.fiber i,
          ∑ q ∈ B.partition.data.fiber j,
            (1 / (p.1 : ℝ)) * primeWeight B.sampleData.n q *
              (-primeKernel B.sampleData.n p q)) *
          (x i - x j) by
    simp_rw [hqsplit, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    symm
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    ring]
  have hgraphScale :
      (∑ j : Band,
        ((1 / (B.harmonicMass i * B.bandCenter i)) *
          (∑ p ∈ B.partition.data.fiber i,
            ∑ q ∈ B.partition.data.fiber j,
              (1 / (p.1 : ℝ)) * primeWeight B.sampleData.n q *
                (-primeKernel B.sampleData.n p q))) * (x i - x j)) =
        (1 / (B.harmonicMass i * B.bandCenter i)) *
          ∑ j : Band,
            (∑ p ∈ B.partition.data.fiber i,
              ∑ q ∈ B.partition.data.fiber j,
                (1 / (p.1 : ℝ)) * primeWeight B.sampleData.n q *
                  (-primeKernel B.sampleData.n p q)) * (x i - x j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hgraphScale]
  simp only [div_eq_mul_inv]
  ring

























end BridgeData
end
end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) (x : Band → Real) (i : Band),
  Eq.{1}
    (Erdos390.Full.SquarefreeSharpBandTransfer.referenceSharpRow.{u_2}
      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B) x i)
    (HAdd.hAdd.{0, 0, 0}
      (HAdd.hAdd.{0, 0, 0}
        (HAdd.hAdd.{0, 0, 0}
          (Erdos390.Full.FiniteGraphQuotientInverse.graphOperator.{u_2}
            (Erdos390.Full.PaperBridgeFit.BridgeData.compressedPrimeGraphEdge.{u_1, u_2} B) x i)
          (Erdos390.Full.PaperBridgeFit.BridgeData.referenceResidualError.{u_1, u_2} B x i))
        (Erdos390.Full.PaperBridgeFit.BridgeData.referenceCenteringDiagonal.{u_1, u_2} B x i))
      (Erdos390.Full.PaperBridgeFit.BridgeData.referenceCenteringKernel.{u_1, u_2} B x i)) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.referenceSharpRow_eq_primeGraph_add_errors
