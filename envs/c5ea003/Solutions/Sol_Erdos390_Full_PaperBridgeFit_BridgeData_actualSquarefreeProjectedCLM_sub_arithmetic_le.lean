-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.actualSquarefreeProjectedCLM_sub_arithmetic_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:16:08.965537+00:00
-- url     : https://prove2.me/submissions/72ee3bb9-1aee-4fab-8453-a5775ec473f9

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

/- Source module: Erdos390.Full.CompressedArithmeticOperator -/
section


/-!
# The actual compressed arithmetic operator

This file packages the diagonal and double-kernel cells used in the
arithmetic bridge, performs the sharp conjugation, and proves the complete
row aggregation estimate.  The moving low row is not discarded: its
normalization is exactly the one provided by the proved normalized
quadrature modules.

No inverse or spectral gap is an input here.  The output is the explicit
operator error that is fed to the finite graph inverse and then to
`StableInverse`.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.CompressedArithmeticOperator

open DoubleKernelPrimeQuadrature DiagonalPrimeQuadrature
open FiniteGraphQuotientInverse

variable {Band : Type*} [Fintype Band]









/-! ## Endpoint-specialized arithmetic and continuum matrices -/















/-! ## Projection to the actual arithmetic gauge -/

/-- A positive weighted projection costs at most a factor two in the
pointwise norm.  This applies to the actual sharp weights
`H_j alpha_j^2`, including the moving low band. -/
theorem abs_meanProjection_sub_le
    (omega x y : Band → ℝ) (R : ℝ)
    (homega : ∀ j, 0 ≤ omega j)
    (hTotal : 0 < ∑ j, omega j)
    (hxy : ∀ j, |x j - y j| ≤ R)
    (i : Band) :
    |meanProjection omega x i - meanProjection omega y i| ≤ 2 * R := by
  have htotal0 : (∑ j, omega j) ≠ 0 := ne_of_gt hTotal
  have hmean : |weightedMean omega x - weightedMean omega y| ≤ R := by
    have hidentity :
        weightedMean omega x - weightedMean omega y =
          (∑ j, omega j * (x j - y j)) / ∑ j, omega j := by
      unfold weightedMean weightTotal
      have hsum :
          (∑ j, omega j * x j) - ∑ j, omega j * y j =
            ∑ j, omega j * (x j - y j) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [show (∑ j, omega j * x j) / (∑ j, omega j) -
          (∑ j, omega j * y j) / (∑ j, omega j) =
          ((∑ j, omega j * x j) - ∑ j, omega j * y j) /
            (∑ j, omega j) by field_simp [htotal0]]
      rw [hsum]
    rw [hidentity, abs_div, abs_of_pos hTotal]
    apply (div_le_iff₀ hTotal).2
    calc
      |∑ j, omega j * (x j - y j)| ≤
          ∑ j, |omega j * (x j - y j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, omega j * R := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, abs_of_nonneg (homega j)]
        exact mul_le_mul_of_nonneg_left (hxy j) (homega j)
      _ = R * ∑ j, omega j := by
        rw [← Finset.sum_mul]
        ring
  unfold meanProjection
  calc
    |(x i - weightedMean omega x) -
        (y i - weightedMean omega y)| =
    |(x i - y i) -
          (weightedMean omega x - weightedMean omega y)| := by ring
    _ = |(x i - y i) +
        (-(weightedMean omega x - weightedMean omega y))| := by
      rw [sub_eq_add_neg]
    _ ≤ |x i - y i| +
        |-(weightedMean omega x - weightedMean omega y)| := abs_add_le _ _
    _ = |x i - y i| +
        |weightedMean omega x - weightedMean omega y| := by rw [abs_neg]
    _ ≤ R + R := add_le_add (hxy i) hmean
    _ = 2 * R := by ring

end Erdos390.Full.CompressedArithmeticOperator

end

/- Source module: Erdos390.Full.MovingLowGaugeTransfer -/
section


/-!
# Moving-low arithmetic/continuum gauge transfer

This file isolates the normalization which is delicate at the moving low
cell.  An additive estimate for the arithmetic center is not enough because
the center itself tends to zero.  We first prove a quantitative relative
center estimate from separate estimates for `H` and `H * alpha`.  We then
write the sharp conjugate of the weighted gauge projection exactly and
compare two such projections through their normalized weights
`omega_j = H_j * alpha_j^2`.

No limiting mesh, covariance gap, or inverse is assumed in this module.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.MovingLowGaugeTransfer

open Erdos390.Lemma84
open PositiveCellTransfer
open PrimeSums
open PrimeBandQuadrature
open MovingLowMomentQuadrature

section RelativeCenter

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
variable {P : ArithmeticBandGeometry.Partition n W Band}









end RelativeCenter

section SharpProjection

variable {Band : Type*} [Fintype Band] [DecidableEq Band]

















omit [Fintype Band] [DecidableEq Band] in
theorem sharpWeight_nonneg_of_mass_nonneg
    (H alpha : Band → ℝ) (hH : ∀ j, 0 ≤ H j) (j : Band) :
    0 ≤ sharpWeight H alpha j := by
  exact mul_nonneg (hH j) (sq_nonneg (alpha j))















end SharpProjection

end Erdos390.Full.MovingLowGaugeTransfer

end

/- Source module: Erdos390.Full.PaperActualSquarefreeReference -/
section


/-!
# The actual bridge squarefree law and the canonical reference operator

This file closes two finite-probability identifications needed in Lemma 8.4.
First, a reciprocal signed profile for the medium-only law survives the
literal physical/head component tilt at the same reciprocal scale.  Second,
the partition-function-reweighted mixture of those component laws is exactly
the `BridgeData.tiltedLaw`, including the between-cell covariance.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open OmittedTiltPairChamber PaperPrimePowerChamberError
open StructuredCells ValuationScoreDomination

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)





































/-! ### Exact finite-dimensional attachment to the arithmetic inverse -/











/-- A unit sharp-row comparison gives an operator-norm comparison after the
exact arithmetic gauge projection.  The factor two is exactly the norm of
subtracting the weighted mean; it is independent of the moving-low mass and
of the number of bands. -/
theorem actualSquarefreeProjectedCLM_sub_arithmetic_le
    [Nonempty Head]
    (xi : B.ParamSpace)
    (cert : Erdos390.Full.PositiveCellTransfer.IntervalCertificate B.partition)
    {r : ℝ} (hr : 0 ≤ r)
    (hrow : ∀ (q : Band → ℝ), (∀ j, |q j| ≤ 1) → ∀ i : Band,
      |SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i -
        CompressedArithmeticOperator.arithmeticSharpOperator
          (y B.sampleData.n) cert.lower cert.upper
            B.partition.center q i| ≤ r)
    (q : PaperWeightedInverseExport.SharpGaugeSpace
      B.partition.mass B.partition.center) :
    ‖(B.actualSquarefreeProjectedCLM xi -
        ArithmeticGaugeStableInverse.projectedSharpCLM
          (CompressedArithmeticOperator.arithmeticDiagonal
            (y B.sampleData.n) cert.lower cert.upper)
          (CompressedArithmeticOperator.arithmeticKernel
            (y B.sampleData.n) cert.lower cert.upper)
          B.partition.center
          (MovingLowGaugeTransfer.sharpWeight
            B.partition.mass B.partition.center)
          (ne_of_gt (actualSharpWeightTotal_pos B))) q‖ ≤
      (2 * r) * ‖q‖ := by
  let omega := MovingLowGaugeTransfer.sharpWeight
    B.partition.mass B.partition.center
  let actualRow : (Band → ℝ) → Band → ℝ := fun b i ↦
    SquarefreeSharpBandTransfer.squarefreeSharpRow
      (B.actualValuationLaw xi) B.partition b i
  let referenceRow : (Band → ℝ) → Band → ℝ := fun b i ↦
    CompressedArithmeticOperator.arithmeticSharpOperator
      (y B.sampleData.n) cert.lower cert.upper B.partition.center b i
  have hraw (i : Band) :
      |actualRow q.1 i - referenceRow q.1 i| ≤ r * ‖q‖ := by
    by_cases hqzero : ‖q‖ = 0
    · have hq0 : q = 0 := norm_eq_zero.mp hqzero
      subst q
      have ha : actualRow (0 : Band → ℝ) i = 0 := by
        simpa only [actualRow, zero_smul, zero_mul] using
          B.squarefreeSharpRow_smul xi 0 (0 : Band → ℝ) i
      have href : referenceRow (0 : Band → ℝ) i = 0 := by
        simpa only [referenceRow, zero_smul, zero_mul] using
          ArithmeticGaugeStableInverse.sharpOperator_smul
            (CompressedArithmeticOperator.arithmeticDiagonal
              (y B.sampleData.n) cert.lower cert.upper)
            (CompressedArithmeticOperator.arithmeticKernel
              (y B.sampleData.n) cert.lower cert.upper)
            B.partition.center (0 : Band → ℝ) 0 i
      have hcoe :
          (((0 : PaperWeightedInverseExport.SharpGaugeSpace
            B.partition.mass B.partition.center) :
              PaperWeightedInverseExport.SharpGaugeSpace
                B.partition.mass B.partition.center) : Band → ℝ) = 0 := rfl
      rw [hcoe, ha, href, norm_zero, mul_zero]
      norm_num
    · have hqpos : 0 < ‖q‖ := lt_of_le_of_ne (norm_nonneg q) (Ne.symm hqzero)
      let q0 : Band → ℝ := fun j ↦ q.1 j / ‖q‖
      have hq0unit (j : Band) : |q0 j| ≤ 1 := by
        have hj : |q.1 j| ≤ ‖q‖ := by
          rw [← Real.norm_eq_abs]
          exact norm_le_pi_norm q.1 j
        dsimp only [q0]
        rw [abs_div, abs_of_pos hqpos]
        exact (div_le_one hqpos).2 hj
      have hunit := hrow q0 hq0unit i
      have hqEq : q.1 = ‖q‖ • q0 := by
        funext j
        dsimp only [q0]
        simp only [Pi.smul_apply, smul_eq_mul]
        field_simp [hqzero]
      have hactual : actualRow q.1 i = ‖q‖ * actualRow q0 i := by
        rw [hqEq]
        exact B.squarefreeSharpRow_smul xi ‖q‖ q0 i
      have hreference : referenceRow q.1 i = ‖q‖ * referenceRow q0 i := by
        rw [hqEq]
        exact ArithmeticGaugeStableInverse.sharpOperator_smul
          (CompressedArithmeticOperator.arithmeticDiagonal
            (y B.sampleData.n) cert.lower cert.upper)
          (CompressedArithmeticOperator.arithmeticKernel
            (y B.sampleData.n) cert.lower cert.upper)
          B.partition.center q0 ‖q‖ i
      rw [hactual, hreference, ← mul_sub, abs_mul, abs_of_pos hqpos]
      exact (mul_le_mul_of_nonneg_left hunit hqpos.le).trans_eq
        (mul_comm ‖q‖ r)
  have hprojected (i : Band) :
      |FiniteGraphQuotientInverse.meanProjection omega
          (actualRow q.1) i -
        FiniteGraphQuotientInverse.meanProjection omega
          (referenceRow q.1) i| ≤ 2 * (r * ‖q‖) :=
    CompressedArithmeticOperator.abs_meanProjection_sub_le omega
      (actualRow q.1) (referenceRow q.1) (r * ‖q‖)
      (fun i ↦ MovingLowGaugeTransfer.sharpWeight_nonneg_of_mass_nonneg
        B.partition.mass B.partition.center
          (fun j ↦ (B.partition.data.mass_pos j).le) i)
      (actualSharpWeightTotal_pos B) hraw i
  have hnonneg : 0 ≤ (2 * r) * ‖q‖ := by positivity
  change ‖((B.actualSquarefreeProjectedCLM xi -
        ArithmeticGaugeStableInverse.projectedSharpCLM
          (CompressedArithmeticOperator.arithmeticDiagonal
            (y B.sampleData.n) cert.lower cert.upper)
          (CompressedArithmeticOperator.arithmeticKernel
            (y B.sampleData.n) cert.lower cert.upper)
          B.partition.center omega
          (ne_of_gt (actualSharpWeightTotal_pos B))) q :
      PaperWeightedInverseExport.SharpGaugeSpace
        B.partition.mass B.partition.center)‖ ≤ (2 * r) * ‖q‖
  change ‖(((B.actualSquarefreeProjectedCLM xi -
        ArithmeticGaugeStableInverse.projectedSharpCLM
          (CompressedArithmeticOperator.arithmeticDiagonal
            (y B.sampleData.n) cert.lower cert.upper)
          (CompressedArithmeticOperator.arithmeticKernel
            (y B.sampleData.n) cert.lower cert.upper)
          B.partition.center omega
          (ne_of_gt (actualSharpWeightTotal_pos B))) q :
      PaperWeightedInverseExport.SharpGaugeSpace
        B.partition.mass B.partition.center) : Band → ℝ)‖ ≤
      (2 * r) * ‖q‖
  rw [pi_norm_le_iff_of_nonneg hnonneg]
  intro i
  rw [Real.norm_eq_abs]
  exact hprojected i |>.trans_eq (by ring)















/-! ### Reference-law row attachment

The literal global-tilt form of Lemma 7.5 is naturally obtained first for an
unguarded component mixture.  The actual bridge law is a guard-deleted
mixture with a residual physical tilt.  The next elementary estimate keeps
that identification issue outside the prime-power algebra: a weighted
prime-row comparison for the full and squarefree covariance matrices moves
the Lemma 7.5 estimate from an arbitrary reference law to the actual law.
The only moving-low loss is displayed explicitly as `rho / center i`.
-/





















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
  (cert :
    Erdos390.Full.PositiveCellTransfer.IntervalCertificate.{u_2}
      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
  {r : Real},
  LE.le.{0} (0 : Real) r →
    (∀ (q : Band → Real),
        (∀ (j : Band), LE.le.{0} (abs.{0} (q j)) (1 : Real)) →
          ∀ (i : Band),
            LE.le.{0}
              (abs.{0}
                (HSub.hSub.{0, 0, 0}
                  (Erdos390.Full.SquarefreeSharpBandTransfer.squarefreeSharpRow.{u_1, u_2}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B xi)
                    (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B) q i)
                  (Erdos390.Full.CompressedArithmeticOperator.arithmeticSharpOperator.{u_2}
                    (Erdos390.Full.ArithmeticModel.y
                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                    (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.lower.{u_2} cert)
                    (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.upper.{u_2} cert)
                    (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                    q i)))
              r) →
      ∀
        (q :
          ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
              (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
              (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))),
        LE.le.{0}
          (Norm.norm.{u_2}
            ((HSub.hSub.{u_2, u_2, u_2}
                (Erdos390.Full.PaperBridgeFit.BridgeData.actualSquarefreeProjectedCLM.{u_1, u_2} B xi)
                (Erdos390.Full.ArithmeticGaugeStableInverse.projectedSharpCLM.{u_2}
                  (Erdos390.Full.CompressedArithmeticOperator.arithmeticDiagonal.{u_2}
                    (Erdos390.Full.ArithmeticModel.y
                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                    (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.lower.{u_2} cert)
                    (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.upper.{u_2} cert))
                  (Erdos390.Full.CompressedArithmeticOperator.arithmeticKernel.{u_2}
                    (Erdos390.Full.ArithmeticModel.y
                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                    (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.lower.{u_2} cert)
                    (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.upper.{u_2} cert))
                  (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                  (Erdos390.Full.MovingLowGaugeTransfer.sharpWeight.{u_2}
                    (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                    (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))
                  (ne_of_gt.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.actualSharpWeightTotal_pos.{u_1, u_2} B))))
              q))
          (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) r) (Norm.norm.{u_2} q)) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.actualSquarefreeProjectedCLM_sub_arithmetic_le
