-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.actualTwoStageCompensatedVariance_bounds_paperScale_of_weightedRow
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:20:38.844205+00:00
-- url     : https://prove2.me/submissions/ff87974e-70fe-4047-a9dd-9c9115e689ce

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
import Theorems.Thm_Erdos390_Full_FiniteSignedQuadraticEntryTransfer_abs_matrixQuadratic_sub_le
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_actualSquarefree_relative_lower_canonicalKappa_of_varianceFactor
import Theorems.Thm_Erdos390_Full_SquarefreeCovarianceReference_abs_sigmaMixture_covII_diagonal_sub_reference_le
import Theorems.Thm_Erdos390_Full_SquarefreeCovarianceReference_abs_sigmaMixture_covII_sub_squarefreeKernelEntry_le_of_squarefree_profiles

/- Source module: Erdos390.Full.PrimePowerCovariance -/
section


/-!
# Exact prime-power covariance expansion

This file replaces the algebraic part of the prime-power transfer by proofs
for the actual valuation and divisor indicators under an actual finite
probability law.  In particular, `V = I + J` and all `JI`, `IJ`, and `JJ`
covariances are finite sums of genuine prime-power indicator covariances.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega Iota : Type*} [Fintype Omega]













theorem covariance_zero_left (mu : FiniteProbability Omega) (G : Omega → ℝ) :
    mu.covariance (fun _ ↦ 0) G = 0 := by
  simp [covariance, expect]

theorem covariance_zero_right (mu : FiniteProbability Omega) (F : Omega → ℝ) :
    mu.covariance F (fun _ ↦ 0) = 0 := by
  simp [covariance, expect]

theorem covariance_add_left (mu : FiniteProbability Omega)
    (F G H : Omega → ℝ) :
    mu.covariance (fun omega ↦ F omega + G omega) H =
      mu.covariance F H + mu.covariance G H := by
  unfold covariance
  rw [mu.expect_add F G]
  rw [show (fun omega ↦ (F omega + G omega) * H omega) =
      fun omega ↦ F omega * H omega + G omega * H omega by
    funext omega
    ring]
  rw [mu.expect_add]
  ring



theorem covariance_smul_left (mu : FiniteProbability Omega)
    (a : ℝ) (F G : Omega → ℝ) :
    mu.covariance (fun omega ↦ a * F omega) G =
      a * mu.covariance F G := by
  unfold covariance
  rw [mu.expect_smul a F]
  rw [show (fun omega ↦ a * F omega * G omega) =
      fun omega ↦ a * (F omega * G omega) by
    funext omega
    ring]
  rw [mu.expect_smul]
  ring



theorem covariance_sum_left (mu : FiniteProbability Omega)
    (s : Finset Iota) (F : Iota → Omega → ℝ) (G : Omega → ℝ) :
    mu.covariance (fun omega ↦ ∑ i ∈ s, F i omega) G =
      ∑ i ∈ s, mu.covariance (F i) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mu.covariance_zero_left]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [mu.covariance_add_left, ih]

theorem covariance_sum_right (mu : FiniteProbability Omega)
    (F : Omega → ℝ) (s : Finset Iota) (G : Iota → Omega → ℝ) :
    mu.covariance F (fun omega ↦ ∑ i ∈ s, G i omega) =
      ∑ i ∈ s, mu.covariance F (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mu.covariance_zero_right]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [mu.covariance_add_right, ih]

theorem covariance_comm (mu : FiniteProbability Omega) (F G : Omega → ℝ) :
    mu.covariance F G = mu.covariance G F := by
  unfold covariance
  congr 1
  · apply Finset.sum_congr rfl
    intro omega _
    ring
  · ring

end FiniteProbability

namespace PrimePowerCovariance

open ArithmeticModel



namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : ℕ}













































end BoundedValuationLaw

end PrimePowerCovariance

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperBridgeFit -/
section


/-!
# The finite arithmetic data in the bridge fit

This file instantiates the nonlinear finite-family layer with the actual
objects appearing in Lemmas 8.5--8.6 and Proposition 8.7: guarded smooth
structured cells, arithmetic prime bands, valuation statistics, the physical
logarithm, centered head indicators, and the compensated slow score.

The sample is the tagged disjoint union of the paper's cells.  Tagging is the
formal counterpart of the disjointification performed before normalization;
the underlying integer remains available as `Sample.value`.

All statements in this file are finite identities.  Asymptotic marked-smooth
estimates are not silently inserted as hypotheses equivalent to the desired
fit.  Where a later analytic estimate is still needed, the exact finite
quantity it must bound is exposed explicitly.
-/

open scoped BigOperators
open Metric Set

namespace Erdos390.Full

noncomputable section

open ArithmeticModel StructuredCells HeadPattern

namespace PaperBridgeFit







namespace StructuredSampleData

variable {Head : Type*} [Fintype Head]



































end StructuredSampleData



namespace BaselineAllocation

variable {Head : Type*} [Fintype Head]
  {D : StructuredSampleData Head}



















end BaselineAllocation









namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

















































































/-! ### Exact main/nuisance coordinate splitting -/





































































/-- Bilinear covariance--Jacobian identity for the concrete vector family. -/
theorem inner_jacobian [Nonempty Head]
    (xi x y : B.ParamSpace) :
    inner ℝ x (B.vectorFamily.jacobian xi y) =
      (B.q / B.L) * B.vectorFamily.scalarFamily.covariance
        (fun m => inner ℝ x (B.statistic m))
        (fun m => inner ℝ y (B.statistic m)) xi := by
  let F : B.sampleData.Sample → ℝ :=
    fun m => inner ℝ x (B.statistic m)
  have hleft : HasFDerivAt
      (fun eta => inner ℝ x (B.vectorFamily.vectorMoment eta))
      (((innerSL ℝ) x).comp (B.vectorFamily.jacobian xi)) xi := by
    exact ((innerSL ℝ) x).hasFDerivAt.comp xi
      (B.vectorFamily.hasFDerivAt_vectorMoment xi)
  have hright : HasFDerivAt
      (B.vectorFamily.scalarFamily.moment F)
      ((B.vectorFamily.baseMass / B.vectorFamily.scale) •
        B.vectorFamily.scalarFamily.covarianceScore F xi) xi :=
    B.vectorFamily.scalarFamily.hasFDerivAt_moment_covariance F xi
  have hfun : (fun eta => inner ℝ x
      (B.vectorFamily.vectorMoment eta)) =
      B.vectorFamily.scalarFamily.moment F := by
    funext eta
    exact B.vectorFamily.inner_vectorMoment x eta
  have hmaps : ((innerSL ℝ) x).comp (B.vectorFamily.jacobian xi) =
      (B.vectorFamily.baseMass / B.vectorFamily.scale) •
        B.vectorFamily.scalarFamily.covarianceScore F xi :=
    hleft.unique (hfun ▸ hright)
  have happ := congrArg
    (fun T : B.ParamSpace →L[ℝ] ℝ => T y) hmaps
  change inner ℝ x (B.vectorFamily.jacobian xi y) =
    (B.vectorFamily.baseMass / B.vectorFamily.scale) *
      B.vectorFamily.scalarFamily.covarianceScore F xi y at happ
  rw [B.vectorFamily.scalarFamily.covarianceScore_apply F xi y] at happ
  have hscore :
      (fun m => B.vectorFamily.scalarFamily.score m y) =
        fun m => inner ℝ y (B.statistic m) := by
    funext m
    simp only [VectorExponentialFamily.scalarFamily, innerSL_apply_apply]
    exact real_inner_comm _ _
  rw [hscore, B.vectorFamily_baseMass] at happ
  simpa only [vectorFamily] using happ

theorem inner_covarianceOperator [Nonempty Head]
    (xi x y : B.ParamSpace) :
    inner ℝ x (B.covarianceOperator xi y) =
      B.vectorFamily.scalarFamily.covariance
        (fun m => inner ℝ x (B.statistic m))
        (fun m => inner ℝ y (B.statistic m)) xi := by
  rw [covarianceOperator, ContinuousLinearMap.smul_apply, inner_smul_right,
    B.inner_jacobian]
  field_simp [ne_of_gt B.L_pos, ne_of_gt B.q_pos]





















theorem nuisanceCovarianceEquiv_apply [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (z : B.NuisanceSpace) :
    B.nuisanceCovarianceEquiv xi hgamma hgap z =
      B.nuisanceCovarianceOperator xi z := by
  simp [nuisanceCovarianceEquiv]



































/-! ## Exact target and moment correspondence -/















































































/-! ## Actual baseline mixture and coarse cells -/





























































































/-! ## Explicit finite diameter -/





















/-! ## A finite `ell^1` tilt bound -/













































/-! ## Target envelopes imply the ODE radius margin -/















/-! ## Concrete Proposition 8.7 endpoint -/











end BridgeData

/-! ## Non-circular order of asymptotic choices -/



end PaperBridgeFit

end


end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperPrimePowerRow -/
section


/-!
# The paper prime-band row contraction

This module specializes the actual finite-law contraction to

* the literal band `primeBand n W`,
* `t_p = log p / log y`,
* reciprocal weight `u_p = 1 / p`,
* row normalization `p`, and
* `invW = 1 / W`.

Thus every elementary prime-coordinate and prime-sum input in the final row
step of paper Lemma 7.5 is discharged here.  The remaining hypotheses are
exactly the actual `JI`, `IJ`, `JJ`, diagonal, and endpoint estimates proved
by the marked four-chamber analysis.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerRow

open ArithmeticModel Scale PrimeSums
open PrimePowerCovariance PrimePowerRowTransfer

noncomputable section

lemma tPrime_nonneg_of_mem_primeBand
    {n W p : Nat} (hn : 1 < n) (hp : p ∈ primeBand n W) :
    0 <= tPrime n p := by
  have hL : 0 < L n := L_pos hn
  have hlogy : 0 < Real.log (y n) := by
    rw [log_y (Nat.zero_lt_of_lt hn)]
    nlinarith
  have hlogp : 0 <= Real.log (p : Real) :=
    Real.log_nonneg (by exact_mod_cast (prime_of_mem_primeBand hp).one_le)
  exact div_nonneg hlogp hlogy.le

lemma tPrime_le_one_of_mem_primeBand
    {n W p : Nat} (hn : 1 < n) (hp : p ∈ primeBand n W) :
    tPrime n p <= 1 := by
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  have hL : 0 < L n := L_pos hn
  have hlogy : 0 < Real.log (y n) := by
    rw [log_y hn0]
    nlinarith
  have hpPrime := prime_of_mem_primeBand hp
  have hp0 : 0 < (p : Real) := by exact_mod_cast hpPrime.pos
  have hyfloor : (yNat n : Real) <= y n :=
    Nat.floor_le (le_of_lt (y_pos hn0))
  have hpcast : (p : Real) <= y n := by
    exact (by exact_mod_cast le_yNat_of_mem_primeBand hp :
      (p : Real) <= (yNat n : Real)).trans hyfloor
  have hlog : Real.log (p : Real) <= Real.log (y n) :=
    Real.log_le_log hp0 hpcast
  unfold tPrime
  calc
    Real.log (p : Real) / Real.log (y n) <=
        Real.log (y n) / Real.log (y n) :=
      div_le_div_of_nonneg_right hlog hlogy.le
    _ = 1 := div_self hlogy.ne'





namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : Nat}
  (law : BoundedValuationLaw Omega M)

set_option maxHeartbeats 800000



end BoundedValuationLaw

end


end Erdos390.Full.PaperPrimePowerRow

end

/- Source module: Erdos390.Full.PartitionPrimeDeviationGeometry -/
section


/-!
# Prime-deviation moments for an actual arithmetic partition

This is the sample-independent form of the arithmetic geometry in Lemma
8.6.  It works directly with `ArithmeticBandGeometry.Partition`, so the
regular mesh constructed from explicit natural endpoints can be audited
without first manufacturing the smooth-number probability space.
-/

open scoped BigOperators

namespace Erdos390.Full.ArithmeticBandGeometry.Partition

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PositiveCellTransfer
open KernelPrimeQuadrature PrimeCoordinateSecondMoment

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
  (P : ArithmeticBandGeometry.Partition n W Band)























theorem center_mem_of_coord_bounds (j : Band) {a b : ℝ}
    (hcoord : ∀ p ∈ P.data.fiber j, tPrime n p.1 ∈ Set.Icc a b) :
    P.center j ∈ Set.Icc a b := by
  have hH := P.data.mass_pos j
  have hLower : a * P.mass j ≤
      ∑ p ∈ P.data.fiber j, (1 / (p.1 : ℝ)) * tPrime n p.1 := by
    change a * (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ)) ≤ _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right
      (hcoord p hp).1 (by positivity : 0 ≤ 1 / (p.1 : ℝ))
  have hUpper :
      (∑ p ∈ P.data.fiber j, (1 / (p.1 : ℝ)) * tPrime n p.1) ≤
        P.mass j * b := by
    change _ ≤ (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ)) * b
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro p hp
    exact mul_le_mul_of_nonneg_left (hcoord p hp).2 (by positivity)
  change ((∑ p ∈ P.data.fiber j,
    (1 / (p.1 : ℝ)) * tPrime n p.1) / P.mass j) ∈ Set.Icc a b
  exact ⟨(le_div_iff₀ hH).2 hLower,
    (div_le_iff₀ hH).2 (by simpa only [mul_comm] using hUpper)⟩









end

end Erdos390.Full.ArithmeticBandGeometry.Partition

end

/- Source module: Erdos390.Full.PaperWeightedInverseExport -/
section


/-!
# Export of the sharp inverse in the paper's weighted band norm

The finite graph argument is naturally written after the diagonal change of
variables `b j = alpha j * q j`.  This file records the change of variables
as an exact linear equivalence between the two arithmetic gauges.  It also
proves that the projected raw row-normalized matrix is conjugate to
`projectedSharpLinearMap`.  Consequently an inverse estimate in the ordinary
supremum norm of `q` is literally the paper estimate
`max_j |b_j| / |alpha_j|` for the unscaled band coefficient `b`.

There is no limiting centre and no continuum gauge in this algebraic export.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.PaperWeightedInverseExport

open ArithmeticGaugeStableInverse
open CompressedArithmeticOperator
open FiniteGraphQuotientInverse
open FiniteGraphStableInverse
open MovingLowGaugeTransfer

variable {Band : Type*} [Fintype Band]















theorem paperSharpNorm_eq_piNorm
    (H alpha : Band → ℝ) (hAlpha : ∀ j, alpha j ≠ 0)
    (b : RawGaugeSpace H alpha) :
    paperSharpNorm H alpha hAlpha b =
      ‖fun j ↦ b.1 j / alpha j‖ := by
  rfl























/-- Coordinate form of the preceding weighted bound. -/
theorem abs_raw_coordinate_le_paperSharpNorm
    (H alpha : Band → ℝ) (hAlpha : ∀ j, alpha j ≠ 0)
    (b : RawGaugeSpace H alpha) (j : Band) :
    |b.1 j| ≤ |alpha j| * paperSharpNorm H alpha hAlpha b := by
  have hcoord : |b.1 j / alpha j| ≤
      paperSharpNorm H alpha hAlpha b := by
    rw [paperSharpNorm_eq_piNorm]
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm (fun k ↦ b.1 k / alpha k) j
  have hrewrite : |b.1 j| = |alpha j| * |b.1 j / alpha j| := by
    rw [abs_div]
    field_simp [abs_ne_zero.mpr (hAlpha j)]
  rw [hrewrite]
  exact mul_le_mul_of_nonneg_left hcoord (abs_nonneg (alpha j))

end Erdos390.Full.PaperWeightedInverseExport

end

/- Source module: Erdos390.Full.PaperCompensatedCoefficientBounds -/
section


/-!
# Actual compensated-prime coefficient bounds for Lemma 8.6

This file specializes the elementary coefficient ledger to the literal
arithmetic prime partition.  The regression vector is an element of the
paper's exact arithmetic gauge

`sum_j H_j * alpha_j * q_j = 0`,

and the compensated coefficient is literally
`c_p = (alpha_{j(p)} - t_p) - q_{j(p)}`.  Thus none of the three norms below
is represented by an abstract array or stored in a certificate.

The sole regression input is the sharp norm estimate produced by the
weighted inverse and the row estimate.  All remaining estimates are derived
from the actual prime sums and the already proved canonical-mesh moment
bounds.
-/

open scoped BigOperators

namespace Erdos390.Full.ArithmeticBandGeometry.Partition

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport PrimeSums

noncomputable section

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
  (P : Partition n W Band)













theorem center_mem_zero_one (hn : 1 < n) (j : Band) :
    P.center j ∈ Set.Icc (0 : ℝ) 1 := by
  apply P.center_mem_of_coord_bounds j
  intro p hp
  have hpBand : p.1 ∈ primeBand n W := p.2
  exact ⟨PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand hn hpBand,
    PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand hn hpBand⟩











/-- Exact first-moment identity for the arithmetic centers. -/
theorem sum_mass_mul_center_eq_bandTReciprocalSum :
    (∑ j : Band, P.mass j * P.center j) =
      bandTReciprocalSum n W := by
  have hcenter (j : Band) :
      P.mass j * P.center j =
        ∑ p ∈ P.data.fiber j,
          (1 / (p.1 : ℝ)) * tPrime n p.1 := by
    change P.data.mass j *
        ((∑ p ∈ P.data.fiber j,
          (1 / (p.1 : ℝ)) * tPrime n p.1) / P.data.mass j) = _
    field_simp [ne_of_gt (P.data.mass_pos j)]
  calc
    (∑ j : Band, P.mass j * P.center j) =
        ∑ j : Band, ∑ p ∈ P.data.fiber j,
          (1 / (p.1 : ℝ)) * tPrime n p.1 := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hcenter j
    _ = ∑ p : BandPrime n W,
          (1 / (p.1 : ℝ)) * tPrime n p.1 := by
            rw [← Finset.sum_fiberwise Finset.univ P.band
              (fun p : BandPrime n W ↦
                (1 / (p.1 : ℝ)) * tPrime n p.1)]
            apply Finset.sum_congr rfl
            intro j hj
            rfl
    _ = bandTReciprocalSum n W := by
          unfold bandTReciprocalSum
          have hattach := Finset.sum_attach (primeBand n W)
            (fun p ↦ tPrime n p / (p : ℝ))
          rw [← hattach]
          apply Finset.sum_congr rfl
          intro p hp
          ring

/-- Exact reindexing of a bandwise coefficient through the actual partition. -/
theorem sum_regressionCoefficient_eq_sum_band
    (q : RawGaugeSpace P.mass P.center)
    (F : ℝ → ℝ) :
    (∑ p : BandPrime n W,
      (1 / (p.1 : ℝ)) * F (P.regressionCoefficient q p)) =
      ∑ j : Band, P.mass j * F (q.1 j) := by
  unfold regressionCoefficient
  rw [← Finset.sum_fiberwise Finset.univ P.band
    (fun p : BandPrime n W ↦ (1 / (p.1 : ℝ)) * F (q.1 (P.band p)))]
  apply Finset.sum_congr rfl
  intro j hj
  change (∑ p ∈ P.data.fiber j,
      (1 / (p.1 : ℝ)) * F (q.1 (P.band p))) =
    P.mass j * F (q.1 j)
  calc
    _ = ∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * F (q.1 j) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hpj : P.band p = j :=
            (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mp hp
          rw [hpj]
    _ = P.mass j * F (q.1 j) := by
          rw [← Finset.sum_mul]
          rfl

/-- The literal weighted square of the actual deviation is definitionally
the arithmetic partition variance. -/
theorem deviationL2Sq_eq_variance :
    (∑ p : BandPrime n W,
      (1 / (p.1 : ℝ)) * (P.deviation p) ^ 2) = P.variance := by
  change (∑ p : BandPrime n W,
      (1 / (p.1 : ℝ)) * (P.deviation p) ^ 2) =
    ∑ p : BandPrime n W,
      (1 / (p.1 : ℝ)) * P.data.cellDeviation p *
        P.data.cellDeviation p
  apply Finset.sum_congr rfl
  intro p hp
  change (1 / (p.1 : ℝ)) *
      (P.center (P.band p) - tPrime n p.1) ^ 2 =
    (1 / (p.1 : ℝ)) *
      (P.center (P.band p) - tPrime n p.1) *
        (P.center (P.band p) - tPrime n p.1)
  rw [pow_two]
  ring

/-- A sharp regression bound gives the literal pointwise band bound. -/
theorem abs_regressionCoefficient_le
    (hn : 1 < n) (q : RawGaugeSpace P.mass P.center)
    {C w : ℝ}
    (hsharp : paperSharpNorm P.mass P.center (P.center_ne_zero hn) q ≤ C * w)
    (p : BandPrime n W) :
    |P.regressionCoefficient q p| ≤ C * w := by
  have hcoord := abs_raw_coordinate_le_paperSharpNorm
    P.mass P.center (P.center_ne_zero hn) q (P.band p)
  have hcenter := (P.center_mem_zero_one hn (P.band p)).2
  have hcenter0 := (P.center_mem_zero_one hn (P.band p)).1
  have habsCenter : |P.center (P.band p)| ≤ 1 := by
    rw [abs_of_nonneg hcenter0]
    exact hcenter
  calc
    |P.regressionCoefficient q p| = |q.1 (P.band p)| := rfl
    _ ≤ |P.center (P.band p)| *
        paperSharpNorm P.mass P.center (P.center_ne_zero hn) q := hcoord
    _ ≤ 1 * paperSharpNorm P.mass P.center (P.center_ne_zero hn) q :=
      mul_le_mul_of_nonneg_right habsCenter (norm_nonneg _)
    _ ≤ C * w := by simpa using hsharp

/-- The actual weighted `L¹` norm of the regression vector. -/
theorem regressionL1_le
    (hn : 1 < n) (q : RawGaugeSpace P.mass P.center)
    {C w K : ℝ} (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hsharp : paperSharpNorm P.mass P.center (P.center_ne_zero hn) q ≤ C * w)
    (hbandT : bandTReciprocalSum n W ≤ K) :
    P.regressionL1 q ≤ C * K * w := by
  have hcw : 0 ≤ C * w := mul_nonneg hC hw
  have hsum : P.regressionL1 q ≤
      (C * w) * ∑ j : Band, P.mass j * P.center j := by
    rw [regressionL1, P.sum_regressionCoefficient_eq_sum_band q abs]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hcoord := abs_raw_coordinate_le_paperSharpNorm
      P.mass P.center (P.center_ne_zero hn) q j
    have hcenter0 := (P.center_mem_zero_one hn j).1
    have hq : |q.1 j| ≤ P.center j * (C * w) := by
      calc
        |q.1 j| ≤ |P.center j| *
            paperSharpNorm P.mass P.center (P.center_ne_zero hn) q := hcoord
        _ ≤ |P.center j| * (C * w) :=
          mul_le_mul_of_nonneg_left hsharp (abs_nonneg _)
        _ = P.center j * (C * w) := by rw [abs_of_nonneg hcenter0]
    calc
      P.mass j * |q.1 j| ≤ P.mass j * (P.center j * (C * w)) :=
        mul_le_mul_of_nonneg_left hq (P.data.mass_pos j).le
      _ = (C * w) * (P.mass j * P.center j) := by ring
  rw [P.sum_mass_mul_center_eq_bandTReciprocalSum] at hsum
  calc
    P.regressionL1 q ≤ (C * w) * bandTReciprocalSum n W := hsum
    _ ≤ (C * w) * K := mul_le_mul_of_nonneg_left hbandT hcw
    _ = C * K * w := by ring

/-- The actual weighted quadratic norm of the regression vector. -/
theorem regressionL2Sq_le
    (hn : 1 < n) (q : RawGaugeSpace P.mass P.center)
    {C w K : ℝ} (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hsharp : paperSharpNorm P.mass P.center (P.center_ne_zero hn) q ≤ C * w)
    (hbandT : bandTReciprocalSum n W ≤ K) :
    P.regressionL2Sq q ≤ C ^ 2 * K * w ^ 2 := by
  have hcw : 0 ≤ C * w := mul_nonneg hC hw
  have hsum : P.regressionL2Sq q ≤
      (C * w) ^ 2 * ∑ j : Band, P.mass j * P.center j := by
    rw [regressionL2Sq, P.sum_regressionCoefficient_eq_sum_band q
      (fun x ↦ x ^ 2)]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hcoord := abs_raw_coordinate_le_paperSharpNorm
      P.mass P.center (P.center_ne_zero hn) q j
    have hcenter := P.center_mem_zero_one hn j
    have hqabs : |q.1 j| ≤ P.center j * (C * w) := by
      calc
        |q.1 j| ≤ |P.center j| *
            paperSharpNorm P.mass P.center (P.center_ne_zero hn) q := hcoord
        _ ≤ |P.center j| * (C * w) :=
          mul_le_mul_of_nonneg_left hsharp (abs_nonneg _)
        _ = P.center j * (C * w) := by rw [abs_of_nonneg hcenter.1]
    have hqsq : (q.1 j) ^ 2 ≤ P.center j * (C * w) ^ 2 := by
      have hsq : (q.1 j) ^ 2 ≤ (P.center j * (C * w)) ^ 2 := by
        have hright0 : 0 ≤ P.center j * (C * w) :=
          mul_nonneg hcenter.1 hcw
        have hprod := mul_nonneg (sub_nonneg.mpr hqabs)
          (add_nonneg (abs_nonneg (q.1 j)) hright0)
        rw [← sq_abs (q.1 j)]
        nlinarith
      have hcenterSq : P.center j ^ 2 ≤ P.center j := by
        have hprod := mul_nonneg hcenter.1 (sub_nonneg.mpr hcenter.2)
        nlinarith
      calc
        (q.1 j) ^ 2 ≤ (P.center j * (C * w)) ^ 2 := hsq
        _ = P.center j ^ 2 * (C * w) ^ 2 := by ring
        _ ≤ P.center j * (C * w) ^ 2 :=
          mul_le_mul_of_nonneg_right hcenterSq (sq_nonneg _)
    calc
      P.mass j * (q.1 j) ^ 2 ≤
          P.mass j * (P.center j * (C * w) ^ 2) :=
        mul_le_mul_of_nonneg_left hqsq (P.data.mass_pos j).le
      _ = (C * w) ^ 2 * (P.mass j * P.center j) := by ring
  rw [P.sum_mass_mul_center_eq_bandTReciprocalSum] at hsum
  calc
    P.regressionL2Sq q ≤ (C * w) ^ 2 * bandTReciprocalSum n W := hsum
    _ ≤ (C * w) ^ 2 * K :=
      mul_le_mul_of_nonneg_left hbandT (sq_nonneg _)
    _ = C ^ 2 * K * w ^ 2 := by ring

/-- All three paper coefficient bounds for the literal compensated vector.
The constants are explicit and independent of the number of bands. -/
theorem compensatedCoefficient_three_bounds
    (hn : 1 < n) (q : RawGaugeSpace P.mass P.center)
    {C w K : ℝ} (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hsharp : paperSharpNorm P.mass P.center (P.center_ne_zero hn) q ≤ C * w)
    (hbandT : bandTReciprocalSum n W ≤ K)
    (hdevSup : ∀ p : BandPrime n W, |P.deviation p| ≤ w)
    (hdevL1 : P.totalL1 ≤ 7 * w)
    (hdevL2 : P.variance ≤ 4 * w ^ 2) :
    (∀ p : BandPrime n W,
        |P.compensatedCoefficient q p| ≤ (1 + C) * w) ∧
      P.compensatedL1 q ≤ (7 + C * K) * w ∧
      P.compensatedL2Sq q ≤
        2 * (4 + C ^ 2 * K) * w ^ 2 := by
  have hqSup : ∀ p : BandPrime n W,
      |P.regressionCoefficient q p| ≤ C * w :=
    P.abs_regressionCoefficient_le hn q hsharp
  have hqL1 : P.regressionL1 q ≤ C * K * w :=
    P.regressionL1_le hn q hC hw hsharp hbandT
  have hqL2 : P.regressionL2Sq q ≤ C ^ 2 * K * w ^ 2 :=
    P.regressionL2Sq_le hn q hC hw hsharp hbandT
  constructor
  · intro p
    unfold compensatedCoefficient
    calc
      |P.deviation p - P.regressionCoefficient q p| ≤
          |P.deviation p| + |P.regressionCoefficient q p| := abs_sub _ _
      _ ≤ w + C * w := add_le_add (hdevSup p) (hqSup p)
      _ = (1 + C) * w := by ring
  constructor
  · unfold compensatedL1
    calc
      (∑ p : BandPrime n W,
          (1 / (p.1 : ℝ)) * |P.compensatedCoefficient q p|) ≤
          ∑ p : BandPrime n W,
            ((1 / (p.1 : ℝ)) * |P.deviation p| +
              (1 / (p.1 : ℝ)) * |P.regressionCoefficient q p|) := by
        apply Finset.sum_le_sum
        intro p hp
        unfold compensatedCoefficient
        simpa only [mul_add] using
          (mul_le_mul_of_nonneg_left (abs_sub
              (P.deviation p) (P.regressionCoefficient q p))
            (one_div_nonneg.mpr
              (show (0 : ℝ) ≤ (p.1 : ℝ) by positivity)))
      _ = (∑ p : BandPrime n W,
          (1 / (p.1 : ℝ)) * |P.deviation p|) +
          ∑ p : BandPrime n W,
            (1 / (p.1 : ℝ)) * |P.regressionCoefficient q p| :=
        Finset.sum_add_distrib
      _ ≤ 7 * w + C * K * w := add_le_add hdevL1 hqL1
      _ = (7 + C * K) * w := by ring
  · unfold compensatedL2Sq
    calc
      (∑ p : BandPrime n W,
          (1 / (p.1 : ℝ)) * (P.compensatedCoefficient q p) ^ 2) ≤
          ∑ p : BandPrime n W,
            (2 * ((1 / (p.1 : ℝ)) * P.deviation p ^ 2) +
              2 * ((1 / (p.1 : ℝ)) *
                (P.regressionCoefficient q p) ^ 2)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hsquare : (P.deviation p - P.regressionCoefficient q p) ^ 2 ≤
            2 * P.deviation p ^ 2 +
              2 * (P.regressionCoefficient q p) ^ 2 := by
          nlinarith [sq_nonneg (P.deviation p + P.regressionCoefficient q p)]
        unfold compensatedCoefficient
        calc
          (1 / (p.1 : ℝ)) *
              (P.deviation p - P.regressionCoefficient q p) ^ 2 ≤
            (1 / (p.1 : ℝ)) *
              (2 * P.deviation p ^ 2 +
                2 * (P.regressionCoefficient q p) ^ 2) :=
              mul_le_mul_of_nonneg_left hsquare
                (one_div_nonneg.mpr
                  (show (0 : ℝ) ≤ (p.1 : ℝ) by positivity))
          _ = 2 * ((1 / (p.1 : ℝ)) * P.deviation p ^ 2) +
              2 * ((1 / (p.1 : ℝ)) *
                (P.regressionCoefficient q p) ^ 2) := by ring
      _ = 2 * (∑ p : BandPrime n W,
            (1 / (p.1 : ℝ)) * P.deviation p ^ 2) +
          2 * (∑ p : BandPrime n W,
            (1 / (p.1 : ℝ)) * (P.regressionCoefficient q p) ^ 2) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ = 2 * P.variance + 2 * P.regressionL2Sq q := by
        rw [P.deviationL2Sq_eq_variance]
        rfl
      _ ≤ 2 * (4 * w ^ 2) + 2 * (C ^ 2 * K * w ^ 2) := by
        linarith
      _ = 2 * (4 + C ^ 2 * K) * w ^ 2 := by ring

end

end Erdos390.Full.ArithmeticBandGeometry.Partition

end

/- Source module: Erdos390.Full.PaperActualCompensatedRegression -/
section


/-!
# The actual two-stage compensated regression in Lemma 8.6

The objects in this file live on the genuine guard-deleted, tilted finite
probability space from `PaperBridgeFit`.  In particular, the nuisance
coefficient is not an abstract vector satisfying a normal equation: it is
defined by applying the inverse of the proved actual nuisance covariance
operator to the literal covariance vector of the post-band-regression score.

This file proves the exact finite identities used before the analytic
`w^2` comparison: the prime-coefficient expansion, nuisance normal equation,
orthogonality, Schur variance identity, and marked-row decomposition.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport
open PrimePowerCovariance

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)















theorem partition_compensatedCoefficient_eq
    (q : B.RawBandGauge)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    B.partition.compensatedCoefficient q p =
      B.actualCompensatedCoefficient q p := rfl











theorem inner_nuisanceCovarianceVector [Nonempty Head]
    (xi : B.ParamSpace) (F : B.sampleData.Sample → ℝ)
    (z : B.NuisanceSpace) :
    inner ℝ z (B.nuisanceCovarianceVector xi F) =
      (B.tiltedLaw xi).covariance
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m)) F := by
  rw [PiLp.inner_apply]
  change (∑ c : NuisanceCoord B.HeadIndex,
      B.nuisanceCovarianceVector xi F c * z c) = _
  rw [show (fun m ↦ inner ℝ z (B.nuisanceStatistic m)) =
      fun m ↦ ∑ c : NuisanceCoord B.HeadIndex,
        z c * B.nuisanceStatistic m c by
    funext m
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro c hc
    rw [RCLike.inner_apply]
    simp only [starRingEnd_apply, star_trivial]
    ring]
  rw [FiniteProbability.covariance_sum_left]
  apply Finset.sum_congr rfl
  intro c hc
  rw [FiniteProbability.covariance_smul_left]
  simp only [B.nuisanceCovarianceVector_apply]
  ring

/-- Bilinear form of the actual nuisance covariance block. -/
theorem inner_nuisanceCovarianceOperator_bilinear [Nonempty Head]
    (xi : B.ParamSpace) (z a : B.NuisanceSpace) :
    inner ℝ z (B.nuisanceCovarianceOperator xi a) =
      (B.tiltedLaw xi).covariance
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m))
        (fun m ↦ inner ℝ a (B.nuisanceStatistic m)) := by
  have hadjoint :
      inner ℝ z (B.nuisanceCovarianceOperator xi a) =
        inner ℝ (B.nuisanceEmbed z)
          (B.covarianceOperator xi (B.nuisanceEmbed a)) := by
    simpa only [nuisanceCovarianceOperator,
      ContinuousLinearMap.comp_apply] using
      (ContinuousLinearMap.adjoint_inner_right B.nuisanceEmbeddingCLM z
        (B.covarianceOperator xi (B.nuisanceEmbeddingCLM a)))
  rw [hadjoint, B.inner_covarianceOperator]
  congr 1
  · funext m
    rw [B.statistic_eq_combine m,
      B.inner_nuisanceEmbed_combine z (B.nuisanceStatistic m)
        (B.mainStatistic m)]
  · funext m
    rw [B.statistic_eq_combine m,
      B.inner_nuisanceEmbed_combine a (B.nuisanceStatistic m)
        (B.mainStatistic m)]



theorem nuisanceCoefficientOfScore_solve [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F : B.sampleData.Sample → ℝ) :
    B.nuisanceCovarianceOperator xi
        (B.nuisanceCoefficientOfScore xi hgamma hgap F) =
      B.nuisanceCovarianceVector xi F := by
  rw [← B.nuisanceCovarianceEquiv_apply xi hgamma hgap]
  exact (B.nuisanceCovarianceEquiv xi hgamma hgap).apply_symm_apply _

/-- Coercivity of the literal nuisance covariance block bounds the actual
regression coefficient by the norm of its literal covariance vector. -/
theorem nuisanceCoefficientOfScore_norm_le [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F : B.sampleData.Sample → ℝ) :
    ‖B.nuisanceCoefficientOfScore xi hgamma hgap F‖ ≤
      ‖B.nuisanceCovarianceVector xi F‖ / gamma := by
  let a := B.nuisanceCoefficientOfScore xi hgamma hgap F
  have hcoer := hgap a
  rw [B.nuisanceCoefficientOfScore_solve xi hgamma hgap F] at hcoer
  have hinner : inner ℝ a (B.nuisanceCovarianceVector xi F) ≤
      ‖a‖ * ‖B.nuisanceCovarianceVector xi F‖ :=
    real_inner_le_norm _ _
  by_cases ha : ‖a‖ = 0
  · change ‖a‖ ≤ ‖B.nuisanceCovarianceVector xi F‖ / gamma
    rw [ha]
    exact div_nonneg (norm_nonneg _) (le_of_lt hgamma)
  · have hapos : 0 < ‖a‖ :=
      lt_of_le_of_ne (norm_nonneg a) (Ne.symm ha)
    have hcancel : gamma * ‖a‖ ≤
        ‖B.nuisanceCovarianceVector xi F‖ := by
      have hmul : (gamma * ‖a‖) * ‖a‖ ≤
          ‖B.nuisanceCovarianceVector xi F‖ * ‖a‖ := by
        calc
          (gamma * ‖a‖) * ‖a‖ = gamma * ‖a‖ ^ 2 := by ring
          _ ≤ inner ℝ a (B.nuisanceCovarianceVector xi F) := hcoer
          _ ≤ ‖B.nuisanceCovarianceVector xi F‖ * ‖a‖ := by
            simpa [mul_comm] using hinner
      exact (mul_le_mul_iff_right₀ hapos).mp (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hmul)
    change ‖a‖ ≤ ‖B.nuisanceCovarianceVector xi F‖ / gamma
    exact (le_div_iff₀ hgamma).2 (by simpa [mul_comm] using hcancel)

/-- The exact Schur loss is nonnegative and is bounded by the squared norm
of the literal nuisance covariance vector divided by the nuisance gap. -/
theorem nuisanceRegressionLoss_bounds [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F : B.sampleData.Sample → ℝ) :
    0 ≤ inner ℝ (B.nuisanceCoefficientOfScore xi hgamma hgap F)
        (B.nuisanceCovarianceVector xi F) ∧
    inner ℝ (B.nuisanceCoefficientOfScore xi hgamma hgap F)
        (B.nuisanceCovarianceVector xi F) ≤
      ‖B.nuisanceCovarianceVector xi F‖ ^ 2 / gamma := by
  let a := B.nuisanceCoefficientOfScore xi hgamma hgap F
  have hsolve := B.nuisanceCoefficientOfScore_solve xi hgamma hgap F
  have hcoer := hgap a
  rw [hsolve] at hcoer
  have hlower : 0 ≤ inner ℝ a (B.nuisanceCovarianceVector xi F) := by
    exact le_trans
      (mul_nonneg (le_of_lt hgamma) (sq_nonneg ‖a‖)) hcoer
  have hnorm := B.nuisanceCoefficientOfScore_norm_le xi hgamma hgap F
  have hinner : inner ℝ a (B.nuisanceCovarianceVector xi F) ≤
      ‖a‖ * ‖B.nuisanceCovarianceVector xi F‖ :=
    real_inner_le_norm _ _
  refine ⟨hlower, hinner.trans ?_⟩
  calc
    ‖a‖ * ‖B.nuisanceCovarianceVector xi F‖ ≤
        (‖B.nuisanceCovarianceVector xi F‖ / gamma) *
          ‖B.nuisanceCovarianceVector xi F‖ :=
      mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ = ‖B.nuisanceCovarianceVector xi F‖ ^ 2 / gamma := by ring



private theorem covariance_sub_right
    {Omega : Type*} [Fintype Omega]
    (mu : FiniteProbability Omega) (F G H : Omega → ℝ) :
    mu.covariance F (fun omega ↦ G omega - H omega) =
      mu.covariance F G - mu.covariance F H := by
  have hfun : (fun omega ↦ G omega - H omega) =
      fun omega ↦ G omega + (-1 : ℝ) * H omega := by
    funext omega
    ring
  rw [hfun, mu.covariance_add_right, mu.covariance_smul_right]
  ring

/-- Exact Schur orthogonality of the actual nuisance residual. -/
theorem nuisanceResidualScore_covariance_zero [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F : B.sampleData.Sample → ℝ) (z : B.NuisanceSpace) :
    (B.tiltedLaw xi).covariance
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m))
        (B.nuisanceResidualScore xi hgamma hgap F) = 0 := by
  let a := B.nuisanceCoefficientOfScore xi hgamma hgap F
  unfold nuisanceResidualScore
  rw [covariance_sub_right]
  have hfirst := B.inner_nuisanceCovarianceVector xi F z
  have hsecond := B.inner_nuisanceCovarianceOperator_bilinear xi z a
  have hsolve := congrArg (fun v : B.NuisanceSpace ↦ inner ℝ z v)
    (B.nuisanceCoefficientOfScore_solve xi hgamma hgap F)
  change inner ℝ z (B.nuisanceCovarianceOperator xi a) =
    inner ℝ z (B.nuisanceCovarianceVector xi F) at hsolve
  rw [hfirst, hsecond] at hsolve
  exact sub_eq_zero.mpr hsolve.symm







/-- Exact Schur-variance identity.  This is an equality at finite `n`; the
subsequent continuum and prime-power arguments only estimate its two terms. -/
theorem nuisanceResidualScore_variance_identity [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F : B.sampleData.Sample → ℝ) :
    (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap F)
        (B.nuisanceResidualScore xi hgamma hgap F) =
      (B.tiltedLaw xi).covariance F F -
        inner ℝ (B.nuisanceCoefficientOfScore xi hgamma hgap F)
          (B.nuisanceCovarianceVector xi F) := by
  let a := B.nuisanceCoefficientOfScore xi hgamma hgap F
  let Zscore : B.sampleData.Sample → ℝ :=
    fun m ↦ inner ℝ a (B.nuisanceStatistic m)
  have horth := B.nuisanceResidualScore_covariance_zero
    xi hgamma hgap F a
  have hcomm : (B.tiltedLaw xi).covariance
      (B.nuisanceResidualScore xi hgamma hgap F) Zscore = 0 := by
    simpa only [Zscore] using
      ((B.tiltedLaw xi).covariance_comm
        (B.nuisanceResidualScore xi hgamma hgap F) Zscore).trans horth
  have hF : F = fun m ↦
      B.nuisanceResidualScore xi hgamma hgap F m + Zscore m := by
    funext m
    unfold nuisanceResidualScore
    simp only [a, Zscore]
    ring
  have hvarZ := B.inner_nuisanceCovarianceOperator_bilinear xi a a
  have hsolve := congrArg (fun v : B.NuisanceSpace ↦ inner ℝ a v)
    (B.nuisanceCoefficientOfScore_solve xi hgamma hgap F)
  change inner ℝ a (B.nuisanceCovarianceOperator xi a) =
    inner ℝ a (B.nuisanceCovarianceVector xi F) at hsolve
  rw [hvarZ] at hsolve
  rw [show (B.tiltedLaw xi).covariance F F =
      (B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceResidualScore xi hgamma hgap F m + Zscore m)
        (fun m ↦ B.nuisanceResidualScore xi hgamma hgap F m + Zscore m) by
    rw [← hF] ]
  rw [FiniteProbability.covariance_add_left,
    FiniteProbability.covariance_add_right,
    FiniteProbability.covariance_add_right]
  rw [horth, hcomm, zero_add, add_zero]
  linarith



/-- A coordinatewise nuisance-row estimate gives the Euclidean estimate used
in the second regression.  The only loss is the square root of the fixed
nuisance dimension.  Keeping this conversion explicit is useful in the
marked-row argument: the analytic input is naturally proved one physical or
head coordinate at a time, whereas the regression coefficient is controlled
in Euclidean norm. -/
theorem nuisanceCovarianceVector_norm_le_sqrt_card_mul [Nonempty Head]
    (xi : B.ParamSpace) (F : B.sampleData.Sample → ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (hcoord : ∀ c : NuisanceCoord B.HeadIndex,
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c) F| ≤ K) :
    ‖B.nuisanceCovarianceVector xi F‖ ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K := by
  have hsq : ‖B.nuisanceCovarianceVector xi F‖ ^ 2 ≤
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, B.nuisanceCovarianceVector_apply]
    calc
      (∑ c : NuisanceCoord B.HeadIndex,
          |(B.tiltedLaw xi).covariance
            (fun m ↦ B.nuisanceStatistic m c) F| ^ 2) ≤
          ∑ _c : NuisanceCoord B.HeadIndex, K ^ 2 := by
        apply Finset.sum_le_sum
        intro c hc
        exact pow_le_pow_left₀ (abs_nonneg _) (hcoord c) 2
      _ = (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K ^ 2 := by
        simp
  have hcard : 0 ≤
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) := by positivity
  have hsqrt :
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)) ^ 2 =
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) :=
    Real.sq_sqrt hcard
  have hrhs0 : 0 ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K :=
    mul_nonneg (Real.sqrt_nonneg _) hK
  have hrhsSq :
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K) ^ 2 =
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K ^ 2 := by
    rw [mul_pow, hsqrt]
  rw [← hrhsSq] at hsq
  nlinarith [norm_nonneg (B.nuisanceCovarianceVector xi F)]

/-- A reciprocal marked row controls the covariance with the entire literal
post-band prime score by the actual compensated weighted `L¹` norm.  This is
the finite summation step used twice in Lemma 8.6: once for the nuisance
coefficient and once for a marked valuation row. -/
theorem abs_covariance_nuisance_postBandPrimeScore_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    (c : NuisanceCoord B.HeadIndex) {Cmarked : ℝ}
    (hmarked : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (p.1 : ℝ))) :
    |(B.tiltedLaw xi).covariance
      (fun m ↦ B.nuisanceStatistic m c)
      (B.postBandPrimeScore q)| ≤
        Cmarked * B.partition.compensatedL1 q := by
  let mu := B.tiltedLaw xi
  let Z : B.sampleData.Sample → ℝ :=
    fun m ↦ B.nuisanceStatistic m c
  have hsum :
      mu.covariance Z (B.postBandPrimeScore q) =
        ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          B.actualCompensatedCoefficient q p *
            mu.covariance Z
              (fun m ↦ valuation p.1 (B.sampleData.value m)) := by
    unfold postBandPrimeScore
    rw [show (fun m ↦ ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.actualCompensatedCoefficient q p *
          valuation p.1 (B.sampleData.value m)) =
      fun m ↦ ∑ p ∈ (Finset.univ :
          Finset (BandPrime B.sampleData.n B.sampleData.W)),
        B.actualCompensatedCoefficient q p *
          valuation p.1 (B.sampleData.value m) by simp]
    rw [mu.covariance_sum_right]
    apply Finset.sum_congr rfl
    intro p hp
    rw [mu.covariance_smul_right]
  change |mu.covariance Z (B.postBandPrimeScore q)| ≤ _
  rw [hsum]
  calc
    |∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.actualCompensatedCoefficient q p *
          mu.covariance Z
            (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          |B.actualCompensatedCoefficient q p *
            mu.covariance Z
              (fun m ↦ valuation p.1 (B.sampleData.value m))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        |B.actualCompensatedCoefficient q p| *
          (Cmarked * (1 / (p.1 : ℝ))) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hmarked p) (abs_nonneg _)
    _ = Cmarked * B.partition.compensatedL1 q := by
      unfold ArithmeticBandGeometry.Partition.compensatedL1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [B.partition_compensatedCoefficient_eq q p]
      ring

/-- Vector form of the reciprocal-row summation.  Thus the covariance vector
needed for the nuisance regression is a consequence of the same componentwise
marked estimates and of the already established coefficient `L¹` bound; it is
not a second independent analytic assumption. -/
theorem nuisanceCovarianceVector_postBand_norm_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {Cmarked : ℝ} (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (p.1 : ℝ))) :
    ‖B.nuisanceCovarianceVector xi (B.postBandPrimeScore q)‖ ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        (Cmarked * B.partition.compensatedL1 q) := by
  have hL1nonneg : 0 ≤ B.partition.compensatedL1 q := by
    unfold ArithmeticBandGeometry.Partition.compensatedL1
    apply Finset.sum_nonneg
    intro p hp
    exact mul_nonneg (by positivity) (abs_nonneg _)
  apply B.nuisanceCovarianceVector_norm_le_sqrt_card_mul
    xi (B.postBandPrimeScore q) (mul_nonneg hCmarked hL1nonneg)
  intro c
  exact B.abs_covariance_nuisance_postBandPrimeScore_le_of_marked
    xi q c (fun p ↦ hmarked c p)

/-- Scaled form used in the final `w²` assembly. -/
theorem nuisanceCovarianceVector_postBand_norm_le_of_marked_and_l1
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {Cmarked CL1 w : ℝ} (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (p.1 : ℝ)))
    (hL1 : B.partition.compensatedL1 q ≤ CL1 * w) :
    ‖B.nuisanceCovarianceVector xi (B.postBandPrimeScore q)‖ ≤
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        (Cmarked * CL1)) * w := by
  have hraw := B.nuisanceCovarianceVector_postBand_norm_le_of_marked
    xi q hCmarked hmarked
  calc
    ‖B.nuisanceCovarianceVector xi (B.postBandPrimeScore q)‖ ≤
        Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * B.partition.compensatedL1 q) := hraw
    _ ≤ Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * (CL1 * w)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hL1 hCmarked)
        (Real.sqrt_nonneg _)
    _ = (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * CL1)) * w := by ring





end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.FiniteProbabilityMixtureTilt -/
section


/-!
# Exponential tilts of finite tagged mixtures

A global exponential tilt of a finite mixture is not obtained by retaining
the old cell weights.  The exact new weights contain the cell partition
functions.  This file proves that identity before any covariance is formed,
so common-profile estimates can safely be averaged across cells.
-/

open scoped BigOperators

namespace Erdos390.Full
namespace FiniteProbability

noncomputable section

variable {Cell : Type*} [Fintype Cell]
  {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]









/-- Pointwise exact factorization of the globally tilted density into the
new cell weight and the componentwise tilted density. -/
theorem exponentialTilt_sigmaMixture_mass
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (S : Sigma Omega → ℝ) (x : Sigma Omega) :
    ((sigmaMixture weight mu).exponentialTilt S).mass x =
      (sigmaMixture (tiltedSigmaWeight weight mu S)
        (fun c => (mu c).exponentialTilt (sigmaCellScore S c))).mass x := by
  rcases x with ⟨c, x⟩
  let Zc := (mu c).expPartition (sigmaCellScore S c)
  let Z := (sigmaMixture weight mu).expPartition S
  have hcellZ : Zc ≠ 0 :=
    ne_of_gt ((mu c).expPartition_pos (sigmaCellScore S c))
  have hglobalZ : Z ≠ 0 :=
    ne_of_gt ((sigmaMixture weight mu).expPartition_pos S)
  change weight.mass c * (mu c).mass x * Real.exp (S ⟨c, x⟩) / Z =
    (weight.mass c * Zc / Z) *
      ((mu c).mass x * Real.exp (S ⟨c, x⟩) / Zc)
  field_simp [hcellZ, hglobalZ]

private theorem finiteProbability_ext
    {Alpha : Type*} [Fintype Alpha]
    {mu nu : FiniteProbability Alpha} (h : mu.mass = nu.mass) : mu = nu := by
  cases mu with
  | mk massMu nonnegMu sumMu =>
    cases nu with
    | mk massNu nonnegNu sumNu =>
      dsimp only at h
      subst massNu
      rfl

/-- Equality of the two finite probability laws, not merely equality of
their expectations. -/
theorem exponentialTilt_sigmaMixture
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (S : Sigma Omega → ℝ) :
    (sigmaMixture weight mu).exponentialTilt S =
      sigmaMixture (tiltedSigmaWeight weight mu S)
        (fun c => (mu c).exponentialTilt (sigmaCellScore S c)) := by
  apply finiteProbability_ext
  funext x
  exact exponentialTilt_sigmaMixture_mass weight mu S x





end

end FiniteProbability
end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperBridgeCellTiltDecomposition -/
section


/-!
# Exact cell-mixture decomposition of the paper bridge tilt

The analytic marked-cell estimates are stated for uniform probability laws on
individual structured cells and their finite tagged mixtures.  This file proves
the exact identification with the probability law carried by `BridgeData`.
Nothing asymptotic is used: the guard-deleted cells, their actual cardinalities,
the baseline cell masses, and the global partition-function reweighting all
remain literal.

This is also the place where the remaining nuisance tilt is exposed.  After the
medium-prime score has been split off, the physical/head factor is an explicit
second exponential tilt; it is not silently absorbed into the prime fugacity.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open FiniteProbability ArithmeticModel ArithmeticBandGeometry

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



























/-- The actual bridge law, with the global cell partition functions handled
correctly, is a tagged mixture of the componentwise tilted guard-deleted
cell laws. -/
theorem tiltedLaw_eq_tiltedSigmaMixture [Nonempty Head]
    (xi : B.ParamSpace) :
    B.tiltedLaw xi =
      sigmaMixture
        (tiltedSigmaWeight B.baselineCellProbability
          B.guardedCellProbability (B.scaledBridgeScore xi))
        (fun c ↦ (B.guardedCellProbability c).exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c)) := by
  rw [B.tiltedLaw_eq_exponentialTilt_baseline]
  exact exponentialTilt_sigmaMixture _ _ _



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperPrimePowerChamberError -/
section


/-!
# Explicit chamber-error majorants for prime-power aggregation

This file replaces the nested restoration ledger by one scalar remainder at
the natural product-reciprocal scale.  The scalar is explicit, uniform over
all moving primes and exponents, and retains the vanishing omitted-score and
`1 / log n` factors needed before the harmonic prime sum is taken.
-/

namespace Erdos390.Full.PaperPrimePowerChamberError

open ArithmeticModel Scale HeadPattern
open OmittedTiltPairChamber FullTiltPairChamber
open LocalFugacityBounds TwoLocalRestorationBound
open PaperTwoLocalRestorationBound PaperScaleMarkedCell
open FullTiltPrimePowerCovariance

noncomputable section

























theorem pairCovarianceScale_nonneg {E : ℝ} (hE : 0 ≤ E) :
    0 ≤ pairCovarianceScale E := by
  unfold pairCovarianceScale
  have hrho : 0 ≤ 1 / DickmanBasic.rho DickmanBasic.U := by
    exact one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
  positivity















end

end Erdos390.Full.PaperPrimePowerChamberError

end

/- Source module: Erdos390.Full.PaperPrimePowerRelativeQuadratic -/
section


/-!
# Relative prime-power quadratic transfer for Lemma 8.6

Lemma 7.5 supplies a genuine weighted row estimate for the difference
between full valuation covariance and squarefree covariance.  This file
proves, by finite summation, that the row estimate gives an error at the
relative `w^2` scale for the actual compensated coefficient vector.  The
proof does not replace `sum |Cov|` by `|sum Cov|`.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerRelativeQuadratic

open ArithmeticModel PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerLemma75

noncomputable section

variable {Omega : Type*} [Fintype Omega] {M : ℕ}





theorem full_sub_squarefree_eq
    (law : BoundedValuationLaw Omega M) (S : Finset ℕ)
    (c : ℕ → ℝ) :
    fullValuationQuadratic law S c - squarefreeQuadratic law S c =
      ∑ p ∈ S, ∑ q ∈ S,
        c p * c q * (law.covVV p q - law.covII p q) := by
  unfold fullValuationQuadratic squarefreeQuadratic
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  ring

theorem fullValuationQuadratic_eq_covariance
    (law : BoundedValuationLaw Omega M) (S : Finset ℕ)
    (c : ℕ → ℝ) :
    fullValuationQuadratic law S c =
      law.probability.covariance
        (fun omega ↦ ∑ p ∈ S, c p * law.V p omega)
        (fun omega ↦ ∑ p ∈ S, c p * law.V p omega) := by
  rw [law.probability.covariance_sum_left]
  unfold fullValuationQuadratic covVV
  apply Finset.sum_congr rfl
  intro p hp
  rw [law.probability.covariance_sum_right]
  apply Finset.sum_congr rfl
  intro q hq
  rw [law.probability.covariance_smul_left,
    law.probability.covariance_smul_right]
  ring

theorem squarefreeQuadratic_eq_covariance
    (law : BoundedValuationLaw Omega M) (S : Finset ℕ)
    (c : ℕ → ℝ) :
    squarefreeQuadratic law S c =
      law.probability.covariance
        (fun omega ↦ ∑ p ∈ S, c p * law.I p omega)
        (fun omega ↦ ∑ p ∈ S, c p * law.I p omega) := by
  rw [law.probability.covariance_sum_left]
  unfold squarefreeQuadratic covII
  apply Finset.sum_congr rfl
  intro p hp
  rw [law.probability.covariance_sum_right]
  apply Finset.sum_congr rfl
  intro q hq
  rw [law.probability.covariance_smul_left,
    law.probability.covariance_smul_right]
  ring

/-- A weighted row bound and the literal coefficient `L∞`/`L¹` bounds imply
a relative quadratic error. -/
theorem abs_full_sub_squarefree_le_of_row
    (law : BoundedValuationLaw Omega M)
    {n W : ℕ} (c : ℕ → ℝ) {Csup CL1 w R : ℝ}
    (hCsup : 0 ≤ Csup) (hCL1 : 0 ≤ CL1)
    (hw : 0 ≤ w) (hR : 0 ≤ R)
    (hcSup : ∀ p ∈ primeBand n W, |c p| ≤ Csup * w)
    (hcL1 : (∑ p ∈ primeBand n W,
      |c p| * (1 / (p : ℝ))) ≤ CL1 * w)
    (hrow : ∀ p ∈ primeBand n W,
      (p : ℝ) * ∑ q ∈ primeBand n W,
        |law.covVV p q - law.covII p q| ≤ R) :
    |fullValuationQuadratic law (primeBand n W) c -
        squarefreeQuadratic law (primeBand n W) c| ≤
      (Csup * CL1) * R * w ^ 2 := by
  have hCw : 0 ≤ Csup * w := mul_nonneg hCsup hw
  have hLw : 0 ≤ CL1 * w := mul_nonneg hCL1 hw
  rw [full_sub_squarefree_eq]
  calc
    |∑ p ∈ primeBand n W, ∑ q ∈ primeBand n W,
        c p * c q * (law.covVV p q - law.covII p q)| ≤
        ∑ p ∈ primeBand n W,
          |∑ q ∈ primeBand n W,
            c p * c q * (law.covVV p q - law.covII p q)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ primeBand n W,
        |c p| * (Csup * w) *
          (∑ q ∈ primeBand n W,
            |law.covVV p q - law.covII p q|) := by
      apply Finset.sum_le_sum
      intro p hp
      calc
        |∑ q ∈ primeBand n W,
            c p * c q * (law.covVV p q - law.covII p q)| ≤
            ∑ q ∈ primeBand n W,
              |c p * c q * (law.covVV p q - law.covII p q)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ q ∈ primeBand n W,
            |c p| * |c q| *
              |law.covVV p q - law.covII p q| := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [abs_mul, abs_mul]
        _ ≤ ∑ q ∈ primeBand n W,
            |c p| * (Csup * w) *
              |law.covVV p q - law.covII p q| := by
          apply Finset.sum_le_sum
          intro q hq
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hcSup q hq) (abs_nonneg _))
            (abs_nonneg _)
        _ = |c p| * (Csup * w) *
            (∑ q ∈ primeBand n W,
              |law.covVV p q - law.covII p q|) := by
          rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ primeBand n W,
        (|c p| * (1 / (p : ℝ))) * (Csup * w) * R := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPosNat : 0 < p := (prime_of_mem_primeBand hp).pos
      have hpPos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPosNat
      have hrowDiv :
          (∑ q ∈ primeBand n W,
            |law.covVV p q - law.covII p q|) ≤ R / (p : ℝ) := by
        exact (le_div_iff₀ hpPos).2 (by
          simpa only [mul_comm] using hrow p hp)
      have hmult : 0 ≤ |c p| * (Csup * w) :=
        mul_nonneg (abs_nonneg _) hCw
      calc
        |c p| * (Csup * w) *
            (∑ q ∈ primeBand n W,
              |law.covVV p q - law.covII p q|) ≤
            |c p| * (Csup * w) * (R / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hrowDiv hmult
        _ = (|c p| * (1 / (p : ℝ))) * (Csup * w) * R := by
          field_simp [ne_of_gt hpPos]
    _ = (Csup * w) * R *
        (∑ p ∈ primeBand n W, |c p| * (1 / (p : ℝ))) := by
      rw [← Finset.sum_mul]
      have hfactor :
          (∑ p ∈ primeBand n W,
            |c p| * (1 / (p : ℝ)) * (Csup * w)) =
          (Csup * w) *
            ∑ p ∈ primeBand n W, |c p| * (1 / (p : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      rw [hfactor]
      ring
    _ ≤ (Csup * w) * R * (CL1 * w) := by
      exact mul_le_mul_of_nonneg_left hcL1
        (mul_nonneg hCw hR)
    _ = (Csup * CL1) * R * w ^ 2 := by ring













end

end Erdos390.Full.PaperPrimePowerRelativeQuadratic

end

/- Source module: Erdos390.Full.PaperActualPrimePowerRelative -/
section


/-!
# Actual bridge specialization of the relative prime-power transfer

This file constructs the bounded valuation law directly from the genuine
guard-deleted tilted bridge sample.  It then applies the weighted row theorem
to the literal post-regression coefficients from Lemma 8.6.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerLemma75
open PaperPrimePowerRelativeQuadratic
open PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)











/-- The subtype and natural-prime `L¹` sums are exactly the same finite sum. -/
theorem compensatedNatL1_eq_partition
    (q : B.RawBandGauge) :
    (∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.actualCompensatedNatCoefficient q p| * (1 / (p : ℝ))) =
      B.partition.compensatedL1 q := by
  unfold ArithmeticBandGeometry.Partition.compensatedL1
  have hattach := Finset.sum_attach
    (primeBand B.sampleData.n B.sampleData.W)
    (fun p ↦ |B.actualCompensatedNatCoefficient q p| * (1 / (p : ℝ)))
  rw [← hattach]
  apply Finset.sum_congr rfl
  intro p hp
  rw [B.actualCompensatedNatCoefficient_of_mem q p.2]
  rw [B.partition_compensatedCoefficient_eq q p]
  ring

/-- The primewise post-band score is the full-valuation score of the actual
bounded valuation law. -/
theorem postBandPrimeScore_eq_actualValuationSum [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    (m : B.sampleData.Sample) :
    B.postBandPrimeScore q m =
      ∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
        B.actualCompensatedNatCoefficient q p *
          (B.actualValuationLaw xi).V p m := by
  unfold postBandPrimeScore actualValuationLaw
    PrimePowerCovariance.BoundedValuationLaw.V
  have hattach := Finset.sum_attach
    (primeBand B.sampleData.n B.sampleData.W)
    (fun p ↦ B.actualCompensatedNatCoefficient q p *
      valuation p (B.sampleData.value m))
  rw [← hattach]
  apply Finset.sum_congr rfl
  intro p hp
  rw [B.actualCompensatedNatCoefficient_of_mem q p.2]



/-- Exact identification of the two finite covariance quadratic forms with
the actual full-valuation and squarefree scores. -/
theorem actualQuadratics_eq_covariances [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge) :
    fullValuationQuadratic (B.actualValuationLaw xi)
        (primeBand B.sampleData.n B.sampleData.W)
        (B.actualCompensatedNatCoefficient q) =
      (B.tiltedLaw xi).covariance
        (B.postBandPrimeScore q) (B.postBandPrimeScore q) ∧
    squarefreeQuadratic (B.actualValuationLaw xi)
        (primeBand B.sampleData.n B.sampleData.W)
        (B.actualCompensatedNatCoefficient q) =
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q) := by
  constructor
  · rw [fullValuationQuadratic_eq_covariance]
    congr 1 <;> funext m <;>
      exact (B.postBandPrimeScore_eq_actualValuationSum xi q m).symm
  · rw [squarefreeQuadratic_eq_covariance]
    rfl







end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.SquarefreeCovarianceReference -/
section


/-!
# Signed squarefree covariance transfer to the Dickman kernel

The prime-power ledger only needs an absolute upper bound.  Lemma 8.4 needs
the stronger *signed* comparison between the genuine divisor-indicator
covariance and the arithmetic Poisson--Dickman matrix.  This file derives
that comparison from the same common one- and two-divisor profiles, before
any band averaging.  In particular, the between-cell covariance of the
tagged mixture is retained exactly.
-/

namespace Erdos390.Full.SquarefreeCovarianceReference

open ArithmeticModel Scale
open FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open OmittedTiltPairChamber
open PaperScaleMarkedCell PaperPrimePowerChamberError
open FullTiltPrimePowerCovariance
open FixedFiniteMixturePrimePower
open DickmanFourMarkProductKernel ConditionedPoissonLimit

noncomputable section

variable {Cell : Type*} [Fintype Cell]
  {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]
  {M : ℕ}













/-- The signed one- and two-divisor comparisons assembled into the single
entrywise estimate consumed by the sharp band-row theorem. -/
theorem sigmaMixture_squarefree_reference_entry_bound_of_squarefree_profiles
    {E CKernel : ℝ} (hE : 0 ≤ E)
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M)
    {n W : ℕ} (hn : 1 < n)
    (hpair : ∀ c p, p ∈ primeBand n W →
      ∀ q, q ∈ (primeBand n W).erase p →
      |(law c).probability.expect
          (fun omega ↦ divInd (pairPower p q 1 1) ((law c).value omega)) -
        paperDivisibilityMain n (pairPower p q 1 1)| ≤
          E * pairWeight p q 1 1)
    (hsingle : ∀ c p, p ∈ primeBand n W →
      |(law c).probability.expect
          (fun omega ↦ divInd p ((law c).value omega)) -
        paperDivisibilityMain n p| ≤ E * singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand n W,
      |covarianceKernel (tPrime n p) (tPrime n p)| ≤ CKernel) :
    let mix := sigmaMixture weight law
    ∀ p q : ArithmeticBandGeometry.BandPrime n W,
      |mix.covII p.1 q.1 - squarefreeReferenceEntry n p.1 q.1| ≤
        (4 * pairCovarianceScale E) /
            ((p.1 : ℝ) * (q.1 : ℝ)) +
          (if p = q then
            (2 * E) / (p.1 : ℝ) +
              ((1 / DickmanBasic.rho DickmanBasic.U + 2 * E) ^ 2 +
                CKernel) / (p.1 : ℝ) ^ 2
          else 0) := by
  dsimp only
  let mix := sigmaMixture weight law
  intro p q
  by_cases hpq : p = q
  · subst q
    rw [if_pos rfl]
    have hdiag := abs_sigmaMixture_covII_diagonal_sub_reference_le
      hE weight law hn p.2 (fun c ↦ hsingle c p.1 p.2)
      (hKernel p.1 p.2)
    have hcovNonneg : 0 ≤ pairCovarianceScale E :=
      pairCovarianceScale_nonneg hE
    have hpPos : (0 : ℝ) < p.1 := by
      exact_mod_cast (prime_of_mem_primeBand p.2).pos
    have hextra : 0 ≤
        (4 * pairCovarianceScale E) / ((p.1 : ℝ) * (p.1 : ℝ)) :=
      div_nonneg (mul_nonneg (by norm_num) hcovNonneg)
        (mul_nonneg hpPos.le hpPos.le)
    exact hdiag.trans (by
      have htwo : 2 * E / (p.1 : ℝ) = (2 * E) / (p.1 : ℝ) := rfl
      rw [htwo]
      linarith)
  · rw [if_neg hpq]
    have hqErase : q.1 ∈ (primeBand n W).erase p.1 :=
      Finset.mem_erase.mpr ⟨fun h ↦ hpq (Subtype.ext h.symm), q.2⟩
    have hoff :=
      abs_sigmaMixture_covII_sub_squarefreeKernelEntry_le_of_squarefree_profiles
      hE weight law hn p.2 hqErase
      (fun c ↦ hpair c p.1 p.2 q.1 hqErase)
      (fun c ↦ hsingle c p.1 p.2)
      (fun c ↦ hsingle c q.1 q.2)
    have href : squarefreeReferenceEntry n p.1 q.1 =
        squarefreeKernelEntry n p.1 q.1 := by
      rw [squarefreeReferenceEntry, if_neg (by
        intro h
        exact hpq (Subtype.ext h))]
    rw [href]
    have hrewrite :
        pairCovarianceScale E * pairWeight p.1 q.1 1 1 =
          (4 * pairCovarianceScale E) /
            ((p.1 : ℝ) * (q.1 : ℝ)) := by
      unfold pairWeight
      norm_num
      ring
    simpa only [mix, hrewrite, add_zero] using hoff



end

end Erdos390.Full.SquarefreeCovarianceReference

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





















private theorem boundedValuationLaw_ext
    {Omega : Type*} [Fintype Omega] {M : ℕ}
    {law₁ law₂ : BoundedValuationLaw Omega M}
    (hprob : law₁.probability = law₂.probability)
    (hvalue : law₁.value = law₂.value) : law₁ = law₂ := by
  cases law₁
  cases law₂
  dsimp only at hprob hvalue
  subst_vars
  rfl

/-- The component mixture just constructed is literally the paper's global
tilted bounded valuation law.  In particular no between-cell covariance is
discarded. -/
theorem sigmaMixture_actualComponentValuationLaw_eq_actualValuationLaw
    [Nonempty Head] (xi : B.ParamSpace) :
    let weight := tiltedSigmaWeight B.baselineCellProbability
      B.guardedCellProbability (B.scaledBridgeScore xi)
    sigmaMixture weight (B.actualComponentValuationLaw xi) =
      B.actualValuationLaw xi := by
  dsimp only
  apply boundedValuationLaw_ext
  · exact congrArg id (B.tiltedLaw_eq_tiltedSigmaMixture xi).symm
  · rfl













/-! ### Exact finite-dimensional attachment to the arithmetic inverse -/



























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

/- Source module: Erdos390.Full.PrimeSquarefreeDirichletGeometry -/
section


/-!
# Prime-level Dirichlet geometry for the squarefree reference covariance

The squarefree Dickman reference matrix is conjugated here on the literal
finite prime band.  The conjugating coordinate is `x_p = c_p / t_p`, the
vertex weight is `t_p / p`, and the quotient metric is `t_p^2 / p`.
Consequently the graph distance to a constant is exactly

`sum_p (c_p - mu * t_p)^2 / p`.

All identities are finite and exact.  The only analytic input in the final
anchor theorem is the already proved uniform negativity of the Dickman
kernel quotient on a fixed interior block.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PrimeSquarefreeDirichletGeometry

open ArithmeticModel
open ConditionedPoissonLimit PoissonDickmanWeightedInverse
open PoissonDickmanDirichlet
open FiniteAnchoredDirichletQuadratic
open SquarefreeCovarianceReference



variable {n W : ℕ}

































/-- Exact identification with the signed reference entries.  The extra
diagonal multiplier is counted once, while the kernel diagonal remains in
the full double sum. -/
theorem primeReferenceQuadratic_eq_entryQuadratic
    (c : PrimeIndex n W → ℝ) :
    primeReferenceQuadratic n c = primeReferenceEntryQuadratic n c := by
  classical
  have hentry (p q : PrimeIndex n W) :
      squarefreeReferenceEntry n p.1 q.1 =
        squarefreeKernelEntry n p.1 q.1 +
          if p = q then DickmanBasic.F (tPrime n p.1) / (p.1 : ℝ) else 0 := by
    by_cases hpq : p = q
    · subst q
      simp [squarefreeReferenceEntry]
      ring
    · have hpqVal : p.1 ≠ q.1 := by
        intro h
        exact hpq (Subtype.ext h)
      simp [squarefreeReferenceEntry, hpq, hpqVal]
  have hdiag (p : PrimeIndex n W) :
      (∑ q, c p * c q *
        (if p = q then DickmanBasic.F (tPrime n p.1) / (p.1 : ℝ) else 0)) =
          DickmanBasic.F (tPrime n p.1) / (p.1 : ℝ) * c p ^ 2 := by
    rw [Finset.sum_eq_single p]
    · simp
      ring
    · intro q hq hqp
      simp [Ne.symm hqp]
    · simp
  have hkernel :
      (∑ p, ∑ q,
        covarianceKernel (tPrime n p.1) (tPrime n q.1) /
            ((p.1 : ℝ) * (q.1 : ℝ)) * c p * c q) =
        ∑ p, ∑ q, c p * c q * squarefreeKernelEntry n p.1 q.1 := by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    unfold squarefreeKernelEntry
    ring
  unfold primeReferenceQuadratic primeReferenceEntryQuadratic
  simp_rw [hentry, mul_add, Finset.sum_add_distrib, hdiag]
  rw [hkernel, add_comm]

















end Erdos390.Full.PrimeSquarefreeDirichletGeometry

end

/- Source module: Erdos390.Full.PaperSquarefreeSlowQuadraticLower -/
section


/-!
# The literal squarefree slow lower bound

This file specializes the prime-level Dirichlet geometry to the paper's
actual compensated coefficient

`c_p = alpha_{j(p)} - t_p - q_{j(p)}`.

It proves three separate facts, so that their analytic inputs can be audited
independently:

1. the graph quotient distance is exactly the arithmetic `physicalSq`;
2. a relative finite row-residual estimate is absorbed by the literal
   compensated `L²` ledger;
3. signed entrywise squarefree-reference errors aggregate in the correct
   product-reciprocal and diagonal norms.

In particular, no squarefree variance lower bound occurs as a hypothesis.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PaperSquarefreeSlowQuadraticLower

open ArithmeticModel ArithmeticBandGeometry
open ArithmeticBandGeometry.Partition
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open FiniteSignedQuadraticEntryTransfer
open SquarefreeCovarianceReference
open SquarefreeReferenceOperatorIdentification
open PrimePowerCovariance

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
variable (P : Partition n W Band)









theorem weightedL1_compensated_eq
    (q : PaperWeightedInverseExport.RawGaugeSpace P.mass P.center) :
    weightedL1 (reciprocalWeight (n := n) (W := W))
        (compensatedPrimeCoefficient P q) =
      P.compensatedL1 q := by
  rfl

theorem weightedL2Sq_compensated_eq
    (q : PaperWeightedInverseExport.RawGaugeSpace P.mass P.center) :
    weightedL2Sq (reciprocalWeight (n := n) (W := W))
        (compensatedPrimeCoefficient P q) =
      P.compensatedL2Sq q := by
  rfl

/-- The second reciprocal diagonal costs one explicit cutoff factor. -/
theorem weightedL2SqSecond_le_invCutoff_mul_weightedL2Sq
    (hW : 0 < W) (c : Prime n W → ℝ) :
    weightedL2SqSecond (reciprocalWeight (n := n) (W := W)) c ≤
      (1 / (W : ℝ)) *
        weightedL2Sq (reciprocalWeight (n := n) (W := W)) c := by
  unfold weightedL2SqSecond weightedL2Sq reciprocalWeight
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have hWp : (W : ℝ) ≤ (p.1 : ℝ) := by
    exact_mod_cast (cutoff_lt_of_mem_primeBand p.2).le
  have hinv : 1 / (p.1 : ℝ) ≤ 1 / (W : ℝ) :=
    one_div_le_one_div_of_le hWR hWp
  have hrecip : 0 ≤ 1 / (p.1 : ℝ) := by positivity
  have hsq : 0 ≤ c p ^ 2 := sq_nonneg _
  calc
    (1 / (p.1 : ℝ)) ^ 2 * c p ^ 2 =
        (1 / (p.1 : ℝ)) * ((1 / (p.1 : ℝ)) * c p ^ 2) := by ring
    _ ≤ (1 / (W : ℝ)) * ((1 / (p.1 : ℝ)) * c p ^ 2) :=
      mul_le_mul_of_nonneg_right hinv (mul_nonneg hrecip hsq)
    _ = (1 / (W : ℝ)) * (1 / (p.1 : ℝ) * c p ^ 2) := by ring









/-- The separated reference quadratic is exactly the matrix quadratic of
the signed reference entries used in the squarefree profile theorem. -/
theorem matrixQuadratic_squarefreeReferenceEntry_eq_primeReference
    (c : Prime n W → ℝ) :
    matrixQuadratic
        (fun p r : Prime n W ↦ squarefreeReferenceEntry n p.1 r.1) c =
      primeReferenceQuadratic n c := by
  change primeReferenceEntryQuadratic n c = primeReferenceQuadratic n c
  exact (primeReferenceQuadratic_eq_entryQuadratic c).symm

/-- Signed entrywise profile estimates aggregate to a quantitative
squarefree-reference quadratic estimate. -/
theorem abs_subtypeSquarefreeQuadratic_sub_primeReference_le
    {Omega : Type*} [Fintype Omega] {M : ℕ}
    (law : BoundedValuationLaw Omega M) (c : Prime n W → ℝ)
    {epsilonOff epsilonDiag epsilonSecond : ℝ}
    (hentry : ∀ p r : Prime n W,
      |law.covII p.1 r.1 - squarefreeReferenceEntry n p.1 r.1| ≤
        epsilonOff * reciprocalWeight p * reciprocalWeight r +
          if p = r then
            epsilonDiag * reciprocalWeight p +
              epsilonSecond * reciprocalWeight p ^ 2
          else 0) :
    |subtypeSquarefreeQuadratic law c - primeReferenceQuadratic n c| ≤
      epsilonOff * weightedL1 (reciprocalWeight (n := n) (W := W)) c ^ 2 +
        epsilonDiag * weightedL2Sq
          (reciprocalWeight (n := n) (W := W)) c +
        epsilonSecond * weightedL2SqSecond
          (reciprocalWeight (n := n) (W := W)) c := by
  unfold subtypeSquarefreeQuadratic
  rw [← matrixQuadratic_squarefreeReferenceEntry_eq_primeReference]
  exact abs_matrixQuadratic_sub_le
    (fun p r : Prime n W ↦ law.covII p.1 r.1)
    (fun p r : Prime n W ↦ squarefreeReferenceEntry n p.1 r.1)
    (reciprocalWeight (n := n) (W := W)) c hentry

/-- A uniform bound for `F` and the signed Dickman kernel gives a completely
explicit upper bound for the finite reference quadratic. -/
theorem abs_primeReferenceQuadratic_le
    (c : Prime n W → ℝ) {CF CKernel : ℝ}
    (hF : ∀ p : Prime n W, |DickmanBasic.F (tPrime n p.1)| ≤ CF)
    (hKernel : ∀ p r : Prime n W,
      |ConditionedPoissonLimit.covarianceKernel
        (tPrime n p.1) (tPrime n r.1)| ≤ CKernel) :
    |primeReferenceQuadratic n c| ≤
      CKernel * weightedL1 reciprocalWeight c ^ 2 +
        CF * weightedL2Sq reciprocalWeight c := by
  have hentry : ∀ p r : Prime n W,
      |squarefreeReferenceEntry n p.1 r.1 - 0| ≤
        CKernel * reciprocalWeight p * reciprocalWeight r +
          if p = r then CF * reciprocalWeight p + 0 * reciprocalWeight p ^ 2
          else 0 := by
    intro p r
    have hpR : (0 : ℝ) < p.1 := by
      exact_mod_cast (prime_of_mem_primeBand p.2).pos
    have hrR : (0 : ℝ) < r.1 := by
      exact_mod_cast (prime_of_mem_primeBand r.2).pos
    by_cases hpr : p = r
    · subst r
      rw [if_pos rfl, sub_zero]
      unfold squarefreeReferenceEntry squarefreeKernelEntry reciprocalWeight
      rw [if_pos rfl]
      calc
        |DickmanBasic.F (tPrime n p.1) / (p.1 : ℝ) +
            ConditionedPoissonLimit.covarianceKernel
              (tPrime n p.1) (tPrime n p.1) /
                ((p.1 : ℝ) * (p.1 : ℝ))| ≤
            |DickmanBasic.F (tPrime n p.1) / (p.1 : ℝ)| +
              |ConditionedPoissonLimit.covarianceKernel
                (tPrime n p.1) (tPrime n p.1) /
                  ((p.1 : ℝ) * (p.1 : ℝ))| := abs_add_le _ _
        _ ≤ CF * (1 / (p.1 : ℝ)) +
              CKernel * (1 / (p.1 : ℝ)) * (1 / (p.1 : ℝ)) := by
          rw [abs_div, abs_of_pos hpR, abs_div,
            abs_of_pos (mul_pos hpR hpR)]
          calc
            |DickmanBasic.F (tPrime n p.1)| / (p.1 : ℝ) +
                |ConditionedPoissonLimit.covarianceKernel
                  (tPrime n p.1) (tPrime n p.1)| /
                    ((p.1 : ℝ) * (p.1 : ℝ)) ≤
              CF / (p.1 : ℝ) + CKernel / ((p.1 : ℝ) * (p.1 : ℝ)) :=
                add_le_add
                  (div_le_div_of_nonneg_right (hF p) hpR.le)
                  (div_le_div_of_nonneg_right (hKernel p p)
                    (mul_nonneg hpR.le hpR.le))
            _ = CF * (1 / (p.1 : ℝ)) +
                CKernel * (1 / (p.1 : ℝ)) * (1 / (p.1 : ℝ)) := by
              field_simp [ne_of_gt hpR]
        _ = CKernel * (1 / (p.1 : ℝ)) * (1 / (p.1 : ℝ)) +
              (CF * (1 / (p.1 : ℝ)) + 0 * (1 / (p.1 : ℝ)) ^ 2) := by
          ring
    · rw [if_neg hpr, sub_zero]
      have hval : p.1 ≠ r.1 := by
        intro h
        exact hpr (Subtype.ext h)
      unfold squarefreeReferenceEntry squarefreeKernelEntry reciprocalWeight
      rw [if_neg hval, abs_div, abs_of_pos (mul_pos hpR hrR)]
      calc
        |ConditionedPoissonLimit.covarianceKernel
            (tPrime n p.1) (tPrime n r.1)| /
              ((p.1 : ℝ) * (r.1 : ℝ)) ≤
            CKernel / ((p.1 : ℝ) * (r.1 : ℝ)) :=
          div_le_div_of_nonneg_right (hKernel p r)
            (mul_nonneg hpR.le hrR.le)
        _ = CKernel * (1 / (p.1 : ℝ)) * (1 / (r.1 : ℝ)) + 0 := by
          field_simp [ne_of_gt hpR, ne_of_gt hrR]
          ring
  have hbound := abs_matrixQuadratic_sub_le
    (fun p r : Prime n W ↦ squarefreeReferenceEntry n p.1 r.1)
    (fun _p _r : Prime n W ↦ 0) reciprocalWeight c hentry
  rw [matrixQuadratic_squarefreeReferenceEntry_eq_primeReference] at hbound
  simpa [matrixQuadratic] using hbound

end Erdos390.Full.PaperSquarefreeSlowQuadraticLower

end

/- Source module: Erdos390.Full.PaperActualSquarefreeSlowLower -/
section


/-!
# Actual squarefree slow lower from signed local profiles

The local one- and two-divisor profiles are first assembled through the
literal sigma mixture, so between-cell covariance is retained.  The resulting
signed entry estimate is then combined with the finite prime Dirichlet lower
from `PaperSquarefreeSlowQuadraticLower`.  Thus the genuine squarefree
variance lower is a conclusion, not an analytic hypothesis.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PaperBridgeFit

open ArithmeticModel ArithmeticBandGeometry
open FiniteProbability OmittedTiltPairChamber
open PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open FixedFiniteMixturePrimePower
open PaperPrimePowerChamberError
open PaperSquarefreeSlowQuadraticLower
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open FiniteSignedQuadraticEntryTransfer
open SquarefreeCovarianceReference
open PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)











/-- Local signed profiles imply the literal actual-law entry comparison.
The proof passes through the exact sigma mixture, so it includes all
between-component covariance terms. -/
theorem actual_squarefree_reference_entry_bound_of_profiles
    [Nonempty Head]
    (xi : B.ParamSpace)
    {Eprofile CKernel : ℝ} (hEprofile : 0 ≤ Eprofile)
    (hpair : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ q, q ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p q 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p q 1 1)| ≤
        Eprofile * pairWeight p q 1 1)
    (hsingle : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤ CKernel) :
    ∀ p r : BandPrime B.sampleData.n B.sampleData.W,
      |(B.actualValuationLaw xi).covII p.1 r.1 -
          squarefreeReferenceEntry B.sampleData.n p.1 r.1| ≤
        (4 * pairCovarianceScale Eprofile) *
            reciprocalWeight p * reciprocalWeight r +
          if p = r then
            (2 * Eprofile) * reciprocalWeight p +
              ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
                CKernel) * reciprocalWeight p ^ 2
          else 0 := by
  let weight := tiltedSigmaWeight B.baselineCellProbability
    B.guardedCellProbability (B.scaledBridgeScore xi)
  have hraw :=
    sigmaMixture_squarefree_reference_entry_bound_of_squarefree_profiles
      hEprofile weight (B.actualComponentValuationLaw xi)
      B.n_gt_one hpair hsingle hKernel
  have hlaw := B.sigmaMixture_actualComponentValuationLaw_eq_actualValuationLaw xi
  dsimp only at hlaw
  rw [hlaw] at hraw
  intro p r
  have hpR : (p.1 : ℝ) ≠ 0 := by
    exact_mod_cast (prime_of_mem_primeBand p.2).ne_zero
  have hrR : (r.1 : ℝ) ≠ 0 := by
    exact_mod_cast (prime_of_mem_primeBand r.2).ne_zero
  unfold reciprocalWeight
  convert hraw p r using 1
  split_ifs <;> field_simp [hpR, hrR]

/-- The subtype-indexed squarefree quadratic is exactly the covariance of
the paper's literal post-band squarefree score. -/
theorem subtypeSquarefreeQuadratic_actual_eq_covariance
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge) :
    subtypeSquarefreeQuadratic (B.actualValuationLaw xi)
        (compensatedPrimeCoefficient B.partition q) =
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q) := by
  let cNat : ℕ → ℝ := B.actualCompensatedNatCoefficient q
  have hquad := (B.actualQuadratics_eq_covariances xi q).2
  change PaperPrimePowerRelativeQuadratic.squarefreeQuadratic
      (B.actualValuationLaw xi)
      (primeBand B.sampleData.n B.sampleData.W) cNat = _ at hquad
  rw [← hquad]
  unfold subtypeSquarefreeQuadratic matrixQuadratic
    PaperPrimePowerRelativeQuadratic.squarefreeQuadratic
  have houter := Finset.sum_attach
    (primeBand B.sampleData.n B.sampleData.W)
    (fun p ↦ ∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
      cNat p * cNat r * (B.actualValuationLaw xi).covII p r)
  rw [← houter]
  apply Finset.sum_congr rfl
  intro p hp
  have hinner := Finset.sum_attach
    (primeBand B.sampleData.n B.sampleData.W)
    (fun r ↦ cNat p.1 * cNat r *
      (B.actualValuationLaw xi).covII p.1 r)
  rw [← hinner]
  apply Finset.sum_congr rfl
  intro r hr
  dsimp only [cNat]
  unfold compensatedPrimeCoefficient
  rw [B.actualCompensatedNatCoefficient_of_mem q p.2]
  rw [B.actualCompensatedNatCoefficient_of_mem q r.2]
  rw [B.partition_compensatedCoefficient_eq q p]
  rw [B.partition_compensatedCoefficient_eq q r]



/-- Matching actual squarefree upper bound from the same signed profiles.
No positivity shortcut is used: the reference form and the signed transfer
error are bounded separately. -/
theorem actualSquarefree_compensated_upper_of_profiles
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {Eprofile CF CKernel : ℝ} (hEprofile : 0 ≤ Eprofile)
    (hpair : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p r 1 1)| ≤
        Eprofile * pairWeight p r 1 1)
    (hsingle : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hF : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |DickmanBasic.F (tPrime B.sampleData.n p.1)| ≤ CF)
    (hKernel : ∀ p r : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p.1) (tPrime B.sampleData.n r.1)| ≤ CKernel) :
    (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q) ≤
      CKernel * B.partition.compensatedL1 q ^ 2 +
        CF * B.partition.compensatedL2Sq q +
        (4 * pairCovarianceScale Eprofile) *
            B.partition.compensatedL1 q ^ 2 +
        (2 * Eprofile) * B.partition.compensatedL2Sq q +
        ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
          CKernel) * weightedL2SqSecond reciprocalWeight
            (compensatedPrimeCoefficient B.partition q) := by
  let c : BandPrime B.sampleData.n B.sampleData.W → ℝ :=
    compensatedPrimeCoefficient B.partition q
  have hentry := B.actual_squarefree_reference_entry_bound_of_profiles
    xi hEprofile hpair hsingle (fun p hp ↦ hKernel ⟨p, hp⟩ ⟨p, hp⟩)
  have herror :=
    abs_subtypeSquarefreeQuadratic_sub_primeReference_le
      (B.actualValuationLaw xi) c hentry
  have herror' :
      |subtypeSquarefreeQuadratic (B.actualValuationLaw xi) c -
          primeReferenceQuadratic B.sampleData.n c| ≤
        (4 * pairCovarianceScale Eprofile) *
            B.partition.compensatedL1 q ^ 2 +
          (2 * Eprofile) * B.partition.compensatedL2Sq q +
          ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
            CKernel) * weightedL2SqSecond reciprocalWeight c := by
    simpa only [c, weightedL1_compensated_eq,
      weightedL2Sq_compensated_eq] using herror
  have htransfer := le_of_abs_le herror'
  have href := abs_primeReferenceQuadratic_le c hF hKernel
  have hrefUpper :
      primeReferenceQuadratic B.sampleData.n c ≤
        CKernel * B.partition.compensatedL1 q ^ 2 +
          CF * B.partition.compensatedL2Sq q := by
    have hleabs : primeReferenceQuadratic B.sampleData.n c ≤
        |primeReferenceQuadratic B.sampleData.n c| := le_abs_self _
    have href' :
        |primeReferenceQuadratic B.sampleData.n c| ≤
          CKernel * B.partition.compensatedL1 q ^ 2 +
            CF * B.partition.compensatedL2Sq q := by
      simpa only [c, weightedL1_compensated_eq,
        weightedL2Sq_compensated_eq] using href
    exact hleabs.trans href'
  rw [B.subtypeSquarefreeQuadratic_actual_eq_covariance xi q] at htransfer
  dsimp only [c] at htransfer hrefUpper ⊢
  linarith



end BridgeData

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualPrimePowerRowTransfer -/
section


/-!
# Actual prime-power transfer from a reference row

The canonical raw Lemma 7.5 certificate is proved for an unguarded reference
law, whereas Lemma 8.6 uses the genuinely guarded and physically tilted law.
This file records the exact finite triangle needed to pass between them.

Only the weighted `VV-II` row is used.  This is deliberate: the compensated
slow coefficient contains the within-band deviation and therefore is not a
lift of a band vector.  A sharp band-operator estimate alone does not control
that coefficient.  The row below does, without postulating a full
`PrimePowerTransferBounds` package for the actual law.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerLemma75 PaperPrimePowerRelativeQuadratic
open PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



/-- Relative compensated slow-quadratic transfer from a literal actual-law
weighted row.  No other field of Lemma 7.5 is used. -/
theorem actual_primePower_relative_variance_bound_of_row
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w R : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hw : 0 ≤ w) (hR : 0 ≤ R)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2)
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV p.1 r.1 -
            (B.actualValuationLaw xi).covII p.1 r.1| ≤ R) :
    |(B.tiltedLaw xi).covariance
        (B.postBandPrimeScore q) (B.postBandPrimeScore q) -
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q)| ≤
      ((1 + C) * (7 + C * K)) * R * w ^ 2 := by
  have hthree :=
    B.partition.compensatedCoefficient_three_bounds B.n_gt_one q
      hC hw hsharp hbandT hdevSup hdevL1 hdevL2
  have hcSup := hthree.1
  have hcL1 := hthree.2.1
  have hnatSup : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.actualCompensatedNatCoefficient q p| ≤ (1 + C) * w := by
    intro p hp
    rw [B.actualCompensatedNatCoefficient_of_mem q hp]
    rw [← B.partition_compensatedCoefficient_eq q ⟨p, hp⟩]
    exact hcSup ⟨p, hp⟩
  have hnatL1 :
      (∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
        |B.actualCompensatedNatCoefficient q p| * (1 / (p : ℝ))) ≤
        (7 + C * K) * w := by
    rw [B.compensatedNatL1_eq_partition]
    exact hcL1
  have hrowNat : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      (p : ℝ) * ∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        |(B.actualValuationLaw xi).covVV p r -
          (B.actualValuationLaw xi).covII p r| ≤ R := by
    intro p hp
    have hrowSubtype := hrow ⟨p, hp⟩
    have hattach := Finset.sum_attach
      (primeBand B.sampleData.n B.sampleData.W)
      (fun r ↦ |(B.actualValuationLaw xi).covVV p r -
        (B.actualValuationLaw xi).covII p r|)
    change (p : ℝ) *
      (∑ r ∈ (primeBand B.sampleData.n B.sampleData.W).attach,
        |(B.actualValuationLaw xi).covVV p r.1 -
          (B.actualValuationLaw xi).covII p r.1|) ≤ R at hrowSubtype
    rw [hattach] at hrowSubtype
    simpa only using hrowSubtype
  have hquad := abs_full_sub_squarefree_le_of_row
    (B.actualValuationLaw xi) (B.actualCompensatedNatCoefficient q)
    (show 0 ≤ 1 + C by linarith)
    (show 0 ≤ 7 + C * K by positivity) hw hR
    hnatSup hnatL1 hrowNat
  obtain ⟨hfull, hsf⟩ := B.actualQuadratics_eq_covariances xi q
  rw [hfull, hsf] at hquad
  simpa only [mul_assoc] using hquad



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualLemma86WeightedRow -/
section


/-!
# Lemma 8.6 from the literal actual weighted prime row

This is the slow-variance assembly in the form produced by the canonical
raw-reference comparison.  In contrast to the older interface, it does not
assume a five-field Lemma 7.5 package for the actual guarded law.  The sole
prime-power input is the weighted `VV-II` row, which is exactly what the
quadratic calculation uses.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PaperBridgeFit

open ArithmeticModel ArithmeticBandGeometry
open FiniteProbability OmittedTiltPairChamber
open PrimePowerCovariance
open PaperPrimePowerChamberError
open PaperSquarefreeSlowQuadraticLower
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



/-- Exact two-stage variance comparison from the squarefree variance, a
literal actual weighted row, and the nuisance marked rows. -/
theorem actualCompensatedScore_variance_bounds_of_squarefree_and_weightedRow
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w R lower upper Cmarked : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hw : 0 ≤ w) (hR : 0 ≤ R)
    (hCmarked : 0 ≤ Cmarked)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV p.1 r.1 -
            (B.actualValuationLaw xi).covII p.1 r.1| ≤ R)
    (hsfLower : lower * w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q))
    (hsfUpper :
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q) ≤
          upper * w ^ 2)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (p.1 : ℝ))) :
    lower * w ^ 2 -
        (((1 + C) * (7 + C * K)) * R) * w ^ 2 -
        ((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * (7 + C * K))) ^ 2 / gamma) * w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.actualCompensatedScore xi hgamma hgap q)
        (B.actualCompensatedScore xi hgamma hgap q) ∧
    (B.tiltedLaw xi).covariance
        (B.actualCompensatedScore xi hgamma hgap q)
        (B.actualCompensatedScore xi hgamma hgap q) ≤
      upper * w ^ 2 +
        (((1 + C) * (7 + C * K)) * R) * w ^ 2 := by
  let E : ℝ := ((1 + C) * (7 + C * K)) * R
  let Cz : ℝ := Real.sqrt
    (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
      (Cmarked * (7 + C * K))
  let full : ℝ := (B.tiltedLaw xi).covariance
    (B.postBandPrimeScore q) (B.postBandPrimeScore q)
  let squarefree : ℝ := (B.tiltedLaw xi).covariance
    (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q)
  let loss : ℝ := inner ℝ
    (B.nuisanceCoefficientOfScore xi hgamma hgap
      (B.postBandPrimeScore q))
    (B.nuisanceCovarianceVector xi (B.postBandPrimeScore q))
  let residualVariance : ℝ := (B.tiltedLaw xi).covariance
    (B.actualCompensatedScore xi hgamma hgap q)
    (B.actualCompensatedScore xi hgamma hgap q)
  have hpow : |full - squarefree| ≤ E * w ^ 2 := by
    exact B.actual_primePower_relative_variance_bound_of_row xi q
      hC hK hw hR hsharp hbandT hdevSup hdevL1 hdevL2 hrow
  have hL1 :=
    (B.partition.compensatedCoefficient_three_bounds B.n_gt_one q
      hC hw hsharp hbandT hdevSup hdevL1 hdevL2).2.1
  have hcovZRaw :=
    B.nuisanceCovarianceVector_postBand_norm_le_of_marked_and_l1
      xi q hCmarked hmarked hL1
  have hcovZ : ‖B.nuisanceCovarianceVector xi
      (B.postBandPrimeScore q)‖ ≤ Cz * w := by
    simpa only [Cz, mul_assoc] using hcovZRaw
  have hvar : residualVariance = full - loss := by
    exact B.nuisanceResidualScore_variance_identity
      xi hgamma hgap (B.postBandPrimeScore q)
  have hloss := B.nuisanceRegressionLoss_bounds
    xi hgamma hgap (B.postBandPrimeScore q)
  have hCz0 : 0 ≤ Cz := by
    dsimp only [Cz]
    positivity
  have hcovSq :
      ‖B.nuisanceCovarianceVector xi (B.postBandPrimeScore q)‖ ^ 2 ≤
        (Cz * w) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hCz0 hw)).2 hcovZ
  have hlossUpper : loss ≤ (Cz ^ 2 / gamma) * w ^ 2 := by
    calc
      loss ≤
          ‖B.nuisanceCovarianceVector xi (B.postBandPrimeScore q)‖ ^ 2 /
            gamma := hloss.2
      _ ≤ (Cz * w) ^ 2 / gamma :=
        div_le_div_of_nonneg_right hcovSq hgamma.le
      _ = (Cz ^ 2 / gamma) * w ^ 2 := by ring
  have hpowLower : -(E * w ^ 2) ≤ full - squarefree :=
    neg_le_of_abs_le hpow
  have hpowUpper : full - squarefree ≤ E * w ^ 2 :=
    le_of_abs_le hpow
  have hlossNonneg : 0 ≤ loss := hloss.1
  change lower * w ^ 2 ≤ squarefree at hsfLower
  change squarefree ≤ upper * w ^ 2 at hsfUpper
  change lower * w ^ 2 - E * w ^ 2 -
      (Cz ^ 2 / gamma) * w ^ 2 ≤ residualVariance ∧
    residualVariance ≤ upper * w ^ 2 + E * w ^ 2
  constructor
  · rw [hvar]
    linarith
  · rw [hvar]
    linarith

/-- Lower-bound-only version of the preceding assembly.  It avoids an
irrelevant squarefree upper estimate and is the form used by the uniform
canonical wrapper. -/
theorem actualCompensatedScore_lower_of_squarefree_and_weightedRow
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w R lower Cmarked : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hw : 0 ≤ w) (hR : 0 ≤ R)
    (hCmarked : 0 ≤ Cmarked)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV p.1 r.1 -
            (B.actualValuationLaw xi).covII p.1 r.1| ≤ R)
    (hsfLower : lower * w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q))
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (p.1 : ℝ))) :
    lower * w ^ 2 -
        (((1 + C) * (7 + C * K)) * R) * w ^ 2 -
        ((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * (7 + C * K))) ^ 2 / gamma) * w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.actualCompensatedScore xi hgamma hgap q)
        (B.actualCompensatedScore xi hgamma hgap q) := by
  let E : ℝ := ((1 + C) * (7 + C * K)) * R
  let Cz : ℝ := Real.sqrt
    (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
      (Cmarked * (7 + C * K))
  let full : ℝ := (B.tiltedLaw xi).covariance
    (B.postBandPrimeScore q) (B.postBandPrimeScore q)
  let squarefree : ℝ := (B.tiltedLaw xi).covariance
    (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q)
  let loss : ℝ := inner ℝ
    (B.nuisanceCoefficientOfScore xi hgamma hgap
      (B.postBandPrimeScore q))
    (B.nuisanceCovarianceVector xi (B.postBandPrimeScore q))
  let residualVariance : ℝ := (B.tiltedLaw xi).covariance
    (B.actualCompensatedScore xi hgamma hgap q)
    (B.actualCompensatedScore xi hgamma hgap q)
  have hpow : |full - squarefree| ≤ E * w ^ 2 :=
    B.actual_primePower_relative_variance_bound_of_row xi q
      hC hK hw hR hsharp hbandT hdevSup hdevL1 hdevL2 hrow
  have hL1 :=
    (B.partition.compensatedCoefficient_three_bounds B.n_gt_one q
      hC hw hsharp hbandT hdevSup hdevL1 hdevL2).2.1
  have hcovZRaw :=
    B.nuisanceCovarianceVector_postBand_norm_le_of_marked_and_l1
      xi q hCmarked hmarked hL1
  have hcovZ : ‖B.nuisanceCovarianceVector xi
      (B.postBandPrimeScore q)‖ ≤ Cz * w := by
    simpa only [Cz, mul_assoc] using hcovZRaw
  have hvar : residualVariance = full - loss :=
    B.nuisanceResidualScore_variance_identity
      xi hgamma hgap (B.postBandPrimeScore q)
  have hloss := B.nuisanceRegressionLoss_bounds
    xi hgamma hgap (B.postBandPrimeScore q)
  have hCz0 : 0 ≤ Cz := by
    dsimp only [Cz]
    positivity
  have hcovSq :
      ‖B.nuisanceCovarianceVector xi (B.postBandPrimeScore q)‖ ^ 2 ≤
        (Cz * w) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hCz0 hw)).2 hcovZ
  have hlossUpper : loss ≤ (Cz ^ 2 / gamma) * w ^ 2 := by
    calc
      loss ≤
          ‖B.nuisanceCovarianceVector xi (B.postBandPrimeScore q)‖ ^ 2 /
            gamma := hloss.2
      _ ≤ (Cz * w) ^ 2 / gamma :=
        div_le_div_of_nonneg_right hcovSq hgamma.le
      _ = (Cz ^ 2 / gamma) * w ^ 2 := by ring
  have hpowLower : -(E * w ^ 2) ≤ full - squarefree :=
    neg_le_of_abs_le hpow
  change lower * w ^ 2 ≤ squarefree at hsfLower
  change lower * w ^ 2 - E * w ^ 2 -
      (Cz ^ 2 / gamma) * w ^ 2 ≤ residualVariance
  rw [hvar]
  linarith





end BridgeData

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualLemma86PaperScale -/
section


/-!
# Paper-scale finite slow-variance lower

The older relative lemma normalized the partition variance by the special
factor `1/16`.  A permitted two-parameter paper mesh instead supplies a
uniform factor depending only on the previously fixed regularity constant.
This file keeps that factor literal.  No comparison between `delta` and
`eta` is encoded in the finite statement.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PaperBridgeFit

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open OmittedTiltPairChamber PrimePowerCovariance
open PaperPrimePowerChamberError PaperSquarefreeSlowQuadraticLower
open PrimeSquarefreeDirichletGeometry FiniteAnchoredDirichletQuadratic
open PaperWeightedInverseExport PaperCanonicalSlowKappa
open FiniteSignedQuadraticEntryTransfer SquarefreeCovarianceReference

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)











/-- Exact two-stage finite lower at an arbitrary paper variance factor. -/
theorem actualTwoStageCompensatedVariance_lower_paperScale_of_weightedRow
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    {C K R varianceFactor rowError Eprofile CKernel anchorFloor Cmarked : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hvarianceFactor : 0 ≤ varianceFactor)
    (hrowError : 0 ≤ rowError) (hEprofile : 0 ≤ Eprofile)
    (hCKernel : 0 ≤ CKernel) (hCmarked : 0 ≤ Cmarked)
    (hW : 0 < B.sampleData.W)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one)
      (B.actualBandRegression xi hgamma hgap e) ≤ C * B.w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ B.w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * B.w)
    (hvarLower : varianceFactor * B.w ^ 2 ≤ B.partition.variance)
    (hdevL2 : B.partition.variance ≤ 4 * B.w ^ 2)
    (hvariance : B.partition.variance ≤ B.partition.centerEnergy)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor)
    (hAnchorMass : anchorFloor ≤
      anchorMass (primeWeight B.sampleData.n) anchor)
    (hrowReference : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hpair : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p r 1 1)| ≤
        Eprofile * pairWeight p r 1 1)
    (hsingle : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hKernel : ∀ p r : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p.1)
          (tPrime B.sampleData.n r.1)| ≤ CKernel)
    (hrowPower : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV p.1 r.1 -
            (B.actualValuationLaw xi).covII p.1 r.1| ≤ R)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (p.1 : ℝ))) :
    B.paperScaleLemma86SlowConstantOfRow varianceFactor anchorFloor
        rowError Eprofile CKernel C K (1 / (B.sampleData.W : ℝ)) R
        Cmarked gamma * B.w ^ 2 ≤
      B.actualTwoStageCompensatedVariance xi hgamma hgap e := by
  let q := B.actualBandRegression xi hgamma hgap e
  let lower := paperScaleSquarefreeSlowConstant varianceFactor
    anchorFloor rowError Eprofile CKernel C K
      (1 / (B.sampleData.W : ℝ))
  have hsfLower :=
    B.actualSquarefree_relative_lower_canonicalKappa_of_varianceFactor
      xi q hC hK B.w_pos.le hvarianceFactor hrowError hEprofile
      hCKernel hW (by simpa only [q] using hsharp) hbandT hdevSup
      hdevL1 hvarLower hdevL2 hvariance anchor hinterior hmass
      hAnchorMass hrowReference hpair hsingle hKernel
  have hlower :=
    B.actualCompensatedScore_lower_of_squarefree_and_weightedRow
      xi q hC hK B.w_pos.le hR hCmarked
      (by simpa only [q] using hsharp) hbandT hdevSup hdevL1 hdevL2
      hgamma hgap hrowPower (by simpa only [q, lower] using hsfLower)
      hmarked
  change B.paperScaleLemma86SlowConstantOfRow varianceFactor anchorFloor
      rowError Eprofile CKernel C K (1 / (B.sampleData.W : ℝ)) R
      Cmarked gamma * B.w ^ 2 ≤
    (B.tiltedLaw xi).covariance
      (B.actualCompensatedScore xi hgamma hgap q)
      (B.actualCompensatedScore xi hgamma hgap q)
  dsimp only [paperScaleLemma86SlowConstantOfRow, lower] at hlower ⊢
  ring_nf at hlower ⊢
  exact hlower

/-- Two-sided literal finite Lemma 8.6 variance estimate.  This exposes the
upper estimate used by the paper instead of retaining it only as an
intermediate squarefree calculation. -/
theorem actualTwoStageCompensatedVariance_bounds_paperScale_of_weightedRow
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    {C K R varianceFactor rowError Eprofile CF CKernel anchorFloor
      Cmarked : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hvarianceFactor : 0 ≤ varianceFactor)
    (hrowError : 0 ≤ rowError) (hEprofile : 0 ≤ Eprofile)
    (hCF : 0 ≤ CF) (hCKernel : 0 ≤ CKernel)
    (hCmarked : 0 ≤ Cmarked) (hW : 0 < B.sampleData.W)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one)
      (B.actualBandRegression xi hgamma hgap e) ≤ C * B.w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ B.w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * B.w)
    (hvarLower : varianceFactor * B.w ^ 2 ≤ B.partition.variance)
    (hdevL2 : B.partition.variance ≤ 4 * B.w ^ 2)
    (hvariance : B.partition.variance ≤ B.partition.centerEnergy)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (hmass : 0 < anchorMass (primeWeight B.sampleData.n) anchor)
    (hAnchorMass : anchorFloor ≤
      anchorMass (primeWeight B.sampleData.n) anchor)
    (hrowReference : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n) (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hpair : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p r 1 1)| ≤
        Eprofile * pairWeight p r 1 1)
    (hsingle : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        Eprofile * singleWeight p 1)
    (hF : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |DickmanBasic.F (tPrime B.sampleData.n p.1)| ≤ CF)
    (hKernel : ∀ p r : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p.1)
          (tPrime B.sampleData.n r.1)| ≤ CKernel)
    (hrowPower : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV p.1 r.1 -
            (B.actualValuationLaw xi).covII p.1 r.1| ≤ R)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (p.1 : ℝ))) :
    B.paperScaleLemma86SlowConstantOfRow varianceFactor anchorFloor
          rowError Eprofile CKernel C K (1 / (B.sampleData.W : ℝ)) R
          Cmarked gamma * B.w ^ 2 ≤
        B.actualTwoStageCompensatedVariance xi hgamma hgap e ∧
      B.actualTwoStageCompensatedVariance xi hgamma hgap e ≤
        paperScaleLemma86SlowUpperConstantOfRow Eprofile CF CKernel C K
          (1 / (B.sampleData.W : ℝ)) R * B.w ^ 2 := by
  let q := B.actualBandRegression xi hgamma hgap e
  let lower := paperScaleSquarefreeSlowConstant varianceFactor
    anchorFloor rowError Eprofile CKernel C K
      (1 / (B.sampleData.W : ℝ))
  let upper := paperScaleSquarefreeSlowUpperConstant Eprofile CF CKernel
    C K (1 / (B.sampleData.W : ℝ))
  have hsfLower :=
    B.actualSquarefree_relative_lower_canonicalKappa_of_varianceFactor
      xi q hC hK B.w_pos.le hvarianceFactor hrowError hEprofile
      hCKernel hW (by simpa only [q] using hsharp) hbandT hdevSup
      hdevL1 hvarLower hdevL2 hvariance anchor hinterior hmass
      hAnchorMass hrowReference hpair hsingle hKernel
  have hthree := B.partition.compensatedCoefficient_three_bounds
    B.n_gt_one q hC B.w_pos.le (by simpa only [q] using hsharp)
      hbandT hdevSup hdevL1 hdevL2
  let CL1 := slowL1Constant C K
  let CL2 := slowL2Constant C K
  let invW := 1 / (B.sampleData.W : ℝ)
  have hL1 : B.partition.compensatedL1 q ≤ CL1 * B.w := by
    simpa only [CL1, slowL1Constant] using hthree.2.1
  have hL2 : B.partition.compensatedL2Sq q ≤ CL2 * B.w ^ 2 := by
    simpa only [CL2, slowL2Constant] using hthree.2.2
  have hCL1 : 0 ≤ CL1 := by
    dsimp only [CL1, slowL1Constant]
    positivity
  have hL1nonneg : 0 ≤ B.partition.compensatedL1 q := by
    unfold ArithmeticBandGeometry.Partition.compensatedL1
    exact Finset.sum_nonneg fun p hp ↦
      mul_nonneg (by positivity) (abs_nonneg _)
  have hL1Sq : B.partition.compensatedL1 q ^ 2 ≤
      CL1 ^ 2 * B.w ^ 2 := by
    have hsquare := (sq_le_sq₀ hL1nonneg
      (mul_nonneg hCL1 B.w_pos.le)).2 hL1
    nlinarith
  have hSecondRaw :=
    weightedL2SqSecond_le_invCutoff_mul_weightedL2Sq
      (n := B.sampleData.n) hW
      (compensatedPrimeCoefficient B.partition q)
  have hInvW : 0 ≤ invW := by dsimp only [invW]; positivity
  have hSecond : weightedL2SqSecond reciprocalWeight
      (compensatedPrimeCoefficient B.partition q) ≤
        invW * CL2 * B.w ^ 2 := by
    rw [weightedL2Sq_compensated_eq] at hSecondRaw
    calc
      _ ≤ invW * B.partition.compensatedL2Sq q := by
        simpa only [invW] using hSecondRaw
      _ ≤ invW * (CL2 * B.w ^ 2) :=
        mul_le_mul_of_nonneg_left hL2 hInvW
      _ = invW * CL2 * B.w ^ 2 := by ring
  have hsfUpperRaw := B.actualSquarefree_compensated_upper_of_profiles
    xi q hEprofile hpair hsingle hF hKernel
  have hsfUpper :
      (B.tiltedLaw xi).covariance
          (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q) ≤
        upper * B.w ^ 2 := by
    have hKernelL1 := mul_le_mul_of_nonneg_left hL1Sq hCKernel
    have hFL2 := mul_le_mul_of_nonneg_left hL2 hCF
    have heOff : 0 ≤ 4 * pairCovarianceScale Eprofile :=
      mul_nonneg (by norm_num) (pairCovarianceScale_nonneg hEprofile)
    have hOffL1 := mul_le_mul_of_nonneg_left hL1Sq heOff
    have heDiag : 0 ≤ 2 * Eprofile := mul_nonneg (by norm_num) hEprofile
    have hDiagL2 := mul_le_mul_of_nonneg_left hL2 heDiag
    have heSecond : 0 ≤ signedSecondConstant Eprofile CKernel := by
      dsimp only [signedSecondConstant]
      positivity
    have hSecondL2 := mul_le_mul_of_nonneg_left hSecond heSecond
    calc
      _ ≤ CKernel * B.partition.compensatedL1 q ^ 2 +
            CF * B.partition.compensatedL2Sq q +
            (4 * pairCovarianceScale Eprofile) *
              B.partition.compensatedL1 q ^ 2 +
            (2 * Eprofile) * B.partition.compensatedL2Sq q +
            signedSecondConstant Eprofile CKernel *
              weightedL2SqSecond reciprocalWeight
                (compensatedPrimeCoefficient B.partition q) := hsfUpperRaw
      _ ≤ upper * B.w ^ 2 := by
        dsimp only [upper, paperScaleSquarefreeSlowUpperConstant]
        dsimp only [CL1, CL2, invW] at hKernelL1 hFL2 hOffL1 hDiagL2 hSecondL2
        ring_nf at hKernelL1 hFL2 hOffL1 hDiagL2 hSecondL2 ⊢
        linarith
  have hbounds := B.actualCompensatedScore_variance_bounds_of_squarefree_and_weightedRow
    xi q hC hK B.w_pos.le hR hCmarked
      (by simpa only [q] using hsharp) hbandT hdevSup hdevL1 hdevL2
      hgamma hgap hrowPower (by simpa only [q, lower] using hsfLower)
      (by simpa only [q, upper] using hsfUpper) hmarked
  have hlowerFull :=
    B.actualTwoStageCompensatedVariance_lower_paperScale_of_weightedRow
      xi hgamma hgap e hC hK hR hvarianceFactor hrowError hEprofile
      hCKernel hCmarked hW hsharp hbandT hdevSup hdevL1 hvarLower
      hdevL2 hvariance anchor hinterior hmass hAnchorMass hrowReference
      hpair hsingle hKernel hrowPower hmarked
  refine ⟨hlowerFull, ?_⟩
  change (B.tiltedLaw xi).covariance
      (B.actualCompensatedScore xi hgamma hgap q)
      (B.actualCompensatedScore xi hgamma hgap q) ≤ _
  dsimp only [paperScaleLemma86SlowUpperConstantOfRow, upper] at hbounds ⊢
  ring_nf at hbounds ⊢
  exact hbounds.2

end BridgeData

end Erdos390.Full.PaperBridgeFit

end

end

universe u_1 u_2
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  [inst_5 : Nonempty.{u_2 + 1} Band] (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
  {gamma : Real} (hgamma : LT.lt.{0} (0 : Real) gamma)
  (hgap :
    ∀ (z : Erdos390.Full.PaperBridgeFit.BridgeData.NuisanceSpace.{u_1, u_2} B),
      LE.le.{0} (HMul.hMul.{0, 0, 0} gamma (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} z) (2 : Nat)))
        (Inner.inner.{0, u_1} Real z
          ((Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceCovarianceOperator.{u_1, u_2} B xi :
              Erdos390.Full.PaperBridgeFit.BridgeData.NuisanceSpace.{u_1, u_2} B →
                Erdos390.Full.PaperBridgeFit.BridgeData.NuisanceSpace.{u_1, u_2} B)
            z)))
  (e :
    LinearEquiv.{0, 0, u_2, u_2} (RingHom.id.{0} Real)
      ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)
      ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B))
  {C K R varianceFactor rowError Eprofile CF CKernel anchorFloor Cmarked : Real},
  LE.le.{0} (0 : Real) C →
    LE.le.{0} (0 : Real) K →
      LE.le.{0} (0 : Real) R →
        LE.le.{0} (0 : Real) varianceFactor →
          LE.le.{0} (0 : Real) rowError →
            LE.le.{0} (0 : Real) Eprofile →
              LE.le.{0} (0 : Real) CF →
                LE.le.{0} (0 : Real) CKernel →
                  LE.le.{0} (0 : Real) Cmarked →
                    LT.lt.{0} (0 : Nat)
                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) →
                      LE.le.{0}
                          (Erdos390.Full.PaperWeightedInverseExport.paperSharpNorm.{u_2}
                            (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2} B)
                            (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B)
                            (Erdos390.Full.ArithmeticBandGeometry.Partition.center_ne_zero.{u_2}
                              (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)
                              (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, u_2} B))
                            (Erdos390.Full.PaperBridgeFit.BridgeData.actualBandRegression.{u_1, u_2} B xi hgamma hgap
                              e))
                          (HMul.hMul.{0, 0, 0} C (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B)) →
                        LE.le.{0}
                            (Erdos390.Full.PrimeSums.bandTReciprocalSum
                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                            K →
                          (∀
                              (p :
                                Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                              LE.le.{0}
                                (abs.{0}
                                  (Erdos390.Full.ArithmeticBandGeometry.Partition.deviation.{u_2}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B) p))
                                (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B)) →
                            LE.le.{0}
                                (Erdos390.Full.ArithmeticBandGeometry.Partition.totalL1.{u_2}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                (HMul.hMul.{0, 0, 0} (7 : Real)
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B)) →
                              LE.le.{0}
                                  (HMul.hMul.{0, 0, 0} varianceFactor
                                    (HPow.hPow.{0, 0, 0} (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B)
                                      (2 : Nat)))
                                  (Erdos390.Full.ArithmeticBandGeometry.Partition.variance.{u_2}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)) →
                                LE.le.{0}
                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.variance.{u_2}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                    (HMul.hMul.{0, 0, 0} (4 : Real)
                                      (HPow.hPow.{0, 0, 0} (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B)
                                        (2 : Nat))) →
                                  LE.le.{0}
                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.variance.{u_2}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.centerEnergy.{u_2}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)) →
                                    ∀
                                      (anchor :
                                        Finset.{0}
                                          (Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))),
                                      (∀
                                          (p :
                                            Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                                          Membership.mem.{0, 0} anchor p →
                                            Membership.mem.{0, 0}
                                              (Set.Icc.{0} (1 / 8 : Real)
                                                (HSub.hSub.{0, 0, 0} (1 : Real) (1 / 8 : Real)))
                                              (Erdos390.Full.ArithmeticModel.tPrime
                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                                (↑p : Nat))) →
                                        LT.lt.{0} (0 : Real)
                                            (Erdos390.Full.FiniteAnchoredDirichletQuadratic.anchorMass.{0}
                                              (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeWeight
                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                              anchor) →
                                          LE.le.{0} anchorFloor
                                              (Erdos390.Full.FiniteAnchoredDirichletQuadratic.anchorMass.{0}
                                                (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeWeight
                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                                anchor) →
                                            (∀
                                                (p :
                                                  Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                        B))),
                                                LE.le.{0}
                                                  (abs.{0}
                                                    (Erdos390.Full.FiniteAnchoredDirichletQuadratic.rowResidual.{0}
                                                      (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeWeight
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                            B)))
                                                      (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeDiagonal
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                            B)))
                                                      (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeKernel
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                            B)))
                                                      p))
                                                  (HMul.hMul.{0, 0, 0} rowError
                                                    (Erdos390.Full.ArithmeticModel.tPrime
                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                          B))
                                                      (↑p : Nat)))) →
                                              (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) (p : Nat),
                                                  Membership.mem.{0, 0}
                                                      (Erdos390.Full.ArithmeticModel.primeBand
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                            B))
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                            B)))
                                                      p →
                                                    ∀ (r : Nat),
                                                      Membership.mem.{0, 0}
                                                          (Finset.erase.{0}
                                                            (Erdos390.Full.ArithmeticModel.primeBand
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                    u_2}
                                                                  B))
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                    u_2}
                                                                  B)))
                                                            p)
                                                          r →
                                                        LE.le.{0}
                                                          (abs.{0}
                                                            (HSub.hSub.{0, 0, 0}
                                                              (Erdos390.Full.FiniteProbability.expect.{0}
                                                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{0}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1,
                                                                      u_2}
                                                                    B xi c))
                                                                fun
                                                                  (omega :
                                                                    Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1}
                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                          u_2}
                                                                        B)
                                                                      c) =>
                                                                Erdos390.Full.ArithmeticModel.divInd
                                                                  (Erdos390.Full.OmittedTiltPairChamber.pairPower p r
                                                                    (1 : Nat) (1 : Nat))
                                                                  (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{0}
                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1,
                                                                        u_2}
                                                                      B xi c)
                                                                    omega))
                                                              (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                      u_2}
                                                                    B))
                                                                (Erdos390.Full.OmittedTiltPairChamber.pairPower p r
                                                                  (1 : Nat) (1 : Nat)))))
                                                          (HMul.hMul.{0, 0, 0} Eprofile
                                                            (Erdos390.Full.PaperPrimePowerChamberError.pairWeight p r
                                                              (1 : Nat) (1 : Nat)))) →
                                                (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) (p : Nat),
                                                    Membership.mem.{0, 0}
                                                        (Erdos390.Full.ArithmeticModel.primeBand
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                u_2}
                                                              B))
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                u_2}
                                                              B)))
                                                        p →
                                                      LE.le.{0}
                                                        (abs.{0}
                                                          (HSub.hSub.{0, 0, 0}
                                                            (Erdos390.Full.FiniteProbability.expect.{0}
                                                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{0}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1,
                                                                    u_2}
                                                                  B xi c))
                                                              fun
                                                                (omega :
                                                                  Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1}
                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                        u_2}
                                                                      B)
                                                                    c) =>
                                                              Erdos390.Full.ArithmeticModel.divInd p
                                                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{0}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1,
                                                                      u_2}
                                                                    B xi c)
                                                                  omega))
                                                            (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                    u_2}
                                                                  B))
                                                              p)))
                                                        (HMul.hMul.{0, 0, 0} Eprofile
                                                          (Erdos390.Full.PaperPrimePowerChamberError.singleWeight p
                                                            (1 : Nat)))) →
                                                  (∀
                                                      (p :
                                                        Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                u_2}
                                                              B))
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                u_2}
                                                              B))),
                                                      LE.le.{0}
                                                        (abs.{0}
                                                          (Erdos390.Full.DickmanBasic.F
                                                            (Erdos390.Full.ArithmeticModel.tPrime
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                    u_2}
                                                                  B))
                                                              (↑p : Nat))))
                                                        CF) →
                                                    (∀
                                                        (p r :
                                                          Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                  u_2}
                                                                B))
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                  u_2}
                                                                B))),
                                                        LE.le.{0}
                                                          (abs.{0}
                                                            (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel
                                                              (Erdos390.Full.ArithmeticModel.tPrime
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                      u_2}
                                                                    B))
                                                                (↑p : Nat))
                                                              (Erdos390.Full.ArithmeticModel.tPrime
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                      u_2}
                                                                    B))
                                                                (↑r : Nat))))
                                                          CKernel) →
                                                      (∀
                                                          (p :
                                                            Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                    u_2}
                                                                  B))
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                    u_2}
                                                                  B))),
                                                          LE.le.{0}
                                                            (HMul.hMul.{0, 0, 0} (↑(↑p : Nat) : Real)
                                                              (∑ r :
                                                                Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                        u_2}
                                                                      B))
                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                        u_2}
                                                                      B)),
                                                                abs.{0}
                                                                  (HSub.hSub.{0, 0, 0}
                                                                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_1}
                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1,
                                                                          u_2}
                                                                        B xi)
                                                                      (↑p : Nat) (↑r : Nat))
                                                                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1}
                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1,
                                                                          u_2}
                                                                        B xi)
                                                                      (↑p : Nat) (↑r : Nat)))))
                                                            R) →
                                                        (∀
                                                            (c :
                                                              Erdos390.Full.PaperBridgeFit.NuisanceCoord.{u_1}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1,
                                                                    u_2}
                                                                  B))
                                                            (p :
                                                              Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                      u_2}
                                                                    B))
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                      u_2}
                                                                    B))),
                                                            LE.le.{0}
                                                              (abs.{0}
                                                                (Erdos390.Full.FiniteProbability.covariance.{u_1}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.tiltedLaw.{u_1,
                                                                      u_2}
                                                                    B xi)
                                                                  (fun
                                                                      (m :
                                                                        Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                              u_2}
                                                                            B)) =>
                                                                    WithLp.ofLp.{u_1}
                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceStatistic.{u_1,
                                                                          u_2}
                                                                        B m)
                                                                      c)
                                                                  fun
                                                                    (m :
                                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                            u_2}
                                                                          B)) =>
                                                                  Erdos390.Full.ArithmeticModel.valuation (↑p : Nat)
                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{u_1}
                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                          u_2}
                                                                        B)
                                                                      m)))
                                                              (HMul.hMul.{0, 0, 0} Cmarked
                                                                (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                  (↑(↑p : Nat) : Real)))) →
                                                          And
                                                            (LE.le.{0}
                                                              (HMul.hMul.{0, 0, 0}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.paperScaleLemma86SlowConstantOfRow.{u_1,
                                                                    u_2}
                                                                  B varianceFactor anchorFloor rowError Eprofile CKernel
                                                                  C K
                                                                  (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                    (↑(Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                              u_2}
                                                                            B)) :
                                                                      Real))
                                                                  R Cmarked gamma)
                                                                (HPow.hPow.{0, 0, 0}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2}
                                                                    B)
                                                                  (2 : Nat)))
                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.actualTwoStageCompensatedVariance.{u_1,
                                                                  u_2}
                                                                B xi hgamma hgap e))
                                                            (LE.le.{0}
                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.actualTwoStageCompensatedVariance.{u_1,
                                                                  u_2}
                                                                B xi hgamma hgap e)
                                                              (HMul.hMul.{0, 0, 0}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.paperScaleLemma86SlowUpperConstantOfRow
                                                                  Eprofile CF CKernel C K
                                                                  (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                    (↑(Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                              u_2}
                                                                            B)) :
                                                                      Real))
                                                                  R)
                                                                (HPow.hPow.{0, 0, 0}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2}
                                                                    B)
                                                                  (2 : Nat)))) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.actualTwoStageCompensatedVariance_bounds_paperScale_of_weightedRow
