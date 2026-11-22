-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.actualBandSchur_fastGauge_eq_projectedTarget
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:14:57.205773+00:00
-- url     : https://prove2.me/submissions/05a758ea-02d0-466d-83fa-dbfdc7d3feb9

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

theorem covarianceOperator_symmetric [Nonempty Head]
    (xi x y : B.ParamSpace) :
    inner ℝ x (B.covarianceOperator xi y) =
      inner ℝ y (B.covarianceOperator xi x) := by
  rw [B.inner_covarianceOperator, B.inner_covarianceOperator]
  unfold FiniteExponentialFamily.covariance FiniteProbability.covariance
  congr 1
  · apply Finset.sum_congr rfl
    intro m hm
    ring
  · ring



















theorem nuisanceCovarianceEquiv_apply [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (z : B.NuisanceSpace) :
    B.nuisanceCovarianceEquiv xi hgamma hgap z =
      B.nuisanceCovarianceOperator xi z := by
  simp [nuisanceCovarianceEquiv]













theorem exactNuisanceRegression_solve [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) :
    B.nuisanceCovarianceOperator xi
        (B.exactNuisanceRegression xi hgamma hgap u) =
      B.crossCovarianceOperator xi u := by
  rw [← B.nuisanceCovarianceEquiv_apply xi hgamma hgap]
  exact (B.nuisanceCovarianceEquiv xi hgamma hgap).apply_symm_apply _

theorem exactNuisanceRegression_isRegression [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) :
    B.IsNuisanceRegression xi
      (B.exactNuisanceRegression xi hgamma hgap) := by
  intro u z
  let R := B.exactNuisanceRegression xi hgamma hgap
  have hres : B.schurResidual R u =
      B.mainEmbed u - B.nuisanceEmbed (R u) :=
    B.schurResidual_eq_sub R u
  have hcross : inner ℝ (B.nuisanceEmbed z)
      (B.covarianceOperator xi (B.mainEmbed u)) =
      inner ℝ z (B.crossCovarianceOperator xi u) := by
    simpa only [crossCovarianceOperator, ContinuousLinearMap.comp_apply] using
      (ContinuousLinearMap.adjoint_inner_right B.nuisanceEmbeddingCLM z
        (B.covarianceOperator xi (B.mainEmbeddingCLM u))).symm
  have hblock : inner ℝ (B.nuisanceEmbed z)
      (B.covarianceOperator xi (B.nuisanceEmbed (R u))) =
      inner ℝ z (B.nuisanceCovarianceOperator xi (R u)) := by
    simpa only [nuisanceCovarianceOperator,
      ContinuousLinearMap.comp_apply] using
      (ContinuousLinearMap.adjoint_inner_right B.nuisanceEmbeddingCLM z
        (B.covarianceOperator xi
          (B.nuisanceEmbeddingCLM (R u)))).symm
  have hsecond : inner ℝ (B.nuisanceEmbed z)
      (B.covarianceOperator xi (B.schurResidual R u)) = 0 := by
    rw [hres, map_sub, inner_sub_right, hcross, hblock]
    rw [B.exactNuisanceRegression_solve xi hgamma hgap]
    exact sub_self _
  refine ⟨?_, hsecond⟩
  rw [B.covarianceOperator_symmetric xi]
  exact hsecond



















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

















/-- Reindexing over the actual partition identifies the raw band score with
the corresponding primewise coefficient sum. -/
theorem bandRegressionScore_eq_primeSum
    (q : B.RawBandGauge) (m : B.sampleData.Sample) :
    B.bandRegressionScore q m =
      ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.bandRegressionCoefficient q p *
          valuation p.1 (B.sampleData.value m) := by
  unfold bandRegressionScore bandScore bandRegressionCoefficient
  rw [← Finset.sum_fiberwise Finset.univ B.partition.band
    (fun p : BandPrime B.sampleData.n B.sampleData.W ↦
      q.1 (B.partition.band p) *
        valuation p.1 (B.sampleData.value m))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpj : B.partition.band p = j :=
    (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff
      B.partition.data).mp hp
  rw [hpj]

/-- The first-stage residual is exactly `S_g - sum_j q_j Omega_j`. -/
theorem postBandPrimeScore_eq_slow_sub_bandRegression
    (q : B.RawBandGauge) (m : B.sampleData.Sample) :
    B.postBandPrimeScore q m =
      B.slowScore m - B.bandRegressionScore q m := by
  rw [B.bandRegressionScore_eq_primeSum q m]
  unfold postBandPrimeScore actualCompensatedCoefficient
    slowScore primeDeviation bandRegressionCoefficient
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring







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





theorem actualCompensatedScore_covariance_nuisance_zero [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge) (z : B.NuisanceSpace) :
    (B.tiltedLaw xi).covariance
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m))
        (B.actualCompensatedScore xi hgamma hgap q) = 0 := by
  exact B.nuisanceResidualScore_covariance_zero xi hgamma hgap
    (B.postBandPrimeScore q) z

















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualTwoStageRegression -/
section


/-!
# The literal two-stage band/nuisance solve of Lemma 8.6

This file defines the actual Schur-projected band operator on the exact raw
arithmetic gauge.  The first regression vector is obtained by inverting this
literal operator on the literal Schur-projected raw slow-score column.  The
second regression is then the actual nuisance inverse already constructed in
`PaperActualCompensatedRegression`.

No covariance matrix, inverse, or regression conclusion is stored in bridge
data.  The equivalence argument of the first-stage constructor is intended to
be supplied by the actual projected inverse conclusion of Lemma 8.4.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport
open CompressedArithmeticOperator
open MovingLowGaugeTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)









theorem projectRawBandVector_sub [Nonempty Band]
    (x y : Band → ℝ) :
    B.projectRawBandVector (x - y) =
      B.projectRawBandVector x - B.projectRawBandVector y := by
  apply Subtype.ext
  funext j
  change weightedGaugeProjection B.harmonicMass B.bandCenter (x - y) j =
    weightedGaugeProjection B.harmonicMass B.bandCenter x j -
      weightedGaugeProjection B.harmonicMass B.bandCenter y j
  have hsum :
      (∑ k : Band,
        B.harmonicMass k * B.bandCenter k * (x k - y k)) =
      (∑ k : Band, B.harmonicMass k * B.bandCenter k * x k) -
        ∑ k : Band, B.harmonicMass k * B.bandCenter k * y k := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  unfold weightedGaugeProjection
  simp only [Pi.sub_apply, hsum]
  ring

/-- The kernel of the exact arithmetic projection is orthogonal to every
raw-gauge vector in the `D` pairing. -/
theorem weighted_sum_eq_zero_of_projectRawBandVector_eq_zero
    [Nonempty Band]
    (x : Band → ℝ) (q : B.RawBandGauge)
    (hx : B.projectRawBandVector x = 0) :
    (∑ j : Band, B.harmonicMass j * q.1 j * x j) = 0 := by
  let mu : ℝ :=
    (∑ k : Band, B.harmonicMass k * B.bandCenter k * x k) /
      sharpWeightTotal B.harmonicMass B.bandCenter
  have hxcoord (j : Band) : x j = B.bandCenter j * mu := by
    have hzero := congrArg (fun v : B.RawBandGauge ↦ v.1 j) hx
    change weightedGaugeProjection B.harmonicMass B.bandCenter x j = 0 at hzero
    unfold weightedGaugeProjection at hzero
    dsimp only [mu]
    linarith
  calc
    (∑ j : Band, B.harmonicMass j * q.1 j * x j) =
        mu * ∑ j : Band,
          rawGaugeWeight B.harmonicMass B.bandCenter j * q.1 j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hxcoord j]
      unfold rawGaugeWeight
      ring
    _ = 0 := by
      have hq := q.2
      change (∑ j : Band,
        rawGaugeWeight B.harmonicMass B.bandCenter j * q.1 j) = 0 at hq
      rw [hq, mul_zero]







theorem normalizedBandCovarianceRow_sub [Nonempty Head]
    (xi : B.ParamSpace) (F G : B.sampleData.Sample → ℝ) :
    B.normalizedBandCovarianceRow xi (fun m ↦ F m - G m) =
      B.normalizedBandCovarianceRow xi F -
        B.normalizedBandCovarianceRow xi G := by
  have hsub : (fun m ↦ F m - G m) =
      fun m ↦ F m + (-1 : ℝ) * G m := by
    funext m
    ring
  rw [hsub, B.normalizedBandCovarianceRow_add,
    B.normalizedBandCovarianceRow_smul]
  funext j
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  ring













theorem nuisanceResidualScore_sub [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F G : B.sampleData.Sample → ℝ) :
    B.nuisanceResidualScore xi hgamma hgap (fun m ↦ F m - G m) =
      fun m ↦ B.nuisanceResidualScore xi hgamma hgap F m -
        B.nuisanceResidualScore xi hgamma hgap G m := by
  have hsub : (fun m ↦ F m - G m) =
      fun m ↦ F m + (-1 : ℝ) * G m := by
    funext m
    ring
  rw [hsub, B.nuisanceResidualScore_add xi hgamma hgap,
    B.nuisanceResidualScore_smul xi hgamma hgap]
  funext m
  ring





theorem bandRegressionScore_sub
    (q r : B.RawBandGauge) :
    B.bandRegressionScore (q - r) =
      fun m ↦ B.bandRegressionScore q m - B.bandRegressionScore r m := by
  have hneg : -r = (-1 : ℝ) • r := (neg_one_smul ℝ r).symm
  rw [sub_eq_add_neg, B.bandRegressionScore_add, hneg,
    B.bandRegressionScore_smul]
  funext m
  ring













theorem actualBandRegression_normalEquation [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q) :
    B.actualBandSchurLinearMap xi hgamma hgap
        (B.actualBandRegression xi hgamma hgap e) =
      B.actualBandRegressionTarget xi hgamma hgap := by
  rw [← he]
  exact e.apply_symm_apply _

/-- The constructed first-stage regression makes the literal normalized
band row of the fully nuisance-projected score vanish after arithmetic gauge
projection. -/
theorem actualBandRegression_projectedResidual_zero
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q) :
    B.projectRawBandVector
      (B.normalizedBandCovarianceRow xi
        (B.actualCompensatedScore xi hgamma hgap
          (B.actualBandRegression xi hgamma hgap e))) = 0 := by
  let q := B.actualBandRegression xi hgamma hgap e
  have hnormal := B.actualBandRegression_normalEquation
    xi hgamma hgap e he
  have hpost : B.postBandPrimeScore q =
      fun m ↦ B.slowScore m - B.bandRegressionScore q m := by
    funext m
    exact B.postBandPrimeScore_eq_slow_sub_bandRegression q m
  have hresidual :
      B.actualCompensatedScore xi hgamma hgap q =
        fun m ↦
          B.nuisanceResidualScore xi hgamma hgap B.slowScore m -
          B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore q) m := by
    unfold actualCompensatedScore
    rw [hpost, B.nuisanceResidualScore_sub xi hgamma hgap]
  rw [hresidual, B.normalizedBandCovarianceRow_sub,
    B.projectRawBandVector_sub]
  change B.actualBandRegressionTarget xi hgamma hgap -
      B.actualBandSchurLinearMap xi hgamma hgap q = 0
  rw [← hnormal]
  exact sub_self _

/-- Exact covariance of a raw gauge score with an arbitrary finite score,
written in the normalized band-row coordinates. -/
theorem covariance_bandRegressionScore_eq_weightedRow [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    (F : B.sampleData.Sample → ℝ) :
    (B.tiltedLaw xi).covariance (B.bandRegressionScore q) F =
      ∑ j : Band, B.harmonicMass j * q.1 j *
        B.normalizedBandCovarianceRow xi F j := by
  unfold bandRegressionScore normalizedBandCovarianceRow
  rw [FiniteProbability.covariance_sum_left]
  apply Finset.sum_congr rfl
  intro j hj
  rw [FiniteProbability.covariance_smul_left]
  have hH := B.harmonicMass_pos j
  field_simp [ne_of_gt hH]

/-- The first-stage normal equation is genuine covariance orthogonality to
every arithmetic gauge score. -/
theorem actualBandRegression_covariance_gauge_zero
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (r : B.RawBandGauge) :
    (B.tiltedLaw xi).covariance (B.bandRegressionScore r)
      (B.actualCompensatedScore xi hgamma hgap
        (B.actualBandRegression xi hgamma hgap e)) = 0 := by
  rw [B.covariance_bandRegressionScore_eq_weightedRow]
  exact B.weighted_sum_eq_zero_of_projectRawBandVector_eq_zero
    (B.normalizedBandCovarianceRow xi
      (B.actualCompensatedScore xi hgamma hgap
        (B.actualBandRegression xi hgamma hgap e))) r
    (B.actualBandRegression_projectedResidual_zero
      xi hgamma hgap e he)

















/-- The fully fitted literal score is orthogonal both to every nuisance
score and to every raw arithmetic-gauge band score. -/
theorem actualTwoStageCompensatedScore_orthogonal
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q) :
    (∀ z : B.NuisanceSpace,
      (B.tiltedLaw xi).covariance
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m))
        (B.actualTwoStageCompensatedScore xi hgamma hgap e) = 0) ∧
    ∀ r : B.RawBandGauge,
      (B.tiltedLaw xi).covariance (B.bandRegressionScore r)
        (B.actualTwoStageCompensatedScore xi hgamma hgap e) = 0 := by
  constructor
  · intro z
    exact B.actualCompensatedScore_covariance_nuisance_zero
      xi hgamma hgap (B.actualBandRegression xi hgamma hgap e) z
  · intro r
    exact B.actualBandRegression_covariance_gauge_zero
      xi hgamma hgap e he r

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperMainRawGaugeCoordinates -/
section


/-!
# Exact identification of the main coordinates with the paper raw gauge

The ODE parameter space stores one coordinate for each concrete gauge-basis
vector and stores `w * lambda` in the slow coordinate.  Lemma 8.6 instead
writes the band coefficient as a vector in the arithmetic hyperplane
`sum_j H_j alpha_j q_j = 0`.  This file identifies these two descriptions
exactly, including the moving low coordinate.  No estimate is used.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

























/-- Exact effective prime coefficient of a Schur residual. -/
theorem schurResidual_effectivePrimeCoefficient
    (R : B.MainSpace → B.NuisanceSpace) (u : B.MainSpace)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    B.effectivePrimeCoefficient (B.schurResidual R u) p =
      (B.rawGaugeOfMain u).1 (B.partition.band p) +
        (u MainCoord.slow / B.w) * B.primeDeviation p := by
  rw [B.schurResidual_eq_sub]
  have hadd := B.effectivePrimeCoefficient_add
    (B.mainEmbed u) (-B.nuisanceEmbed (R u)) p
  have hneg := B.effectivePrimeCoefficient_smul (-1)
    (B.nuisanceEmbed (R u)) p
  rw [sub_eq_add_neg, hadd]
  change B.effectivePrimeCoefficient (B.mainEmbed u) p +
      B.effectivePrimeCoefficient (-B.nuisanceEmbed (R u)) p = _
  rw [show -B.nuisanceEmbed (R u) =
      (-1 : ℝ) • B.nuisanceEmbed (R u) by simp,
    hneg, B.nuisanceEmbed_effectivePrimeCoefficient]
  simp





/-- Exact score represented by a main parameter in intrinsic raw-gauge and
stored-slow coordinates.  The factor `1 / w` is visible because the actual
`MainSpace` stores `w * lambda`. -/
theorem vectorScore_mainEmbed_eq_rawGauge_add_slow [Nonempty Head]
    (u : B.MainSpace) (m : B.sampleData.Sample) :
    B.vectorFamily.scalarFamily.score m (B.mainEmbed u) =
      B.bandRegressionScore (B.rawGaugeOfMain u) m +
        (u MainCoord.slow / B.w) * B.slowScore m := by
  rw [B.vectorScore_eq_effectivePrime_add_nuisance]
  have hnuisance : B.nuisanceParameter (B.mainEmbed u) = 0 := by
    apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).injective
    funext c
    cases c <;> rfl
  rw [hnuisance, inner_zero_left, add_zero]
  simp_rw [B.mainEmbed_effectivePrimeCoefficient, add_mul]
  rw [Finset.sum_add_distrib]
  have hband := B.bandRegressionScore_eq_primeSum
    (B.rawGaugeOfMain u) m
  unfold bandRegressionCoefficient at hband
  rw [← hband]
  unfold slowScore
  rw [Finset.mul_sum]
  apply congrArg₂ (fun x y : ℝ ↦ x + y) rfl
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Exact score of a Schur residual.  This is the literal finite score on
which the band and marked covariance rows act. -/
theorem vectorScore_schurResidual_eq_rawGauge_slow_nuisance
    [Nonempty Head]
    (R : B.MainSpace → B.NuisanceSpace) (u : B.MainSpace)
    (m : B.sampleData.Sample) :
    B.vectorFamily.scalarFamily.score m (B.schurResidual R u) =
      B.bandRegressionScore (B.rawGaugeOfMain u) m +
        (u MainCoord.slow / B.w) * B.slowScore m -
          inner ℝ (R u) (B.nuisanceStatistic m) := by
  rw [B.vectorScore_eq_effectivePrime_add_nuisance,
    B.nuisanceParameter_schurResidual]
  simp_rw [B.schurResidual_effectivePrimeCoefficient, add_mul]
  rw [Finset.sum_add_distrib]
  have hband := B.bandRegressionScore_eq_primeSum
    (B.rawGaugeOfMain u) m
  unfold bandRegressionCoefficient at hband
  rw [← hband]
  unfold slowScore
  rw [inner_neg_left]
  have hslow :
      (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        u MainCoord.slow / B.w * B.primeDeviation p *
          ArithmeticModel.valuation p.1 (B.sampleData.value m)) =
        (u MainCoord.slow / B.w) *
          ∑ p : BandPrime B.sampleData.n B.sampleData.W,
            B.primeDeviation p *
              ArithmeticModel.valuation p.1 (B.sampleData.value m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [hslow]
  ring

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperExactSchurRawSlow -/
section


/-!
# Exact raw-gauge/slow form of the finite Schur regression

This file identifies the nuisance regression occurring in the actual Schur
operator with the regression of the literal raw-gauge/slow score.  It is an
exact finite-dimensional identity, and is the first attachment needed to
turn the two-stage estimates of Lemma 8.6 into bounds for the Proposition
8.7 vector field.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The exponential-family score of a pure nuisance parameter is exactly
the Euclidean pairing with the literal physical/head statistic. -/
theorem vectorScore_nuisanceEmbed_eq_nuisanceStatistic [Nonempty Head]
    (z : B.NuisanceSpace) (m : B.sampleData.Sample) :
    B.vectorFamily.scalarFamily.score m (B.nuisanceEmbed z) =
      inner ℝ z (B.nuisanceStatistic m) := by
  rw [B.vectorScore_eq_effectivePrime_add_nuisance]
  have hnuisance : B.nuisanceParameter (B.nuisanceEmbed z) = z := by
    apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).injective
    funext c
    cases c <;> rfl
  simp_rw [B.nuisanceEmbed_effectivePrimeCoefficient]
  rw [hnuisance]
  simp

/-- The main-to-nuisance covariance block is the covariance vector of the
literal main score. -/
theorem crossCovarianceOperator_eq_nuisanceCovarianceVector_mainScore
    [Nonempty Head]
    (xi : B.ParamSpace) (u : B.MainSpace) :
    B.crossCovarianceOperator xi u =
      B.nuisanceCovarianceVector xi
        (fun m ↦ B.vectorFamily.scalarFamily.score m (B.mainEmbed u)) := by
  apply ext_inner_left ℝ
  intro z
  have hcross :
      inner ℝ z (B.crossCovarianceOperator xi u) =
        inner ℝ (B.nuisanceEmbed z)
          (B.covarianceOperator xi (B.mainEmbed u)) := by
    simpa only [crossCovarianceOperator,
      ContinuousLinearMap.comp_apply] using
      (ContinuousLinearMap.adjoint_inner_right
        B.nuisanceEmbeddingCLM z
        (B.covarianceOperator xi (B.mainEmbeddingCLM u)))
  rw [hcross, B.inner_covarianceOperator,
    B.inner_nuisanceCovarianceVector]
  congr 1
  funext m
  calc
    inner ℝ (B.nuisanceEmbed z) (B.statistic m) =
        inner ℝ (B.statistic m) (B.nuisanceEmbed z) :=
      real_inner_comm _ _
    _ = inner ℝ z (B.nuisanceStatistic m) := by
      simpa only [VectorExponentialFamily.scalarFamily,
        innerSL_apply_apply] using
          B.vectorScore_nuisanceEmbed_eq_nuisanceStatistic z m
  funext m
  simpa only [VectorExponentialFamily.scalarFamily,
    innerSL_apply_apply] using
      (real_inner_comm (B.mainEmbed u) (B.statistic m)).symm

/-- The nuisance component of the exact Schur residual is the actual finite
regression coefficient of the literal main score. -/
theorem exactNuisanceRegression_eq_nuisanceCoefficient_mainScore
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) :
    B.exactNuisanceRegression xi hgamma hgap u =
      B.nuisanceCoefficientOfScore xi hgamma hgap
        (fun m ↦ B.vectorFamily.scalarFamily.score m (B.mainEmbed u)) := by
  apply B.nuisanceCovarianceOperator_injective xi hgamma hgap
  rw [B.exactNuisanceRegression_solve,
    B.nuisanceCoefficientOfScore_solve]
  exact B.crossCovarianceOperator_eq_nuisanceCovarianceVector_mainScore xi u

/-- Consequently the score of the exact Schur residual is literally the
nuisance residual of the raw main score. -/
theorem vectorScore_exactSchurResidual_eq_nuisanceResidual_mainScore
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) :
    (fun m ↦ B.vectorFamily.scalarFamily.score m
      (B.schurResidual (B.exactNuisanceRegression xi hgamma hgap) u)) =
      B.nuisanceResidualScore xi hgamma hgap
        (fun m ↦ B.vectorFamily.scalarFamily.score m (B.mainEmbed u)) := by
  funext m
  rw [B.vectorScore_schurResidual_eq_rawGauge_slow_nuisance]
  unfold nuisanceResidualScore
  rw [← B.exactNuisanceRegression_eq_nuisanceCoefficient_mainScore]
  change _ =
    B.vectorFamily.scalarFamily.score m (B.mainEmbed u) -
      inner ℝ (B.exactNuisanceRegression xi hgamma hgap u)
        (B.nuisanceStatistic m)
  rw [B.vectorScore_mainEmbed_eq_rawGauge_add_slow]

/-- Exact fast/slow score decomposition used by the full block inverse.  If
the raw gauge coordinate has the algebraic form

`q_fast - lambda * q_reg`

and the stored slow coordinate is `w * lambda`, then the Schur-residual
score is the nuisance-projected fast score plus `lambda` times the literal
two-stage compensated score.  This is the finite identity behind the marked
row integration in Proposition 8.7. -/
theorem vectorScore_exactSchurResidual_fast_add_compensated
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) (qFast qReg : B.RawBandGauge) (lambda : ℝ)
    (hq : B.rawGaugeOfMain u = qFast - lambda • qReg)
    (hslow : u MainCoord.slow = B.w * lambda) :
    (fun m ↦ B.vectorFamily.scalarFamily.score m
      (B.schurResidual (B.exactNuisanceRegression xi hgamma hgap) u)) =
      fun m ↦
        B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore qFast) m +
          lambda * B.actualCompensatedScore xi hgamma hgap qReg m := by
  rw [B.vectorScore_exactSchurResidual_eq_nuisanceResidual_mainScore]
  have hinput :
      (fun m ↦ B.vectorFamily.scalarFamily.score m (B.mainEmbed u)) =
        fun m ↦ B.bandRegressionScore qFast m +
          lambda * B.postBandPrimeScore qReg m := by
    funext m
    rw [B.vectorScore_mainEmbed_eq_rawGauge_add_slow, hq,
      B.bandRegressionScore_sub,
      B.bandRegressionScore_smul, hslow,
      mul_div_cancel_left₀ lambda (ne_of_gt B.w_pos),
      B.postBandPrimeScore_eq_slow_sub_bandRegression]
    ring
  rw [hinput, B.nuisanceResidualScore_add,
    B.nuisanceResidualScore_smul]
  rfl

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperExactSchurTwoStageQuadratic -/
section


/-!
# Exact quadratic attachment for the two-stage Schur regression

This file supplies the finite-dimensional algebra between the arithmetic
band inverse of Lemma 8.4 and the compensated slow score of Lemma 8.6.  In
particular, no limiting operator, mesh estimate, or covariance lower bound
is assumed here.

The first identity identifies the quadratic form of the literal projected
band Schur operator with the variance of the nuisance-residual band score.
The second identity proves that the fast band residual and the fitted slow
score are exactly covariance-orthogonal.  Combining them gives the exact
fast/slow quadratic decomposition of the main Schur block used in
Proposition 8.7.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport MovingLowGaugeTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



/-- Projecting a normalized band row does not change its pairing with an
arithmetic-gauge vector.  This is the exact finite arithmetic centering
identity; in particular it does not replace the arithmetic centres by
continuum cell centres. -/
theorem weighted_pairing_projectRawBandVector
    [Nonempty Band]
    (q : B.RawBandGauge) (x : Band → ℝ) :
    (∑ j : Band, B.harmonicMass j * q.1 j *
        (B.projectRawBandVector x).1 j) =
      ∑ j : Band, B.harmonicMass j * q.1 j * x j := by
  let mu : ℝ :=
    (∑ k : Band, B.harmonicMass k * B.bandCenter k * x k) /
      sharpWeightTotal B.harmonicMass B.bandCenter
  have hcoord (j : Band) :
      (B.projectRawBandVector x).1 j = x j - B.bandCenter j * mu := by
    change weightedGaugeProjection B.harmonicMass B.bandCenter x j = _
    unfold weightedGaugeProjection
    rfl
  rw [show (∑ j : Band, B.harmonicMass j * q.1 j *
      (B.projectRawBandVector x).1 j) =
      (∑ j : Band, B.harmonicMass j * q.1 j * x j) -
        mu * (∑ j : Band,
          rawGaugeWeight B.harmonicMass B.bandCenter j * q.1 j) by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hcoord]
    unfold rawGaugeWeight
    ring]
  have hq := q.2
  change (∑ j : Band,
    rawGaugeWeight B.harmonicMass B.bandCenter j * q.1 j) = 0 at hq
  rw [hq, mul_zero, sub_zero]



/-- Bilinear form of the preceding identity.  It is needed for the
covariance Cauchy--Schwarz conversion from a sharp inverse bound to a
positive `D`-quadratic gap. -/
theorem actualBandSchur_bilinear_eq_residualCovariance
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q r : B.RawBandGauge) :
    B.bandDPairing q (B.actualBandSchurLinearMap xi hgamma hgap r) =
      (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q))
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore r)) := by
  let Fq : B.sampleData.Sample → ℝ := B.bandRegressionScore q
  let Fr : B.sampleData.Sample → ℝ := B.bandRegressionScore r
  let aq : B.NuisanceSpace :=
    B.nuisanceCoefficientOfScore xi hgamma hgap Fq
  let Zq : B.sampleData.Sample → ℝ :=
    fun m ↦ inner ℝ aq (B.nuisanceStatistic m)
  let Rq : B.sampleData.Sample → ℝ :=
    B.nuisanceResidualScore xi hgamma hgap Fq
  let Rr : B.sampleData.Sample → ℝ :=
    B.nuisanceResidualScore xi hgamma hgap Fr
  have hFq : Fq = fun m ↦ Rq m + Zq m := by
    funext m
    simp only [Fq, Rq, Zq, aq]
    unfold nuisanceResidualScore
    ring
  have horth : (B.tiltedLaw xi).covariance Zq Rr = 0 := by
    simpa only [Zq, Rr, aq] using
      B.nuisanceResidualScore_covariance_zero
        xi hgamma hgap Fr aq
  calc
    B.bandDPairing q (B.actualBandSchurLinearMap xi hgamma hgap r) =
        ∑ j : Band, B.harmonicMass j * q.1 j *
          B.normalizedBandCovarianceRow xi Rr j := by
      unfold bandDPairing
      exact B.weighted_pairing_projectRawBandVector q
        (B.normalizedBandCovarianceRow xi Rr)
    _ = (B.tiltedLaw xi).covariance Fq Rr := by
      exact (B.covariance_bandRegressionScore_eq_weightedRow
        xi q Rr).symm
    _ = (B.tiltedLaw xi).covariance Rq Rr := by
      rw [hFq, FiniteProbability.covariance_add_left, horth, add_zero]







/-- The nuisance-residual fast band score is exactly orthogonal to the
two-stage compensated slow score.  Both the band normal equation and the
nuisance normal equation are used; neither orthogonality is postulated. -/
theorem fastResidual_covariance_twoStageCompensated_eq_zero
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (qFast : B.RawBandGauge) :
    (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore qFast))
        (B.actualTwoStageCompensatedScore xi hgamma hgap e) = 0 := by
  let a : B.NuisanceSpace := B.nuisanceCoefficientOfScore xi hgamma hgap
    (B.bandRegressionScore qFast)
  have hband : (B.tiltedLaw xi).covariance
      (B.bandRegressionScore qFast)
      (B.actualTwoStageCompensatedScore xi hgamma hgap e) = 0 :=
    (B.actualTwoStageCompensatedScore_orthogonal
      xi hgamma hgap e he).2 qFast
  have hnuisance : (B.tiltedLaw xi).covariance
      (fun m ↦ inner ℝ a (B.nuisanceStatistic m))
      (B.actualTwoStageCompensatedScore xi hgamma hgap e) = 0 :=
    (B.actualTwoStageCompensatedScore_orthogonal
      xi hgamma hgap e he).1 a
  have hresidual :
      B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore qFast) =
        fun m ↦ B.bandRegressionScore qFast m -
          inner ℝ a (B.nuisanceStatistic m) := by
    rfl
  rw [hresidual]
  have hsub : (fun m ↦ B.bandRegressionScore qFast m -
      inner ℝ a (B.nuisanceStatistic m)) =
      fun m ↦ B.bandRegressionScore qFast m +
        (-1 : ℝ) * inner ℝ a (B.nuisanceStatistic m) := by
    funext m
    ring
  rw [hsub, FiniteProbability.covariance_add_left,
    FiniteProbability.covariance_smul_left, hband, hnuisance]
  ring







end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperExactTwoStageTargetSolve -/
section


/-!
# Exact two-stage solution of the finite Schur target equation

This file performs the algebraic block solve which is used, but usually
left implicit, in Proposition 8.7.  The right side is the literal normalized
paper target.  Its fast band component and compensated slow component are
defined below from the actual finite arithmetic data.  No asymptotic
estimate, continuum operator, or covariance lower bound is asserted here.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport
  MovingLowGaugeTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

private theorem sum_mainCoord_target {Gauge : Type*} [Fintype Gauge]
    (f : MainCoord Gauge → ℝ) :
    (∑ c : MainCoord Gauge, f c) =
      (∑ j : Gauge, f (.gauge j)) + f .slow := by
  let e : MainCoord Gauge ≃ Gauge ⊕ Unit :=
    { toFun := fun c => match c with
        | .gauge j => Sum.inl j
        | .slow => Sum.inr ()
      invFun := fun s => match s with
        | Sum.inl j => .gauge j
        | Sum.inr _ => .slow
      left_inv := by intro c; cases c <;> rfl
      right_inv := by intro s; cases s <;> rfl }
  calc
    (∑ c : MainCoord Gauge, f c) =
        ∑ s : Gauge ⊕ Unit, f (e.symm s) := by
      exact Fintype.sum_equiv e f (fun s => f (e.symm s))
        (fun c => by simp)
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp [e]





/-- The `D` pairing is positive definite on the actual raw arithmetic
gauge.  This is a finite statement using only positivity of the actual
harmonic masses. -/
theorem eq_zero_of_bandDPairing_self_eq_zero
    (q : B.RawBandGauge) (hzero : B.bandDPairing q q = 0) : q = 0 := by
  apply Subtype.ext
  funext j
  have hterm :
      B.harmonicMass j * q.1 j * q.1 j ≤
        ∑ k : Band, B.harmonicMass k * q.1 k * q.1 k := by
    have h := Finset.single_le_sum
      (s := (Finset.univ : Finset Band))
      (f := fun k => B.harmonicMass k * q.1 k * q.1 k)
      (fun k hk => by
        change 0 ≤ B.harmonicMass k * q.1 k * q.1 k
        calc
          0 ≤ B.harmonicMass k * (q.1 k * q.1 k) :=
            mul_nonneg (B.harmonicMass_pos k).le
              (mul_self_nonneg (q.1 k))
          _ = B.harmonicMass k * q.1 k * q.1 k := by ring)
      (Finset.mem_univ j)
    simpa using h
  unfold bandDPairing at hzero
  rw [hzero] at hterm
  have hmass := B.harmonicMass_pos j
  have hprod : B.harmonicMass j * (q.1 j) ^ 2 = 0 := by
    apply le_antisymm
    · simpa [pow_two, mul_assoc] using hterm
    · positivity
  have hsq : (q.1 j) ^ 2 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hmass)
  exact sq_eq_zero_iff.mp hsq

/-- The projected target row represents exactly the gauge part of the
normalized paper target under the finite arithmetic `D` pairing. -/
theorem bandDPairing_projectedNormalizedTargetBand
    [Nonempty Head] [Nonempty Band]
    (Delta : Band → ℝ) (r : B.RawBandGauge) :
    B.bandDPairing r (B.projectedNormalizedTargetBand Delta) =
      inner ℝ (B.mainRawSlowLinearEquiv.symm (r, 0))
        (B.mainPart (B.normalizedTarget Delta)) := by
  rw [PiLp.inner_apply]
  change B.bandDPairing r (B.projectedNormalizedTargetBand Delta) =
    ∑ c : MainCoord B.GaugeIndex,
      B.mainPart (B.normalizedTarget Delta) c *
        B.mainRawSlowLinearEquiv.symm (r, 0) c
  rw [sum_mainCoord_target]
  simp only [B.mainRawSlowLinearEquiv_symm_gauge,
    B.mainRawSlowLinearEquiv_symm_slow, mul_zero, add_zero,
    B.mainPart_gauge]
  rw [show B.bandDPairing r (B.projectedNormalizedTargetBand Delta) =
      ∑ j : Band, B.harmonicMass j * r.1 j *
        B.normalizedTargetBandRow Delta j by
    unfold projectedNormalizedTargetBand bandDPairing
    exact B.weighted_pairing_projectRawBandVector r
      (B.normalizedTargetBandRow Delta)]
  unfold normalizedTargetBandRow
  have hmass (j : Band) : B.harmonicMass j ≠ 0 :=
    ne_of_gt (B.harmonicMass_pos j)
  have hcancel (j : Band) :
      B.harmonicMass j * r.1 j *
          ((B.L / B.q) * Delta j / B.harmonicMass j) =
        r.1 j * ((B.L / B.q) * Delta j) := by
    field_simp [hmass j]
  simp_rw [hcancel]
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun j : Band => r.1 j * ((B.L / B.q) * Delta j)) B.lowBand]
  rw [B.rawBandGauge_low_eq]
  simp only [B.normalizedTarget_apply, unscaledTarget, coordScale,
    div_one]
  have hrhs :
      (∑ x : B.GaugeIndex,
        (B.L / B.q) *
            (Delta x.1 - B.lowRatio x * Delta B.lowBand) * r.1 x.1) =
        (∑ x : B.GaugeIndex,
          r.1 x.1 * ((B.L / B.q) * Delta x.1)) -
          (∑ x : B.GaugeIndex, B.lowRatio x * r.1 x.1) *
            ((B.L / B.q) * Delta B.lowBand) := by
    calc
      (∑ x : B.GaugeIndex,
        (B.L / B.q) *
            (Delta x.1 - B.lowRatio x * Delta B.lowBand) * r.1 x.1) =
          ∑ x : B.GaugeIndex,
            (r.1 x.1 * ((B.L / B.q) * Delta x.1) -
              (B.lowRatio x * r.1 x.1) *
                ((B.L / B.q) * Delta B.lowBand)) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_mul]
  rw [hrhs]
  ring



/-- Bilinear form of the literal exact Schur operator.  Both arguments are
the genuine finite nuisance-regression residuals. -/
theorem inner_exactSchurCovarianceOperator_bilinear
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (v u : B.MainSpace) :
    inner ℝ v (B.exactSchurCovarianceOperator xi hgamma hgap u) =
      inner ℝ
        (B.schurResidual (B.exactNuisanceRegression xi hgamma hgap) v)
        (B.covarianceOperator xi
          (B.schurResidual
            (B.exactNuisanceRegression xi hgamma hgap) u)) := by
  let R := B.exactNuisanceRegression xi hgamma hgap
  let rv := B.schurResidual R v
  let ru := B.schurResidual R u
  have hleft :
      inner ℝ v (B.exactSchurCovarianceOperator xi hgamma hgap u) =
        inner ℝ (B.mainEmbed v) (B.covarianceOperator xi ru) := by
    simpa only [exactSchurCovarianceOperator,
      ContinuousLinearMap.comp_apply,
      B.exactSchurEmbeddingCLM_apply, R, ru] using
      (ContinuousLinearMap.adjoint_inner_right B.mainEmbeddingCLM v
        (B.covarianceOperator xi ru))
  have hv : B.mainEmbed v = rv + B.nuisanceEmbed (R v) := by
    rw [show rv = B.mainEmbed v - B.nuisanceEmbed (R v) from
      B.schurResidual_eq_sub R v]
    abel
  have horth :=
    (B.exactNuisanceRegression_isRegression xi hgamma hgap u (R v)).2
  have horth' : inner ℝ (B.nuisanceEmbed (R v))
      (B.covarianceOperator xi ru) = 0 := by
    simpa only [R, ru] using horth
  calc
    inner ℝ v (B.exactSchurCovarianceOperator xi hgamma hgap u) =
        inner ℝ (B.mainEmbed v) (B.covarianceOperator xi ru) := hleft
    _ = inner ℝ rv (B.covarianceOperator xi ru) := by
      rw [hv, inner_add_left]
      rw [horth', add_zero]







/-- The exact Schur residual of a raw-only main vector has precisely the
nuisance-residual band score. -/
theorem vectorScore_exactSchurResidual_rawOnly
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge) :
    (fun m => B.vectorFamily.scalarFamily.score m
      (B.schurResidual (B.exactNuisanceRegression xi hgamma hgap)
        (B.rawOnlyMain q))) =
      B.nuisanceResidualScore xi hgamma hgap
        (B.bandRegressionScore q) := by
  rw [B.vectorScore_exactSchurResidual_eq_nuisanceResidual_mainScore]
  congr 1
  funext m
  rw [B.vectorScore_mainEmbed_eq_rawGauge_add_slow]
  simp



theorem rawGauge_eq_fastGauge_sub_regression
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (u : B.MainSpace) :
    B.rawGaugeOfMain u =
      B.fastGaugeOfMain xi hgamma hgap e u -
        (u MainCoord.slow / B.w) •
          B.actualBandRegression xi hgamma hgap e := by
  unfold fastGaugeOfMain
  abel

theorem slow_eq_w_mul_slow_div (u : B.MainSpace) :
    u MainCoord.slow = B.w * (u MainCoord.slow / B.w) := by
  field_simp [ne_of_gt B.w_pos]

/-- Every solution of the literal main Schur equation has fast band
coordinate equal to the inverse solution of the literal projected target
row.  This is an exact finite identity, not an inverse estimate. -/
theorem actualBandSchur_fastGauge_eq_projectedTarget
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (Delta : Band → ℝ) (u : B.MainSpace)
    (hu : B.exactSchurCovarianceOperator xi hgamma hgap u =
      B.mainPart (B.normalizedTarget Delta)) :
    B.actualBandSchurLinearMap xi hgamma hgap
        (B.fastGaugeOfMain xi hgamma hgap e u) =
      B.projectedNormalizedTargetBand Delta := by
  let qReg := B.actualBandRegression xi hgamma hgap e
  let lambda := u MainCoord.slow / B.w
  let qFast := B.fastGaugeOfMain xi hgamma hgap e u
  have hq : B.rawGaugeOfMain u = qFast - lambda • qReg := by
    simpa only [qFast, lambda, qReg] using
      B.rawGauge_eq_fastGauge_sub_regression xi hgamma hgap e u
  have hs : u MainCoord.slow = B.w * lambda := by
    simpa only [lambda] using B.slow_eq_w_mul_slow_div u
  have hscoreU := B.vectorScore_exactSchurResidual_fast_add_compensated
    xi hgamma hgap u qFast qReg lambda hq hs
  have hpair : ∀ r : B.RawBandGauge,
      B.bandDPairing r
          (B.actualBandSchurLinearMap xi hgamma hgap qFast) =
        B.bandDPairing r (B.projectedNormalizedTargetBand Delta) := by
    intro r
    let vr := B.rawOnlyMain r
    have hscoreR := B.vectorScore_exactSchurResidual_rawOnly
      xi hgamma hgap r
    have horth := B.fastResidual_covariance_twoStageCompensated_eq_zero
      xi hgamma hgap e he r
    have horth' :
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore r))
          (B.actualCompensatedScore xi hgamma hgap qReg) = 0 := by
      simpa only [actualTwoStageCompensatedScore, qReg] using horth
    calc
      B.bandDPairing r
          (B.actualBandSchurLinearMap xi hgamma hgap qFast) =
          (B.tiltedLaw xi).covariance
            (B.nuisanceResidualScore xi hgamma hgap
              (B.bandRegressionScore r))
            (B.nuisanceResidualScore xi hgamma hgap
              (B.bandRegressionScore qFast)) :=
        B.actualBandSchur_bilinear_eq_residualCovariance
          xi hgamma hgap r qFast
      _ = (B.tiltedLaw xi).covariance
          (fun m => B.vectorFamily.scalarFamily.score m
            (B.schurResidual
              (B.exactNuisanceRegression xi hgamma hgap) vr))
          (fun m => B.vectorFamily.scalarFamily.score m
            (B.schurResidual
              (B.exactNuisanceRegression xi hgamma hgap) u)) := by
        rw [hscoreR, hscoreU,
          FiniteProbability.covariance_add_right,
          FiniteProbability.covariance_smul_right, horth']
        ring
      _ = inner ℝ vr
          (B.exactSchurCovarianceOperator xi hgamma hgap u) := by
        rw [B.inner_exactSchurCovarianceOperator_bilinear]
        rw [B.inner_covarianceOperator]
        congr 1 <;> funext m <;>
          simp only [VectorExponentialFamily.scalarFamily,
            innerSL_apply_apply] <;> exact real_inner_comm _ _
      _ = inner ℝ vr (B.mainPart (B.normalizedTarget Delta)) := by
        rw [hu]
      _ = B.bandDPairing r
          (B.projectedNormalizedTargetBand Delta) :=
        (B.bandDPairing_projectedNormalizedTargetBand Delta r).symm
  let d : B.RawBandGauge :=
    B.actualBandSchurLinearMap xi hgamma hgap qFast -
      B.projectedNormalizedTargetBand Delta
  have hdPair : B.bandDPairing d d = 0 := by
    have hd := hpair d
    unfold d bandDPairing at hd ⊢
    simp only [Submodule.coe_sub, Pi.sub_apply]
    calc
      (∑ j : Band,
        B.harmonicMass j *
          ((B.actualBandSchurLinearMap xi hgamma hgap qFast).1 j -
            (B.projectedNormalizedTargetBand Delta).1 j) *
          ((B.actualBandSchurLinearMap xi hgamma hgap qFast).1 j -
            (B.projectedNormalizedTargetBand Delta).1 j)) =
          (∑ j : Band,
            B.harmonicMass j *
              ((B.actualBandSchurLinearMap xi hgamma hgap qFast).1 j -
                (B.projectedNormalizedTargetBand Delta).1 j) *
              (B.actualBandSchurLinearMap xi hgamma hgap qFast).1 j) -
          (∑ j : Band,
            B.harmonicMass j *
              ((B.actualBandSchurLinearMap xi hgamma hgap qFast).1 j -
                (B.projectedNormalizedTargetBand Delta).1 j) *
              (B.projectedNormalizedTargetBand Delta).1 j) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := sub_eq_zero.mpr hd
  have hdZero := B.eq_zero_of_bandDPairing_self_eq_zero d hdPair
  simpa only [d, qFast] using sub_eq_zero.mp hdZero

















































end BridgeData

end

end Erdos390.Full.PaperBridgeFit

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
          ((Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceCovarianceOperator.{u_1, u_2} B xi) z)))
  (e :
    LinearEquiv.{0, 0, u_2, u_2} (RingHom.id.{0} Real)
      ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)
      ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)),
  (∀ (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)),
      Eq.{u_2 + 1} (e q)
        ((Erdos390.Full.PaperBridgeFit.BridgeData.actualBandSchurLinearMap.{u_1, u_2} B xi hgamma hgap) q)) →
    ∀ (Delta : Band → Real) (u : Erdos390.Full.PaperBridgeFit.BridgeData.MainSpace.{u_1, u_2} B),
      Eq.{u_2 + 1}
          ((Erdos390.Full.PaperBridgeFit.BridgeData.exactSchurCovarianceOperator.{u_1, u_2} B xi hgamma hgap) u)
          (Erdos390.Full.PaperBridgeFit.BridgeData.mainPart.{u_1, u_2} B
            (Erdos390.Full.PaperBridgeFit.BridgeData.normalizedTarget.{u_1, u_2} B Delta)) →
        Eq.{u_2 + 1}
          ((Erdos390.Full.PaperBridgeFit.BridgeData.actualBandSchurLinearMap.{u_1, u_2} B xi hgamma hgap)
            (Erdos390.Full.PaperBridgeFit.BridgeData.fastGaugeOfMain.{u_1, u_2} B xi hgamma hgap e u))
          (Erdos390.Full.PaperBridgeFit.BridgeData.projectedNormalizedTargetBand.{u_1, u_2} B Delta) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.actualBandSchur_fastGauge_eq_projectedTarget
