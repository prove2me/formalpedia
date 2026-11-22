-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.eventually_exists_uniform_actualBandSchurEquiv_and_quadratic_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:04:25.469205+00:00
-- url     : https://prove2.me/submissions/7a2eb59e-63da-4e84-b1f4-732082ab2ec0

import Definitions.Def_erdos390_analytic_compact_goals
import Definitions.Def_erdos390_analytic_statement_auxiliaries
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











theorem covariance_self_nonneg (mu : FiniteProbability Omega) (F : Omega → ℝ) :
    0 ≤ mu.covariance F F := by
  unfold covariance expect
  rw [show (∑ omega, mu.mass omega * (F omega * F omega)) =
      ∑ omega, mu.mass omega * F omega ^ 2 by
    apply Finset.sum_congr rfl
    intro omega _
    ring]
  rw [show (∑ omega, mu.mass omega * F omega) *
      (∑ omega, mu.mass omega * F omega) =
        (∑ omega, mu.mass omega * F omega) ^ 2 by ring]
  rw [PatternMixture.weightedVariance_pairDifference mu.mass F mu.mass_sum]
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    mul_nonneg
      (mul_nonneg (mu.mass_nonneg i) (mu.mass_nonneg j)) (sq_nonneg _)

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

/- Source module: Erdos390.Full.PrimeSums -/
section


/-!
# Prime sums on the actual moving band

This file derives the finite prime-sum estimates needed in Lemma 7.5 from
Mathlib's Chebyshev bound.  No prime-sum estimate is introduced as a contract.
-/

open scoped BigOperators Nat.Prime
open Filter Topology

namespace Erdos390.Full.PrimeSums

open ArithmeticModel Scale



















private theorem primeBand_subset_primesUpTo (n W : ℕ) :
    primeBand n W ⊆ primesUpTo (yNat n) := by
  intro p hp
  have h := mem_primeBand.mp hp
  simp [primesUpTo, h.1, h.2.2]





















/-- A global Chebyshev bound for the logarithmically weighted reciprocal
prime sum.  The deliberately simple constant is uniform in the endpoint. -/
theorem fullLogReciprocalSum_le (Y : ℕ) (hY : 2 ≤ Y) :
    fullLogReciprocalSum Y ≤ Real.log 4 * (1 + Real.log (Y : ℝ)) := by
  rw [fullLogReciprocalSum_eq Y hY]
  have hYR : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hY0 : (0 : ℝ) < (Y : ℝ) := by linarith
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have htheta : Chebyshev.theta (Y : ℝ) / (Y : ℝ) ≤ Real.log 4 := by
    calc
      Chebyshev.theta (Y : ℝ) / (Y : ℝ) ≤
          (Real.log 4 * (Y : ℝ)) / (Y : ℝ) := by
        gcongr
        exact Chebyshev.theta_le_log4_mul_x (by positivity)
      _ = Real.log 4 := by field_simp
  have hint :
      (∫ t in (2 : ℝ)..Y, Chebyshev.theta t / t ^ 2) ≤
        Real.log 4 * Real.log (Y : ℝ) := by
    calc
      (∫ t in (2 : ℝ)..Y, Chebyshev.theta t / t ^ 2) ≤
          ∫ t in (2 : ℝ)..Y, Real.log 4 * (1 / t) := by
        refine intervalIntegral.integral_mono_on hYR
          (intervalIntegrable_theta_div_sq hYR) ?_ ?_
        · apply ContinuousOn.intervalIntegrable
          intro t ht
          rw [Set.uIcc_of_le hYR] at ht
          have ht0 : t ≠ 0 := by linarith [ht.1]
          exact ContinuousAt.continuousWithinAt
            (continuousAt_const.mul (continuousAt_const.div continuousAt_id ht0))
        · intro t ht
          calc
            Chebyshev.theta t / t ^ 2 ≤ (Real.log 4 * t) / t ^ 2 := by
              gcongr
              exact Chebyshev.theta_le_log4_mul_x (by linarith [ht.1])
            _ = Real.log 4 * (1 / t) := by
              have ht0 : t ≠ 0 := by linarith [ht.1]
              field_simp
      _ = Real.log 4 * Real.log ((Y : ℝ) / 2) := by
        rw [intervalIntegral.integral_const_mul,
          integral_one_div_of_pos (by norm_num) hY0]
      _ ≤ Real.log 4 * Real.log (Y : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hlog4
        apply Real.log_le_log (div_pos hY0 (by norm_num))
        linarith
  nlinarith

theorem bandLogReciprocalSum_le_full (n W : ℕ) :
    bandLogReciprocalSum n W ≤ fullLogReciprocalSum (yNat n) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (primeBand_subset_primesUpTo n W)
  intro p hp hnot
  have hp' : p ≤ yNat n ∧ p.Prime := by
    simpa [primesUpTo] using hp
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp'.2.one_le)) (by positivity)





private theorem bandTReciprocalSum_eq (n W : ℕ) :
    bandTReciprocalSum n W =
      bandLogReciprocalSum n W / Real.log (y n) := by
  rw [bandTReciprocalSum, bandLogReciprocalSum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [tPrime]
  ring

/-- The `t_p/p` mass of the moving prime band is uniformly bounded.  This is
the first-moment estimate used in the weighted covariance-row contraction. -/
theorem eventually_bandTReciprocalSum_le (W : ℕ) :
    ∀ᶠ n in atTop, bandTReciprocalSum n W ≤ 2 * Real.log 4 := by
  have hyTop : Tendsto (fun n : ℕ => y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0,
    hyTop.eventually (eventually_ge_atTop (2 : ℝ)),
    hLTop.eventually (eventually_ge_atTop (9 / 2 : ℝ))] with n hn hyn hLn
  have hyNat : 2 ≤ yNat n := by
    exact Nat.le_floor hyn
  have hlogy : 1 ≤ Real.log (y n) := by
    rw [log_y hn]
    nlinarith
  have hlogy0 : 0 < Real.log (y n) := lt_of_lt_of_le (by norm_num) hlogy
  have hyNatPos : (0 : ℝ) < (yNat n : ℝ) := by positivity
  have hyFloor : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le (le_of_lt (y_pos hn))
  have hlogFloor : Real.log (yNat n : ℝ) ≤ Real.log (y n) :=
    Real.log_le_log hyNatPos hyFloor
  have hnum :
      Real.log 4 * (1 + Real.log (yNat n : ℝ)) ≤
        Real.log 4 * (2 * Real.log (y n)) := by
    apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by norm_num))
    nlinarith
  calc
    bandTReciprocalSum n W =
        bandLogReciprocalSum n W / Real.log (y n) := bandTReciprocalSum_eq n W
    _ ≤ fullLogReciprocalSum (yNat n) / Real.log (y n) := by
      exact div_le_div_of_nonneg_right (bandLogReciprocalSum_le_full n W)
        (le_of_lt hlogy0)
    _ ≤ (Real.log 4 * (1 + Real.log (yNat n : ℝ))) /
          Real.log (y n) := by
      exact div_le_div_of_nonneg_right (fullLogReciprocalSum_le (yNat n) hyNat)
        (le_of_lt hlogy0)
    _ ≤ (Real.log 4 * (2 * Real.log (y n))) / Real.log (y n) := by
      exact div_le_div_of_nonneg_right hnum (le_of_lt hlogy0)
    _ = 2 * Real.log 4 := by field_simp

end Erdos390.Full.PrimeSums

end

/- Source module: Erdos390.Full.StableInverse -/
section


/-!
# Stable inversion under an operator perturbation

This is the quantitative finite-dimensional perturbation lemma needed after
the continuum inverse has been transferred to the arithmetic gauge space.
It does not assume invertibility of the perturbed operator.  Instead it
derives it from a proved inverse for the reference operator and an operator
error smaller than the reciprocal inverse bound.
-/

namespace Erdos390.Full

noncomputable section

namespace StableInverse

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]







theorem perturbedEquiv_apply
    (A Ainv E : X →L[ℝ] X) (C delta : ℝ)
    (hC : 0 ≤ C)
    (hsmall : C * delta < 1)
    (hleft : ∀ x, Ainv (A x) = x)
    (hinv : ∀ y, ‖Ainv y‖ ≤ C * ‖y‖)
    (herror : ∀ x, ‖E x‖ ≤ delta * ‖x‖) (x : X) :
    perturbedEquiv A Ainv E C delta hC hsmall
      hleft hinv herror x = (A + E) x := by
  simp [perturbedEquiv]

theorem perturbed_inverse_bound_mul
    (A Ainv E : X →L[ℝ] X) (C delta : ℝ)
    (hC : 0 ≤ C)
    (hsmall : C * delta < 1)
    (hleft : ∀ x, Ainv (A x) = x)
    (hinv : ∀ y, ‖Ainv y‖ ≤ C * ‖y‖)
    (herror : ∀ x, ‖E x‖ ≤ delta * ‖x‖) (y : X) :
    (1 - C * delta) *
        ‖(perturbedEquiv A Ainv E C delta hC hsmall
          hleft hinv herror).symm y‖ ≤ C * ‖y‖ := by
  let e := perturbedEquiv A Ainv E C delta hC hsmall
    hleft hinv herror
  have hcontrol := reference_control A Ainv E C delta hC
    hleft hinv herror (e.symm y)
  have happ : (A + E) (e.symm y) = y := by
    rw [← perturbedEquiv_apply A Ainv E C delta hC hsmall
      hleft hinv herror]
    exact e.apply_symm_apply y
  simpa [e, happ] using hcontrol

theorem perturbed_inverse_bound
    (A Ainv E : X →L[ℝ] X) (C delta : ℝ)
    (hC : 0 ≤ C)
    (hsmall : C * delta < 1)
    (hleft : ∀ x, Ainv (A x) = x)
    (hinv : ∀ y, ‖Ainv y‖ ≤ C * ‖y‖)
    (herror : ∀ x, ‖E x‖ ≤ delta * ‖x‖) (y : X) :
    ‖(perturbedEquiv A Ainv E C delta hC hsmall
        hleft hinv herror).symm y‖ ≤
      (C / (1 - C * delta)) * ‖y‖ := by
  have hcoef : 0 < 1 - C * delta := sub_pos.mpr hsmall
  rw [show (C / (1 - C * delta)) * ‖y‖ =
      (C * ‖y‖) / (1 - C * delta) by ring]
  apply (le_div_iff₀ hcoef).2
  simpa [mul_comm] using
    perturbed_inverse_bound_mul A Ainv E C delta hC
      hsmall hleft hinv herror y

end StableInverse

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











omit [DecidableEq Band] in
/-- The sharp conjugate is just subtraction of the `omega`-weighted mean.
This is the finite arithmetic identity
`S^{-1} P_{alpha,H} S = I - 1 omega^T/(1^T omega)`. -/
theorem unscale_weightedGaugeProjection_scale_eq
    (H alpha x : Band → ℝ)
    (hAlpha : ∀ j, alpha j ≠ 0)
    (hTotal : sharpWeightTotal H alpha ≠ 0) :
    unscaleByCenter alpha
        (weightedGaugeProjection H alpha (scaleByCenter alpha x)) =
      fun j => x j -
        (∑ k, sharpWeight H alpha k * x k) /
          sharpWeightTotal H alpha := by
  funext j
  have hsum :
      (∑ k, H k * alpha k * (alpha k * x k)) =
        ∑ k, sharpWeight H alpha k * x k := by
    apply Finset.sum_congr rfl
    intro k hk
    unfold sharpWeight
    ring
  unfold unscaleByCenter weightedGaugeProjection scaleByCenter
  rw [hsum]
  field_simp [hAlpha j, hTotal]





omit [Fintype Band] [DecidableEq Band] in
theorem sharpWeight_nonneg_of_mass_nonneg
    (H alpha : Band → ℝ) (hH : ∀ j, 0 ≤ H j) (j : Band) :
    0 ≤ sharpWeight H alpha j := by
  exact mul_nonneg (hH j) (sq_nonneg (alpha j))















end SharpProjection

end Erdos390.Full.MovingLowGaugeTransfer

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





theorem weightedGaugeProjection_scale_eq
    (H alpha x : Band → ℝ)
    (hAlpha : ∀ j, alpha j ≠ 0)
    (hTotal : sharpWeightTotal H alpha ≠ 0)
    (i : Band) :
    weightedGaugeProjection H alpha (scaleByCenter alpha x) i =
      alpha i * meanProjection (sharpWeight H alpha) x i := by
  have hconj := congrFun
    (unscale_weightedGaugeProjection_scale_eq H alpha x hAlpha hTotal) i
  unfold unscaleByCenter at hconj
  unfold meanProjection weightedMean weightTotal
  calc
    weightedGaugeProjection H alpha (scaleByCenter alpha x) i =
        alpha i *
          (weightedGaugeProjection H alpha (scaleByCenter alpha x) i /
            alpha i) := by field_simp [hAlpha i]
    _ = alpha i *
        (x i - (∑ k, sharpWeight H alpha k * x k) /
          sharpWeightTotal H alpha) := by rw [hconj]



















end Erdos390.Full.PaperWeightedInverseExport

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









/-- Exact marked-row identity for an arbitrary nuisance coefficient.  The
vector on the right is the literal covariance vector of the marked score,
so a Euclidean row estimate can be used without introducing a
coordinate-counting loss. -/
theorem covariance_marked_nuisanceScore_eq_inner [Nonempty Head]
    (xi : B.ParamSpace) (F : B.sampleData.Sample → ℝ)
    (z : B.NuisanceSpace) :
    (B.tiltedLaw xi).covariance F
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m)) =
      inner ℝ z (B.nuisanceCovarianceVector xi F) := by
  rw [(B.tiltedLaw xi).covariance_comm]
  exact (B.inner_nuisanceCovarianceVector xi F z).symm

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











end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.FiniteProbabilityCovarianceCauchySchwarz -/
section


/-!
# Cauchy--Schwarz for a literal finite covariance

The two-stage Schur argument needs Cauchy--Schwarz for the actual finite
tilted law, not an abstract positive-semidefinite assumption.  This file
derives it directly from the mass function of `FiniteProbability`.
-/

open scoped BigOperators

namespace Erdos390.Full.FiniteProbability

noncomputable section

variable {Omega : Type*} [Fintype Omega]

/-- Covariance is the weighted inner product of the two centered functions. -/
theorem covariance_eq_sum_mass_mul_centered
    (mu : FiniteProbability Omega) (F G : Omega → ℝ) :
    mu.covariance F G =
      ∑ omega, mu.mass omega * (F omega - mu.expect F) *
        (G omega - mu.expect G) := by
  unfold covariance
  generalize hEF : mu.expect F = EF
  generalize hEG : mu.expect G = EG
  unfold expect at hEF hEG ⊢
  symm
  calc
    (∑ omega, mu.mass omega * (F omega - EF) * (G omega - EG)) =
        (∑ omega, mu.mass omega * (F omega * G omega)) -
          (∑ omega, mu.mass omega * F omega) * EG -
          EF * (∑ omega, mu.mass omega * G omega) +
          (EF * EG) * (∑ omega, mu.mass omega) := by
      rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro omega homega
      ring
    _ = (∑ omega, mu.mass omega * (F omega * G omega)) - EF * EG := by
      rw [mu.mass_sum, ← hEF, ← hEG]
      ring

/-- Squared Cauchy--Schwarz inequality for the exact finite covariance. -/
theorem covariance_sq_le_mul_self
    (mu : FiniteProbability Omega) (F G : Omega → ℝ) :
    mu.covariance F G ^ 2 ≤
      mu.covariance F F * mu.covariance G G := by
  let f : Omega → ℝ := fun omega ↦
    Real.sqrt (mu.mass omega) * (F omega - mu.expect F)
  let g : Omega → ℝ := fun omega ↦
    Real.sqrt (mu.mass omega) * (G omega - mu.expect G)
  have hcross : (∑ omega, f omega * g omega) = mu.covariance F G := by
    rw [mu.covariance_eq_sum_mass_mul_centered]
    apply Finset.sum_congr rfl
    intro omega homega
    dsimp only [f, g]
    have hsqrt : Real.sqrt (mu.mass omega) ^ 2 = mu.mass omega :=
      Real.sq_sqrt (mu.mass_nonneg omega)
    calc
      Real.sqrt (mu.mass omega) * (F omega - mu.expect F) *
          (Real.sqrt (mu.mass omega) * (G omega - mu.expect G)) =
          Real.sqrt (mu.mass omega) ^ 2 *
            (F omega - mu.expect F) * (G omega - mu.expect G) := by ring
      _ = mu.mass omega * (F omega - mu.expect F) *
            (G omega - mu.expect G) := by rw [hsqrt]
  have hleft : (∑ omega, f omega ^ 2) = mu.covariance F F := by
    rw [mu.covariance_eq_sum_mass_mul_centered]
    apply Finset.sum_congr rfl
    intro omega homega
    dsimp only [f]
    have hsqrt : Real.sqrt (mu.mass omega) ^ 2 = mu.mass omega :=
      Real.sq_sqrt (mu.mass_nonneg omega)
    rw [mul_pow, hsqrt]
    ring
  have hright : (∑ omega, g omega ^ 2) = mu.covariance G G := by
    rw [mu.covariance_eq_sum_mass_mul_centered]
    apply Finset.sum_congr rfl
    intro omega homega
    dsimp only [g]
    have hsqrt : Real.sqrt (mu.mass omega) ^ 2 = mu.mass omega :=
      Real.sq_sqrt (mu.mass_nonneg omega)
    rw [mul_pow, hsqrt]
    ring
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  simpa only [hcross, hleft, hright] using hCS

end

end Erdos390.Full.FiniteProbability

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



/-- Arithmetic gauge projection costs at most a factor two in the paper's
sharp norm.  This is the exact finite form of the rowwise step used on the
right side of the regression equation: a bound
`|x_j| <= C * alpha_j` remains a sharp bound after applying
`P_{alpha,n}`.  Positivity of the actual harmonic masses and centers proves
the weighted-mean estimate; no operator bound is assumed. -/
theorem projectRawBandVector_paperSharpNorm_le_two
    [Nonempty Band]
    (x : Band → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hx : ∀ j, |x j| ≤ C * B.bandCenter j) :
    paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.projectRawBandVector x) ≤ 2 * C := by
  let u : Band → ℝ := fun j ↦ x j / B.bandCenter j
  let omega : Band → ℝ :=
    sharpWeight B.harmonicMass B.bandCenter
  let total : ℝ := sharpWeightTotal B.harmonicMass B.bandCenter
  have hAlpha (j : Band) : B.bandCenter j ≠ 0 :=
    B.partition.center_ne_zero B.n_gt_one j
  have hAlphaPos (j : Band) : 0 < B.bandCenter j :=
    B.bandCenter_pos j
  have hTotal : 0 < total := by
    simpa only [total] using B.sharpBandWeightTotal_pos
  have hu (j : Band) : |u j| ≤ C := by
    dsimp only [u]
    rw [abs_div, abs_of_pos (hAlphaPos j)]
    exact (div_le_iff₀ (hAlphaPos j)).2 (by
      simpa only [mul_comm] using hx j)
  have hOmega (j : Band) : 0 ≤ omega j := by
    dsimp only [omega]
    exact sharpWeight_nonneg_of_mass_nonneg
      B.harmonicMass B.bandCenter
      (fun k ↦ (B.harmonicMass_pos k).le) j
  have hMean :
      |(∑ j, omega j * u j) / total| ≤ C := by
    rw [abs_div, abs_of_pos hTotal]
    calc
      |∑ j, omega j * u j| / total ≤
          (∑ j, |omega j * u j|) / total :=
        div_le_div_of_nonneg_right
          (Finset.abs_sum_le_sum_abs _ _) hTotal.le
      _ ≤ (∑ j, omega j * C) / total := by
        apply div_le_div_of_nonneg_right _ hTotal.le
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, abs_of_nonneg (hOmega j)]
        exact mul_le_mul_of_nonneg_left (hu j) (hOmega j)
      _ = C := by
        rw [← Finset.sum_mul]
        change total * C / total = C
        field_simp [ne_of_gt hTotal]
  have hScale : scaleByCenter B.bandCenter u = x := by
    funext j
    unfold scaleByCenter u
    field_simp [hAlpha j]
  have hProjected (j : Band) :
      (B.projectRawBandVector x).1 j / B.bandCenter j =
        u j - (∑ k, omega k * u k) / total := by
    have hconj := congrFun
      (unscale_weightedGaugeProjection_scale_eq
        B.harmonicMass B.bandCenter u hAlpha (ne_of_gt hTotal)) j
    change weightedGaugeProjection B.harmonicMass B.bandCenter
        (scaleByCenter B.bandCenter u) j / B.bandCenter j = _ at hconj
    rw [hScale] at hconj
    simpa only [BridgeData.projectRawBandVector, omega, total] using hconj
  rw [paperSharpNorm_eq_piNorm]
  have hTwoC : 0 ≤ 2 * C := mul_nonneg (by norm_num) hC
  rw [pi_norm_le_iff_of_nonneg hTwoC]
  intro j
  rw [Real.norm_eq_abs, hProjected]
  exact (abs_sub _ _).trans (by linarith [hu j, hMean])

















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperWeightedGaugeDGeometry -/
section


/-!
# Finite `D`-pairing geometry in the paper's sharp gauge

These are the exact finite weighted inequalities used when covariance
Cauchy--Schwarz is combined with the sharp-gauge inverse.  No continuum
centre or limiting weight is introduced.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.PaperWeightedInverseExport

open MovingLowGaugeTransfer

variable {Band : Type*} [Fintype Band] [Nonempty Band]





theorem rawDLowerWeight_le (H alpha : Band → ℝ) (j : Band) :
    rawDLowerWeight H alpha ≤ H j * alpha j ^ 2 := by
  classical
  unfold rawDLowerWeight
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

/-- Positivity of the literal finite minimum. -/
theorem rawDLowerWeight_pos
    (H alpha : Band → ℝ) (hH : ∀ j, 0 < H j)
    (hAlpha : ∀ j, alpha j ≠ 0) :
    0 < rawDLowerWeight H alpha := by
  classical
  let s : Finset ℝ := Finset.univ.image (fun j ↦ H j * alpha j ^ 2)
  have hs : s.Nonempty := Finset.univ_nonempty.image _
  have hmem := Finset.min'_mem s hs
  obtain ⟨j, hj, hEq⟩ := Finset.mem_image.mp hmem
  have hAlphaSq : 0 < alpha j ^ 2 := sq_pos_of_ne_zero (hAlpha j)
  unfold rawDLowerWeight
  change 0 < s.min' hs
  rw [← hEq]
  exact mul_pos (hH j) hAlphaSq

/-- The `D` quadratic form controls the paper's sharp supremum norm by the
smallest literal sharp diagonal weight. -/
theorem rawDLowerWeight_mul_paperSharpNorm_sq_le
    (H alpha : Band → ℝ) (hH : ∀ j, 0 < H j)
    (hAlpha : ∀ j, alpha j ≠ 0)
    (q : RawGaugeSpace H alpha) :
    rawDLowerWeight H alpha *
        paperSharpNorm H alpha hAlpha q ^ 2 ≤
      rawDPairing H alpha q q := by
  classical
  let f : Band → ℝ := fun j ↦ q.1 j / alpha j
  obtain ⟨j, hj, hsup⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun k : Band ↦ ‖f k‖₊)
  have hnorm : paperSharpNorm H alpha hAlpha q = |f j| := by
    rw [paperSharpNorm_eq_piNorm]
    change ‖f‖ = |f j|
    rw [Pi.norm_def, ← Finset.sup'_eq_sup Finset.univ_nonempty, hsup]
    simp only [coe_nnnorm, Real.norm_eq_abs]
  have hmin0 : 0 ≤ rawDLowerWeight H alpha :=
    (rawDLowerWeight_pos H alpha hH hAlpha).le
  have hterm :
      rawDLowerWeight H alpha * |f j| ^ 2 ≤ H j * q.1 j ^ 2 := by
    calc
      rawDLowerWeight H alpha * |f j| ^ 2 ≤
          (H j * alpha j ^ 2) * |f j| ^ 2 :=
        mul_le_mul_of_nonneg_right (rawDLowerWeight_le H alpha j)
          (sq_nonneg _)
      _ = H j * q.1 j ^ 2 := by
        dsimp only [f]
        rw [sq_abs]
        field_simp [hAlpha j]
  rw [hnorm]
  exact hterm.trans (by
    unfold rawDPairing
    simpa only [pow_two, mul_assoc] using
      (Finset.single_le_sum
        (fun k hk ↦ mul_nonneg (hH k).le (sq_nonneg (q.1 k)))
        (Finset.mem_univ j)))

/-- Absolute `D` pairing is bounded by the total sharp weight times the two
paper-sharp norms. -/
theorem abs_rawDPairing_le_sharpWeightTotal_mul
    (H alpha : Band → ℝ) (hH : ∀ j, 0 < H j)
    (hAlpha : ∀ j, alpha j ≠ 0)
    (q r : RawGaugeSpace H alpha) :
    |rawDPairing H alpha q r| ≤
      sharpWeightTotal H alpha * paperSharpNorm H alpha hAlpha q *
        paperSharpNorm H alpha hAlpha r := by
  have hq (j : Band) :
      |q.1 j / alpha j| ≤ paperSharpNorm H alpha hAlpha q := by
    rw [paperSharpNorm_eq_piNorm]
    simpa only [Real.norm_eq_abs] using
      ((pi_norm_le_iff_of_nonempty
        (fun k ↦ q.1 k / alpha k)).mp le_rfl j)
  have hr (j : Band) :
      |r.1 j / alpha j| ≤ paperSharpNorm H alpha hAlpha r := by
    rw [paperSharpNorm_eq_piNorm]
    simpa only [Real.norm_eq_abs] using
      ((pi_norm_le_iff_of_nonempty
        (fun k ↦ r.1 k / alpha k)).mp le_rfl j)
  have hq0 : 0 ≤ paperSharpNorm H alpha hAlpha q := norm_nonneg _
  have hr0 : 0 ≤ paperSharpNorm H alpha hAlpha r := norm_nonneg _
  calc
    |rawDPairing H alpha q r| ≤
        ∑ j, |H j * q.1 j * r.1 j| := by
      unfold rawDPairing
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (H j * alpha j ^ 2) *
          paperSharpNorm H alpha hAlpha q *
            paperSharpNorm H alpha hAlpha r := by
      apply Finset.sum_le_sum
      intro j hj
      have hweight : 0 ≤ H j * alpha j ^ 2 :=
        mul_nonneg (hH j).le (sq_nonneg _)
      have hratio :
          |q.1 j / alpha j| * |r.1 j / alpha j| ≤
            paperSharpNorm H alpha hAlpha q *
              paperSharpNorm H alpha hAlpha r :=
        mul_le_mul (hq j) (hr j) (abs_nonneg _) hq0
      calc
        |H j * q.1 j * r.1 j| =
            (H j * alpha j ^ 2) *
              (|q.1 j / alpha j| * |r.1 j / alpha j|) := by
          rw [abs_mul, abs_mul, abs_of_pos (hH j), abs_div, abs_div,
            ← sq_abs]
          field_simp [abs_ne_zero.mpr (hAlpha j)]
        _ ≤ (H j * alpha j ^ 2) *
              (paperSharpNorm H alpha hAlpha q *
                paperSharpNorm H alpha hAlpha r) :=
          mul_le_mul_of_nonneg_left hratio hweight
        _ = (H j * alpha j ^ 2) *
              paperSharpNorm H alpha hAlpha q *
                paperSharpNorm H alpha hAlpha r := by ring
    _ = sharpWeightTotal H alpha * paperSharpNorm H alpha hAlpha q *
          paperSharpNorm H alpha hAlpha r := by
      unfold sharpWeightTotal sharpWeight
      rw [← Finset.sum_mul, ← Finset.sum_mul]

end Erdos390.Full.PaperWeightedInverseExport

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

/-- The quadratic form of the literal arithmetic band Schur map is exactly
the variance of the band score after the actual finite nuisance regression.
This is an equality at finite `n`, in the arithmetic `D`-pairing. -/
theorem actualBandSchur_quadratic_eq_residualVariance
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge) :
    (∑ j : Band, B.harmonicMass j * q.1 j *
        (B.actualBandSchurLinearMap xi hgamma hgap q).1 j) =
      (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q))
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q)) := by
  let F : B.sampleData.Sample → ℝ := B.bandRegressionScore q
  let a : B.NuisanceSpace :=
    B.nuisanceCoefficientOfScore xi hgamma hgap F
  let Z : B.sampleData.Sample → ℝ :=
    fun m ↦ inner ℝ a (B.nuisanceStatistic m)
  let R : B.sampleData.Sample → ℝ :=
    B.nuisanceResidualScore xi hgamma hgap F
  have hF : F = fun m ↦ R m + Z m := by
    funext m
    simp only [F, R, Z, a]
    unfold nuisanceResidualScore
    ring
  have horth : (B.tiltedLaw xi).covariance Z R = 0 := by
    simpa only [Z, R, a] using
      B.nuisanceResidualScore_covariance_zero
        xi hgamma hgap F a
  calc
    (∑ j : Band, B.harmonicMass j * q.1 j *
        (B.actualBandSchurLinearMap xi hgamma hgap q).1 j) =
        ∑ j : Band, B.harmonicMass j * q.1 j *
          B.normalizedBandCovarianceRow xi R j := by
      exact B.weighted_pairing_projectRawBandVector q
        (B.normalizedBandCovarianceRow xi R)
    _ = (B.tiltedLaw xi).covariance F R := by
      exact (B.covariance_bandRegressionScore_eq_weightedRow
        xi q R).symm
    _ = (B.tiltedLaw xi).covariance R R := by
      rw [hF, FiniteProbability.covariance_add_left, horth, add_zero]

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

/-- Covariance Cauchy--Schwarz converts an inverse bound for the literal
band Schur map into a quantitative `D`-quadratic estimate.  The two displayed
`D` comparisons are pure finite weighted-gauge geometry; they are kept as
arguments here so this analytic attachment cannot silently change norms. -/
theorem actualBandSchur_quadratic_mul_bound_of_inverse
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    {Cinv Dlower Dupper : ℝ}
    (hCinv : 0 ≤ Cinv) (hDlower : 0 ≤ Dlower)
    (hDupper : 0 ≤ Dupper)
    (hinv : ∀ v,
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) (e.symm v) ≤
        Cinv * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) v)
    (hDdiag : ∀ v,
      Dlower *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) v ^ 2 ≤
        B.bandDPairing v v)
    (hDbilin : ∀ v u,
      |B.bandDPairing v u| ≤
        Dupper *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) v *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) u)
    (q : B.RawBandGauge) :
    Dlower ^ 2 *
        paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
      (Dupper * Cinv) *
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore q))
          (B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore q)) := by
  let S : B.RawBandGauge → ℝ := fun v ↦
    paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) v
  let R : B.RawBandGauge → B.sampleData.Sample → ℝ := fun v ↦
    B.nuisanceResidualScore xi hgamma hgap (B.bandRegressionScore v)
  let Q : B.RawBandGauge → ℝ := fun v ↦
    (B.tiltedLaw xi).covariance (R v) (R v)
  let y : B.RawBandGauge := e.symm q
  have hey : B.actualBandSchurLinearMap xi hgamma hgap y = q := by
    rw [← he, LinearEquiv.apply_symm_apply]
  have hDqq : Dlower * S q ^ 2 ≤ B.bandDPairing q q := hDdiag q
  have hDqq0 : 0 ≤ B.bandDPairing q q :=
    (mul_nonneg hDlower (sq_nonneg _)).trans hDqq
  have hcross : B.bandDPairing q q =
      (B.tiltedLaw xi).covariance (R q) (R y) := by
    calc
      B.bandDPairing q q =
          B.bandDPairing q
            (B.actualBandSchurLinearMap xi hgamma hgap y) := by rw [hey]
      _ = (B.tiltedLaw xi).covariance (R q) (R y) :=
        B.actualBandSchur_bilinear_eq_residualCovariance
          xi hgamma hgap q y
  have hcs : (B.bandDPairing q q) ^ 2 ≤ Q q * Q y := by
    rw [hcross]
    exact (B.tiltedLaw xi).covariance_sq_le_mul_self (R q) (R y)
  have hQy : Q y = B.bandDPairing y q := by
    calc
      Q y = B.bandDPairing y
          (B.actualBandSchurLinearMap xi hgamma hgap y) :=
        (B.actualBandSchur_quadratic_eq_residualVariance
          xi hgamma hgap y).symm
      _ = B.bandDPairing y q := by rw [hey]
  have hSy : S y ≤ Cinv * S q := hinv q
  have hS0 (v : B.RawBandGauge) : 0 ≤ S v := by
    exact norm_nonneg _
  have hQy0 : 0 ≤ Q y :=
    (B.tiltedLaw xi).covariance_self_nonneg (R y)
  have hQq0 : 0 ≤ Q q :=
    (B.tiltedLaw xi).covariance_self_nonneg (R q)
  have hQyUpper : Q y ≤ Dupper * Cinv * S q ^ 2 := by
    rw [hQy]
    calc
      B.bandDPairing y q ≤ |B.bandDPairing y q| := le_abs_self _
      _ ≤ Dupper * S y * S q := hDbilin y q
      _ ≤ Dupper * (Cinv * S q) * S q := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hSy hDupper) (hS0 q)
      _ = Dupper * Cinv * S q ^ 2 := by ring
  by_cases hSq : S q = 0
  · change Dlower ^ 2 * S q ^ 2 ≤ (Dupper * Cinv) * Q q
    rw [hSq]
    norm_num
    exact mul_nonneg (mul_nonneg hDupper hCinv) hQq0
  · have hSqPos : 0 < S q := lt_of_le_of_ne (hS0 q) (Ne.symm hSq)
    have hDsq : (Dlower * S q ^ 2) ^ 2 ≤
        (B.bandDPairing q q) ^ 2 := by
      exact sq_le_sq₀ (mul_nonneg hDlower (sq_nonneg _)) hDqq0 |>.2 hDqq
    have hmaster : (Dlower * S q ^ 2) ^ 2 ≤
        Q q * (Dupper * Cinv * S q ^ 2) := by
      exact hDsq.trans (hcs.trans
        (mul_le_mul_of_nonneg_left hQyUpper hQq0))
    nlinarith [sq_pos_of_pos hSqPos]

/-- Division form of the preceding quantitative gap. -/
theorem actualBandSchur_quadratic_lower_of_inverse
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    {Cinv Dlower Dupper : ℝ}
    (hCinv : 0 < Cinv) (hDlower : 0 ≤ Dlower)
    (hDupper : 0 < Dupper)
    (hinv : ∀ v,
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) (e.symm v) ≤
        Cinv * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) v)
    (hDdiag : ∀ v,
      Dlower *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) v ^ 2 ≤
        B.bandDPairing v v)
    (hDbilin : ∀ v u,
      |B.bandDPairing v u| ≤
        Dupper *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) v *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) u)
    (q : B.RawBandGauge) :
    (Dlower ^ 2 / (Dupper * Cinv)) *
        paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q))
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q)) := by
  have hmul := B.actualBandSchur_quadratic_mul_bound_of_inverse
    xi hgamma hgap e he hCinv.le hDlower hDupper.le
    hinv hDdiag hDbilin q
  have hden : 0 < Dupper * Cinv := mul_pos hDupper hCinv
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).2
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Literal arithmetic specialization of the inverse-to-quadratic theorem.
The two `D` constants and both weighted inequalities are now conclusions of
the finite positive harmonic masses and centres. -/
theorem actualBandSchur_quadratic_lower_of_inverse_arithmetic
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    {Cinv : ℝ} (hCinv : 0 < Cinv)
    (hinv : ∀ v,
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) (e.symm v) ≤
        Cinv * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) v)
    (q : B.RawBandGauge) :
    (rawDLowerWeight B.harmonicMass B.bandCenter ^ 2 /
        (sharpWeightTotal B.harmonicMass B.bandCenter * Cinv)) *
        paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q))
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q)) := by
  apply B.actualBandSchur_quadratic_lower_of_inverse
    xi hgamma hgap e he hCinv
    (rawDLowerWeight_pos B.harmonicMass B.bandCenter
      B.harmonicMass_pos
      (B.partition.center_ne_zero B.n_gt_one)).le
    B.sharpBandWeightTotal_pos
    hinv
  · intro v
    simpa only [bandDPairing, rawDPairing] using
      rawDLowerWeight_mul_paperSharpNorm_sq_le
        B.harmonicMass B.bandCenter B.harmonicMass_pos
        (B.partition.center_ne_zero B.n_gt_one) v
  · intro v u
    simpa only [bandDPairing, rawDPairing] using
      abs_rawDPairing_le_sharpWeightTotal_mul
        B.harmonicMass B.bandCenter B.harmonicMass_pos
        (B.partition.center_ne_zero B.n_gt_one) v u









end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualFullBandIdentification -/
section


/-!
# Exact identification of the actual full-valuation band operator

The full-valuation sharp operator produced by Lemmas 7.5 and 8.4 is defined
through the bounded valuation law.  The nonlinear bridge is written through
covariance rows of the actual tilted sample.  This file proves that these
are the same finite operator before nuisance regression, and records the
exact sharp/raw gauge conjugacy.  No asymptotic estimate is used.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The bounded-law full band row is literally the normalized covariance row
of the actual tilted bridge law. -/
theorem fullBandRow_actualValuationLaw_eq_normalizedBandCovarianceRow
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge) (i : Band) :
    PrimePowerSharpBandTransfer.fullBandRow
        (B.actualValuationLaw xi) B.partition q.1 i =
      B.normalizedBandCovarianceRow xi
        (B.bandRegressionScore q) i := by
  have hscore : B.bandRegressionScore q =
      fun m ↦ ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.bandRegressionCoefficient q p *
          ArithmeticModel.valuation p.1 (B.sampleData.value m) := by
    funext m
    exact B.bandRegressionScore_eq_primeSum q m
  rw [hscore]
  unfold PrimePowerSharpBandTransfer.fullBandRow
    normalizedBandCovarianceRow bandScore
    PrimePowerCovariance.BoundedValuationLaw.covVV
    PrimePowerCovariance.BoundedValuationLaw.V
    actualValuationLaw
  rw [FiniteProbability.covariance_sum_left]
  simp_rw [FiniteProbability.covariance_sum_right,
    FiniteProbability.covariance_smul_right]
  simp only [bandRegressionCoefficient]
  change (1 / B.harmonicMass i) * _ = _ / B.harmonicMass i
  ring



/-- Scaling the literal full sharp operator back to raw coordinates gives
exactly `actualBandFullLinearMap`. -/
theorem scale_actualFullProjected_eq_actualBandFull
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace)
    (q : PaperWeightedInverseExport.SharpGaugeSpace
      B.harmonicMass B.bandCenter) :
    scaleGaugeLinearEquiv B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.actualFullProjectedCLM xi q) =
      B.actualBandFullLinearMap xi
        (scaleGaugeLinearEquiv B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q) := by
  apply Subtype.ext
  funext i
  let S := scaleGaugeLinearEquiv B.harmonicMass B.bandCenter
    (B.partition.center_ne_zero B.n_gt_one)
  change B.bandCenter i *
      FiniteGraphQuotientInverse.meanProjection
        (MovingLowGaugeTransfer.sharpWeight
          B.harmonicMass B.bandCenter)
        (fun j ↦ PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q.1 j) i =
    MovingLowGaugeTransfer.weightedGaugeProjection
      B.harmonicMass B.bandCenter
      (B.normalizedBandCovarianceRow xi
        (B.bandRegressionScore (S q))) i
  have hrow :
      B.normalizedBandCovarianceRow xi
        (B.bandRegressionScore (S q)) =
      MovingLowGaugeTransfer.scaleByCenter B.bandCenter
        (fun j ↦ PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q.1 j) := by
    funext j
    rw [← B.fullBandRow_actualValuationLaw_eq_normalizedBandCovarianceRow]
    unfold PrimePowerSharpBandTransfer.fullSharpRow
    change PrimePowerSharpBandTransfer.fullBandRow
        (B.actualValuationLaw xi) B.partition (S q).1 j =
      B.bandCenter j *
        (PrimePowerSharpBandTransfer.fullBandRow
          (B.actualValuationLaw xi) B.partition
            (fun k ↦ B.bandCenter k * q.1 k) j / B.bandCenter j)
    have hscaled : (S q).1 =
        fun k ↦ B.bandCenter k * q.1 k := by
      funext k
      exact scaleGaugeLinearEquiv_apply
        B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one) q k
    rw [hscaled]
    exact (mul_div_cancel₀ _
      (B.partition.center_ne_zero B.n_gt_one j)).symm
  rw [hrow]
  exact (PaperWeightedInverseExport.weightedGaugeProjection_scale_eq
    B.harmonicMass B.bandCenter
    (fun j ↦ PrimePowerSharpBandTransfer.fullSharpRow
      (B.actualValuationLaw xi) B.partition q.1 j)
    (B.partition.center_ne_zero B.n_gt_one)
    (ne_of_gt B.sharpBandWeightTotal_pos) i).symm

/-- Exact finite nuisance-Schur correction.  The correction is displayed as
the projected normalized row of the actual regression coefficient; it is not
discarded as a generic `o(1)` perturbation. -/
theorem actualBandSchurLinearMap_eq_full_sub_nuisanceCorrection
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge) :
    B.actualBandSchurLinearMap xi hgamma hgap q =
      B.actualBandFullLinearMap xi q -
        B.projectRawBandVector
          (B.normalizedBandCovarianceRow xi
            (fun m ↦ inner ℝ
              (B.nuisanceCoefficientOfScore xi hgamma hgap
                (B.bandRegressionScore q))
              (B.nuisanceStatistic m))) := by
  change B.projectRawBandVector
      (B.normalizedBandCovarianceRow xi
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q))) =
    B.projectRawBandVector
        (B.normalizedBandCovarianceRow xi (B.bandRegressionScore q)) -
      B.projectRawBandVector
        (B.normalizedBandCovarianceRow xi
          (fun m ↦ inner ℝ
            (B.nuisanceCoefficientOfScore xi hgamma hgap
              (B.bandRegressionScore q))
            (B.nuisanceStatistic m)))
  unfold nuisanceResidualScore
  rw [B.normalizedBandCovarianceRow_sub]
  exact B.projectRawBandVector_sub _ _









/-- If the sharp equivalence represents the actual Schur operator, its raw
transport is literally `actualBandSchurLinearMap`. -/
theorem rawBandEquivOfSharpEquiv_eq_actualBandSchurLinearMap
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
      SharpGaugeSpace B.partition.mass B.partition.center)
    (he : ∀ q, e q = B.actualSchurProjectedCLM xi hgamma hgap q)
    (b : RawGaugeSpace B.partition.mass B.partition.center) :
    B.rawBandEquivOfSharpEquiv e b =
      B.actualBandSchurLinearMap xi hgamma hgap b := by
  let S := scaleGaugeLinearEquiv B.partition.mass B.partition.center
    (B.partition.center_ne_zero B.n_gt_one)
  change S (e (S.symm b)) = B.actualBandSchurLinearMap xi hgamma hgap b
  rw [he]
  change S (S.symm
    (B.actualBandSchurLinearMap xi hgamma hgap (S (S.symm b)))) = _
  rw [S.apply_symm_apply, S.apply_symm_apply]

/-- The sharp inverse estimate is exactly the paper's weighted raw-gauge
inverse estimate after transport. -/
theorem rawBandEquivOfSharpEquiv_symm_paperSharpNorm_le
    [Nonempty Band]
    (e : SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
      SharpGaugeSpace B.partition.mass B.partition.center)
    {C : ℝ} (hinv : ∀ v, ‖e.symm v‖ ≤ C * ‖v‖)
    (u : RawGaugeSpace B.partition.mass B.partition.center) :
    paperSharpNorm B.partition.mass B.partition.center
        (B.partition.center_ne_zero B.n_gt_one)
        ((B.rawBandEquivOfSharpEquiv e).symm u) ≤
      C * paperSharpNorm B.partition.mass B.partition.center
        (B.partition.center_ne_zero B.n_gt_one) u := by
  let S := scaleGaugeLinearEquiv B.partition.mass B.partition.center
    (B.partition.center_ne_zero B.n_gt_one)
  let Eraw := B.rawBandEquivOfSharpEquiv e
  change ‖S.symm (Eraw.symm u)‖ ≤ C * ‖S.symm u‖
  have hinvEq : Eraw.symm u = S (e.symm (S.symm u)) := by
    apply Eraw.injective
    rw [Eraw.apply_symm_apply]
    change u = S (e (S.symm (S (e.symm (S.symm u)))))
    rw [S.symm_apply_apply, e.apply_symm_apply, S.apply_symm_apply]
  rw [hinvEq, S.symm_apply_apply]
  exact hinv (S.symm u)

/-- A literal row-relative estimate for the finite nuisance correction gives
the sharp operator-norm perturbation used in the Schur step.  This theorem
contains no asymptotic input: the application must supply the displayed
row estimate, uniformly in the preselected tilt box. -/
theorem actualSchurProjectedCLM_sub_full_le_of_nuisanceCorrectionRow
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    {r : ℝ} (hr : 0 ≤ r)
    (hrow : ∀
      (q : SharpGaugeSpace B.partition.mass B.partition.center) (i : Band),
      |B.normalizedBandCovarianceRow xi
          (fun m ↦ inner ℝ
            (B.nuisanceCoefficientOfScore xi hgamma hgap
              (B.bandRegressionScore
                (scaleGaugeLinearEquiv B.partition.mass B.partition.center
                  (B.partition.center_ne_zero B.n_gt_one) q)))
            (B.nuisanceStatistic m)) i| ≤
        (r * ‖q‖) * B.bandCenter i)
    (q : SharpGaugeSpace B.partition.mass B.partition.center) :
    ‖(B.actualSchurProjectedCLM xi hgamma hgap -
        B.actualFullProjectedCLM xi) q‖ ≤
      (2 * r) * ‖q‖ := by
  let S := scaleGaugeLinearEquiv B.partition.mass B.partition.center
    (B.partition.center_ne_zero B.n_gt_one)
  let correction : Band → ℝ := fun i ↦
    B.normalizedBandCovarianceRow xi
      (fun m ↦ inner ℝ
        (B.nuisanceCoefficientOfScore xi hgamma hgap
          (B.bandRegressionScore (S q)))
        (B.nuisanceStatistic m)) i
  have hcorrection (i : Band) :
      |correction i| ≤ (r * ‖q‖) * B.bandCenter i := by
    exact hrow q i
  have hC : 0 ≤ r * ‖q‖ := mul_nonneg hr (norm_nonneg q)
  have hproject :
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one)
          (B.projectRawBandVector correction) ≤
        2 * (r * ‖q‖) :=
    B.projectRawBandVector_paperSharpNorm_le_two
      correction hC hcorrection
  have hfull :
      S.symm (B.actualBandFullLinearMap xi (S q)) =
        B.actualFullProjectedCLM xi q := by
    apply S.injective
    rw [S.apply_symm_apply]
    exact (B.scale_actualFullProjected_eq_actualBandFull xi q).symm
  have hschur :
      S.symm (B.actualBandSchurLinearMap xi hgamma hgap (S q)) =
        B.actualSchurProjectedCLM xi hgamma hgap q := by
    rfl
  rw [ContinuousLinearMap.sub_apply, ← hschur, ← hfull]
  rw [← map_sub]
  have hraw := B.actualBandSchurLinearMap_eq_full_sub_nuisanceCorrection
    xi hgamma hgap (S q)
  change ‖S.symm
      (B.actualBandSchurLinearMap xi hgamma hgap (S q) -
        B.actualBandFullLinearMap xi (S q))‖ ≤ (2 * r) * ‖q‖
  rw [hraw]
  simp only [sub_sub_cancel_left]
  change ‖S.symm (-B.projectRawBandVector correction)‖ ≤ (2 * r) * ‖q‖
  calc
    ‖S.symm (-B.projectRawBandVector correction)‖ =
        ‖-S.symm (B.projectRawBandVector correction)‖ :=
      congrArg norm (map_neg S.symm (B.projectRawBandVector correction))
    _ = ‖S.symm (B.projectRawBandVector correction)‖ := norm_neg _
    _ ≤ (2 * r) * ‖q‖ :=
      hproject.trans_eq (show 2 * (r * ‖q‖) = (2 * r) * ‖q‖ by ring)

/-- Two literal covariance-vector estimates imply the relative nuisance
correction row.  This is the exact finite aggregation needed to attach an
analytic marked-row theorem: `hsource` controls the nuisance coefficient,
while `hband` controls the marked output band.  The factor `1 / amin` is
kept visible, so at the moving low cell an application must prove a rate
strong enough to dominate the vanishing minimum centre. -/
theorem actualSchurProjectedCLM_sub_full_le_of_nuisanceCovarianceBounds
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    {Csource Crow amin : ℝ}
    (hCsource : 0 ≤ Csource) (hCrow : 0 ≤ Crow) (hamin : 0 < amin)
    (hcenter : ∀ i : Band, amin ≤ B.bandCenter i)
    (hsource : ∀ q :
      SharpGaugeSpace B.partition.mass B.partition.center,
      ‖B.nuisanceCovarianceVector xi
          (B.bandRegressionScore
            (scaleGaugeLinearEquiv B.partition.mass B.partition.center
              (B.partition.center_ne_zero B.n_gt_one) q))‖ ≤
        Csource * ‖q‖)
    (hband : ∀ i : Band,
      ‖B.nuisanceCovarianceVector xi (B.bandScore i)‖ ≤
        Crow * B.harmonicMass i)
    (q : SharpGaugeSpace B.partition.mass B.partition.center) :
    ‖(B.actualSchurProjectedCLM xi hgamma hgap -
        B.actualFullProjectedCLM xi) q‖ ≤
      (2 * (((Csource / gamma) * Crow) / amin)) * ‖q‖ := by
  let A : ℝ := (Csource / gamma) * Crow
  have hA : 0 ≤ A := by
    exact mul_nonneg (div_nonneg hCsource hgamma.le) hCrow
  have hrow : ∀
      (q' : SharpGaugeSpace B.partition.mass B.partition.center) (i : Band),
      |B.normalizedBandCovarianceRow xi
          (fun m ↦ inner ℝ
            (B.nuisanceCoefficientOfScore xi hgamma hgap
              (B.bandRegressionScore
                (scaleGaugeLinearEquiv B.partition.mass B.partition.center
                  (B.partition.center_ne_zero B.n_gt_one) q')))
            (B.nuisanceStatistic m)) i| ≤
        ((A / amin) * ‖q'‖) * B.bandCenter i := by
    intro q' i
    let S' := scaleGaugeLinearEquiv B.partition.mass B.partition.center
      (B.partition.center_ne_zero B.n_gt_one)
    let z' := B.nuisanceCoefficientOfScore xi hgamma hgap
      (B.bandRegressionScore (S' q'))
    change |B.normalizedBandCovarianceRow xi
        (fun m ↦ inner ℝ z' (B.nuisanceStatistic m)) i| ≤ _
    have hz' : ‖z'‖ ≤ (Csource / gamma) * ‖q'‖ := by
      calc
        ‖z'‖ ≤
            ‖B.nuisanceCovarianceVector xi
              (B.bandRegressionScore (S' q'))‖ / gamma :=
          B.nuisanceCoefficientOfScore_norm_le xi hgamma hgap _
        _ ≤ (Csource * ‖q'‖) / gamma :=
          div_le_div_of_nonneg_right (hsource q') hgamma.le
        _ = (Csource / gamma) * ‖q'‖ := by ring
    have hH : 0 < B.harmonicMass i := B.harmonicMass_pos i
    unfold normalizedBandCovarianceRow
    rw [B.covariance_marked_nuisanceScore_eq_inner,
      abs_div, abs_of_pos hH]
    have hinner := abs_real_inner_le_norm z'
      (B.nuisanceCovarianceVector xi (B.bandScore i))
    calc
      |inner ℝ z' (B.nuisanceCovarianceVector xi (B.bandScore i))| /
            B.harmonicMass i ≤
          (‖z'‖ * ‖B.nuisanceCovarianceVector xi (B.bandScore i)‖) /
            B.harmonicMass i :=
        div_le_div_of_nonneg_right hinner hH.le
      _ ≤ (((Csource / gamma) * ‖q'‖) *
            (Crow * B.harmonicMass i)) / B.harmonicMass i := by
        apply div_le_div_of_nonneg_right _ hH.le
        exact mul_le_mul hz' (hband i) (norm_nonneg _)
          (mul_nonneg (div_nonneg hCsource hgamma.le) (norm_nonneg q'))
      _ = A * ‖q'‖ := by
        dsimp only [A]
        field_simp [ne_of_gt hH]
      _ = ((A / amin) * ‖q'‖) * amin := by
        field_simp [ne_of_gt hamin]
      _ ≤ ((A / amin) * ‖q'‖) * B.bandCenter i :=
        mul_le_mul_of_nonneg_left (hcenter i)
          (mul_nonneg (div_nonneg hA hamin.le) (norm_nonneg q'))
  exact B.actualSchurProjectedCLM_sub_full_le_of_nuisanceCorrectionRow
    xi hgamma hgap (div_nonneg hA hamin.le) hrow q



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualSchurMarkedRow -/
section


/-!
# Attaching reciprocal nuisance marked rows to the actual Schur operator

This file performs the finite summations that turn a coordinatewise bound
`|Cov(Z_c,v_p)| <= Cmarked / p` into the two covariance-vector bounds used
by the exact Schur perturbation theorem.  The analytic rate remains a
literal hypothesis; in particular the proof does not replace the required
`O(1/(pL))` estimate by a merely bounded `O(1/p)` row.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Summing a reciprocal marked-prime estimate over one literal band gives
exactly its harmonic mass. -/
theorem abs_covariance_nuisance_bandScore_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace) (c : NuisanceCoord B.HeadIndex) (i : Band)
    {Cmarked : ℝ}
    (hmarked : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ))) :
    |(B.tiltedLaw xi).covariance
      (fun m ↦ B.nuisanceStatistic m c) (B.bandScore i)| ≤
        Cmarked * B.harmonicMass i := by
  let mu := B.tiltedLaw xi
  let Z : B.sampleData.Sample → ℝ :=
    fun m ↦ B.nuisanceStatistic m c
  have hsum :
      mu.covariance Z (B.bandScore i) =
        ∑ p ∈ B.partition.data.fiber i,
          mu.covariance Z
            (fun m ↦ ArithmeticModel.valuation p.1
              (B.sampleData.value m)) := by
    unfold bandScore
    rw [mu.covariance_sum_right]
  change |mu.covariance Z (B.bandScore i)| ≤ _
  rw [hsum]
  calc
    |∑ p ∈ B.partition.data.fiber i,
        mu.covariance Z
          (fun m ↦ ArithmeticModel.valuation p.1
            (B.sampleData.value m))| ≤
        ∑ p ∈ B.partition.data.fiber i,
          |mu.covariance Z
            (fun m ↦ ArithmeticModel.valuation p.1
              (B.sampleData.value m))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ B.partition.data.fiber i,
        Cmarked * (1 / (p.1 : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hmarked p
    _ = Cmarked * B.harmonicMass i := by
      change (∑ p ∈ B.partition.data.fiber i,
        Cmarked * (1 / (p.1 : ℝ))) =
          Cmarked * ∑ p ∈ B.partition.data.fiber i,
            (1 / (p.1 : ℝ))
      rw [Finset.mul_sum]

/-- Euclidean vector form of the preceding one-band summation. -/
theorem nuisanceCovarianceVector_bandScore_norm_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace) (i : Band)
    {Cmarked : ℝ} (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ))) :
    ‖B.nuisanceCovarianceVector xi (B.bandScore i)‖ ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        (Cmarked * B.harmonicMass i) := by
  have hK : 0 ≤ Cmarked * B.harmonicMass i :=
    mul_nonneg hCmarked (B.harmonicMass_pos i).le
  exact B.nuisanceCovarianceVector_norm_le_sqrt_card_mul
    xi (B.bandScore i) hK (fun c ↦
      B.abs_covariance_nuisance_bandScore_le_of_marked
        xi c i (fun p ↦ hmarked c p))

/-- The same reciprocal marked family controls the nuisance covariance of
every sharp-gauge band score.  The finite factor is the exact arithmetic
first moment `sum_i H_i alpha_i`; no continuum replacement is made. -/
theorem abs_covariance_nuisance_scaledBandRegression_le_of_marked
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) (c : NuisanceCoord B.HeadIndex)
    {Cmarked : ℝ}
    (hmarked : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (q : SharpGaugeSpace B.partition.mass B.partition.center) :
    |(B.tiltedLaw xi).covariance
      (fun m ↦ B.nuisanceStatistic m c)
      (B.bandRegressionScore
        (scaleGaugeLinearEquiv B.partition.mass B.partition.center
          (B.partition.center_ne_zero B.n_gt_one) q))| ≤
      (Cmarked *
        (∑ j : Band, B.harmonicMass j * B.bandCenter j)) * ‖q‖ := by
  let mu := B.tiltedLaw xi
  let Z : B.sampleData.Sample → ℝ :=
    fun m ↦ B.nuisanceStatistic m c
  let S := scaleGaugeLinearEquiv B.partition.mass B.partition.center
    (B.partition.center_ne_zero B.n_gt_one)
  have hsum :
      mu.covariance Z (B.bandRegressionScore (S q)) =
        ∑ j : Band, (S q).1 j *
          mu.covariance Z (B.bandScore j) := by
    unfold bandRegressionScore
    rw [show (fun m ↦ ∑ j : Band, (S q).1 j * B.bandScore j m) =
      fun m ↦ ∑ j ∈ (Finset.univ : Finset Band),
        (S q).1 j * B.bandScore j m by simp]
    rw [mu.covariance_sum_right]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mu.covariance_smul_right]
  have hcoeff (j : Band) : |(S q).1 j| ≤ B.bandCenter j * ‖q‖ := by
    rw [show (S q).1 j = B.bandCenter j * q.1 j by rfl,
      abs_mul, abs_of_pos (B.bandCenter_pos j)]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm q.1 j)
      (B.bandCenter_pos j).le
  change |mu.covariance Z (B.bandRegressionScore (S q))| ≤ _
  rw [hsum]
  calc
    |∑ j : Band, (S q).1 j * mu.covariance Z (B.bandScore j)| ≤
        ∑ j : Band, |(S q).1 j *
          mu.covariance Z (B.bandScore j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Band, (B.bandCenter j * ‖q‖) *
        (Cmarked * B.harmonicMass j) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul (hcoeff j)
        (B.abs_covariance_nuisance_bandScore_le_of_marked
          xi c j (fun p ↦ hmarked p))
        (abs_nonneg _)
        (mul_nonneg (B.bandCenter_pos j).le (norm_nonneg q))
    _ = (Cmarked *
        (∑ j : Band, B.harmonicMass j * B.bandCenter j)) * ‖q‖ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Euclidean vector version of the sharp-gauge source estimate. -/
theorem nuisanceCovarianceVector_scaledBandRegression_norm_le_of_marked
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace)
    {Cmarked : ℝ} (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (q : SharpGaugeSpace B.partition.mass B.partition.center) :
    ‖B.nuisanceCovarianceVector xi
      (B.bandRegressionScore
        (scaleGaugeLinearEquiv B.partition.mass B.partition.center
          (B.partition.center_ne_zero B.n_gt_one) q))‖ ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        ((Cmarked *
          (∑ j : Band, B.harmonicMass j * B.bandCenter j)) * ‖q‖) := by
  have hmoment : 0 ≤ ∑ j : Band,
      B.harmonicMass j * B.bandCenter j := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (B.harmonicMass_pos j).le (B.bandCenter_pos j).le
  have hK : 0 ≤ (Cmarked *
      (∑ j : Band, B.harmonicMass j * B.bandCenter j)) * ‖q‖ :=
    mul_nonneg (mul_nonneg hCmarked hmoment) (norm_nonneg q)
  exact B.nuisanceCovarianceVector_norm_le_sqrt_card_mul xi _ hK
    (fun c ↦ B.abs_covariance_nuisance_scaledBandRegression_le_of_marked
      xi c (fun p ↦ hmarked c p) q)



/-- A coordinatewise reciprocal nuisance marked row closes the finite Schur
operator perturbation with the completely explicit rate above.  Therefore an
application with `Cmarked = O(1/L)` and `amin` of order `1/log L` obtains the
required `O(log L/L^2)` sharp error, whereas an `O(1)` marked constant does
not suffice. -/
theorem actualSchurProjectedCLM_sub_full_le_of_marked
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    {Cmarked amin : ℝ} (hCmarked : 0 ≤ Cmarked) (hamin : 0 < amin)
    (hcenter : ∀ i : Band, amin ≤ B.bandCenter i)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (q : SharpGaugeSpace B.partition.mass B.partition.center) :
    ‖(B.actualSchurProjectedCLM xi hgamma hgap -
        B.actualFullProjectedCLM xi) q‖ ≤
      (2 * B.nuisanceMarkedSchurRate Cmarked gamma amin) * ‖q‖ := by
  let droot : ℝ := Real.sqrt
    (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  let moment : ℝ := ∑ j : Band,
    B.harmonicMass j * B.bandCenter j
  let Csource : ℝ := droot * (Cmarked * moment)
  let Crow : ℝ := droot * Cmarked
  have hmoment : 0 ≤ moment := by
    dsimp only [moment]
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (B.harmonicMass_pos j).le (B.bandCenter_pos j).le
  have hdroot : 0 ≤ droot := by
    exact Real.sqrt_nonneg _
  have hCsource : 0 ≤ Csource :=
    mul_nonneg hdroot (mul_nonneg hCmarked hmoment)
  have hCrow : 0 ≤ Crow := mul_nonneg hdroot hCmarked
  have hsource : ∀ q' :
      SharpGaugeSpace B.partition.mass B.partition.center,
      ‖B.nuisanceCovarianceVector xi
          (B.bandRegressionScore
            (scaleGaugeLinearEquiv B.partition.mass B.partition.center
              (B.partition.center_ne_zero B.n_gt_one) q'))‖ ≤
        Csource * ‖q'‖ := by
    intro q'
    have h := B.nuisanceCovarianceVector_scaledBandRegression_norm_le_of_marked
      xi hCmarked hmarked q'
    simpa only [Csource, droot, moment, mul_assoc] using h
  have hband : ∀ i : Band,
      ‖B.nuisanceCovarianceVector xi (B.bandScore i)‖ ≤
        Crow * B.harmonicMass i := by
    intro i
    have h := B.nuisanceCovarianceVector_bandScore_norm_le_of_marked
      xi i hCmarked hmarked
    simpa only [Crow, droot, mul_assoc] using h
  have h :=
    B.actualSchurProjectedCLM_sub_full_le_of_nuisanceCovarianceBounds
      xi hgamma hgap hCsource hCrow hamin hcenter hsource hband q
  simpa only [nuisanceMarkedSchurRate, Csource, Crow, droot, moment] using h



/-- Stable inverse for the literal nuisance-Schur operator, now consuming
only the already constructed full-valuation inverse and a coordinatewise
reciprocal nuisance marked family. -/
theorem exists_actualSchurProjectedEquiv_of_full_of_marked
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace)
    (fullEquiv :
      SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
        SharpGaugeSpace B.partition.mass B.partition.center)
    (hfull : ∀ q, fullEquiv q = B.actualFullProjectedCLM xi q)
    {gamma C Cmarked amin : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hC : 0 ≤ C) (hCmarked : 0 ≤ Cmarked) (hamin : 0 < amin)
    (hcenter : ∀ i : Band, amin ≤ B.bandCenter i)
    (hinv : ∀ v, ‖fullEquiv.symm v‖ ≤ C * ‖v‖)
    (hsmall : C *
      (2 * B.nuisanceMarkedSchurRate Cmarked gamma amin) < 1)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ))) :
    ∃ schurEquiv :
      SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
        SharpGaugeSpace B.partition.mass B.partition.center,
      (∀ q, schurEquiv q =
        B.actualSchurProjectedCLM xi hgamma hgap q) ∧
      ∀ v, ‖schurEquiv.symm v‖ ≤
        (C / (1 - C *
          (2 * B.nuisanceMarkedSchurRate Cmarked gamma amin))) * ‖v‖ := by
  let A := B.actualFullProjectedCLM xi
  let Ainv : SharpGaugeSpace B.partition.mass B.partition.center →L[ℝ]
      SharpGaugeSpace B.partition.mass B.partition.center := fullEquiv.symm
  let delta : ℝ := 2 * B.nuisanceMarkedSchurRate Cmarked gamma amin
  let E := B.actualSchurProjectedCLM xi hgamma hgap - A
  have hleft (q : SharpGaugeSpace B.partition.mass B.partition.center) :
      Ainv (A q) = q := by
    dsimp only [Ainv, A]
    rw [← hfull q]
    exact fullEquiv.symm_apply_apply q
  have hinv' (v : SharpGaugeSpace B.partition.mass B.partition.center) :
      ‖Ainv v‖ ≤ C * ‖v‖ := hinv v
  have herror (q : SharpGaugeSpace B.partition.mass B.partition.center) :
      ‖E q‖ ≤ delta * ‖q‖ := by
    dsimp only [E, A, delta]
    exact B.actualSchurProjectedCLM_sub_full_le_of_marked
      xi hgamma hgap hCmarked hamin hcenter hmarked q
  have hsmall' : C * delta < 1 := by
    simpa only [delta] using hsmall
  let schurEquiv := StableInverse.perturbedEquiv
    A Ainv E C delta hC hsmall' hleft hinv' herror
  refine ⟨schurEquiv, ?_, ?_⟩
  · intro q
    rw [StableInverse.perturbedEquiv_apply]
    dsimp only [schurEquiv, E]
    simp only [add_sub_cancel]
  · intro v
    simpa only [delta] using StableInverse.perturbed_inverse_bound
      A Ainv E C delta hC hsmall' hleft hinv' herror v

/-- End-to-end raw-gauge form consumed by the paper's two-stage regression:
the sharp full inverse and the literal nuisance marked family construct an
actual linear equivalence whose map is exactly the finite Schur band matrix,
with the stated paper-sharp inverse bound. -/
theorem exists_actualBandSchurEquiv_of_full_of_marked
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace)
    (fullEquiv :
      SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
        SharpGaugeSpace B.partition.mass B.partition.center)
    (hfull : ∀ q, fullEquiv q = B.actualFullProjectedCLM xi q)
    {gamma C Cmarked amin : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hC : 0 ≤ C) (hCmarked : 0 ≤ Cmarked) (hamin : 0 < amin)
    (hcenter : ∀ i : Band, amin ≤ B.bandCenter i)
    (hinv : ∀ v, ‖fullEquiv.symm v‖ ≤ C * ‖v‖)
    (hsmall : C *
      (2 * B.nuisanceMarkedSchurRate Cmarked gamma amin) < 1)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ))) :
    ∃ rawEquiv :
      RawGaugeSpace B.partition.mass B.partition.center ≃ₗ[ℝ]
        RawGaugeSpace B.partition.mass B.partition.center,
      (∀ b, rawEquiv b =
        B.actualBandSchurLinearMap xi hgamma hgap b) ∧
      ∀ u,
        paperSharpNorm B.partition.mass B.partition.center
            (B.partition.center_ne_zero B.n_gt_one) (rawEquiv.symm u) ≤
          (C / (1 - C *
            (2 * B.nuisanceMarkedSchurRate Cmarked gamma amin))) *
            paperSharpNorm B.partition.mass B.partition.center
              (B.partition.center_ne_zero B.n_gt_one) u := by
  obtain ⟨sharpEquiv, hsharp, hinvSharp⟩ :=
    B.exists_actualSchurProjectedEquiv_of_full_of_marked
      xi fullEquiv hfull hgamma hgap hC hCmarked hamin hcenter
      hinv hsmall hmarked
  let rawEquiv := B.rawBandEquivOfSharpEquiv sharpEquiv
  refine ⟨rawEquiv, ?_, ?_⟩
  · intro b
    exact B.rawBandEquivOfSharpEquiv_eq_actualBandSchurLinearMap
      xi hgamma hgap sharpEquiv hsharp b
  · intro u
    exact B.rawBandEquivOfSharpEquiv_symm_paperSharpNorm_le
      sharpEquiv hinvSharp u

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalNuisanceUniformFloor -/
section


/-!
# A root uniform lower floor for the canonical nuisance gap

The exact canonical nuisance gap is allowed to use a varying reference head
and a varying positive barycentric target.  This file bounds its two finite
dimensional constants by quantities depending only on the fixed head type,
and replaces the varying cell-mass margin by one prescribed positive floor.
The result is the uniform positive scalar needed before taking an eventual
Schur-smallness threshold.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel PaperGuardCensus









namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The actual nuisance coordinate count is bounded by the full head count
plus the physical coordinate. -/
theorem nuisanceCoord_card_le_head_add_one :
    Fintype.card (NuisanceCoord B.HeadIndex) ≤ Fintype.card Head + 1 := by
  let f : NuisanceCoord B.HeadIndex → Option Head
    | .physical => none
    | .head h => some h.1
  have hf : Function.Injective f := by
    intro x y hxy
    cases x <;> cases y <;> simp_all [f, Subtype.ext_iff]
  simpa using Fintype.card_le_of_injective f hf

theorem sqrt_nuisanceCoord_card_le_ceiling :
    Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤
      nuisanceDimensionCeiling Head := by
  unfold nuisanceDimensionCeiling
  apply Real.sqrt_le_sqrt
  exact_mod_cast B.nuisanceCoord_card_le_head_add_one

theorem nuisanceStatisticCoefficient_le_ceiling
    {U : ℝ} (hU : 1 ≤ U) :
    B.nuisanceStatisticCoefficient U ≤
      nuisanceStatisticCoefficientCeiling Head U := by
  unfold nuisanceStatisticCoefficient nuisanceStatisticCoefficientCeiling
  have hmax : 0 ≤ max (PaperStatisticNorm.physicalLogCoefficient U)
      (3 / Real.log 2) := by
    exact (PaperStatisticNorm.physicalLogCoefficient_nonneg hU).trans
      (le_max_left _ _)
  exact mul_le_mul_of_nonneg_right
    B.sqrt_nuisanceCoord_card_le_ceiling hmax

theorem nuisanceGeometryConstant_le_ceiling (sep R : ℝ) :
    B.nuisanceGeometryConstant sep R ≤
      nuisanceGeometryCeiling Head sep R := by
  unfold nuisanceGeometryConstant nuisanceGeometryCeiling
  have hcard : (Fintype.card B.HeadIndex : ℝ) ≤
      (Fintype.card Head : ℝ) := by
    exact_mod_cast Fintype.card_le_of_injective
      (fun h : B.HeadIndex ↦ h.1) (fun _ _ h ↦ Subtype.ext h)
  have hfactor : 0 ≤ 8 * R ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hcard hfactor]

omit [DecidableEq Head] in
theorem canonicalEffectiveNuisanceGammaFloor_pos
    (I : PhysicalIntervals) {U a marginFloor : ℝ} {W : ℕ}
    (hmargin : 0 < marginFloor) :
    0 < canonicalEffectiveNuisanceGammaFloor Head I U a W marginFloor := by
  unfold canonicalEffectiveNuisanceGammaFloor
  have hsep := fixedInterval_separation_pos I
  have hgeom : 0 < nuisanceGeometryCeiling Head
      (Real.log (I.lower .plus) - Real.log (I.upper .minus))
      (Real.log U) := by
    unfold nuisanceGeometryCeiling
    positivity
  exact mul_pos (Real.exp_pos _)
    (div_pos (mul_pos (sq_pos_of_pos hmargin) (sq_pos_of_pos hsep))
      (mul_pos (by norm_num) hgeom))

/-- Every target with the prescribed cell-mass floor has a canonical
nuisance gap bounded below by the preceding root scalar. -/
theorem canonicalEffectiveNuisanceGammaFloor_le
    [Nonempty Head]
    (I : PhysicalIntervals) {U a marginFloor : ℝ}
    (hU : 1 ≤ U) (ha : 0 ≤ a) (hmargin : 0 < marginFloor)
    (T : BarycentricTarget B.sampleData)
    (hTmargin : marginFloor ≤ T.cellMassMargin) :
    canonicalEffectiveNuisanceGammaFloor Head I U a B.sampleData.W
        marginFloor ≤
      B.canonicalEffectiveNuisanceGamma I U a T := by
  let sep : ℝ := Real.log (I.lower .plus) - Real.log (I.upper .minus)
  let R : ℝ := Real.log U
  let Kactual : ℝ :=
    PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
      B.nuisanceStatisticCoefficient U
  let Kceiling : ℝ :=
    PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
      nuisanceStatisticCoefficientCeiling Head U
  have hK : Kactual ≤ Kceiling := by
    dsimp only [Kactual, Kceiling]
    linarith [B.nuisanceStatisticCoefficient_le_ceiling hU]
  have hKa : Kactual * a ≤ Kceiling * a :=
    mul_le_mul_of_nonneg_right hK ha
  have hexp : Real.exp (-2 * (Kceiling * a)) ≤
      Real.exp (-2 * (Kactual * a)) := by
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hsep : 0 < sep := fixedInterval_separation_pos I
  have hTpos : 0 < T.cellMassMargin := T.cellMassMargin_pos
  have hmarginSq : marginFloor ^ 2 ≤ T.cellMassMargin ^ 2 :=
    (sq_le_sq₀ hmargin.le hTpos.le).2 hTmargin
  have hnum : marginFloor ^ 2 * sep ^ 2 ≤
      T.cellMassMargin ^ 2 * sep ^ 2 :=
    mul_le_mul_of_nonneg_right hmarginSq (sq_nonneg sep)
  have hgeomActual : 0 < B.nuisanceGeometryConstant sep R :=
    B.nuisanceGeometryConstant_pos sep R
  have hgeomCeiling : 0 < nuisanceGeometryCeiling Head sep R := by
    unfold nuisanceGeometryCeiling
    positivity
  have hgeomLe : B.nuisanceGeometryConstant sep R ≤
      nuisanceGeometryCeiling Head sep R :=
    B.nuisanceGeometryConstant_le_ceiling sep R
  have hgap :
      marginFloor ^ 2 * sep ^ 2 /
          (2 * nuisanceGeometryCeiling Head sep R) ≤
        B.uniformNuisanceGap T.cellMassMargin sep R := by
    unfold uniformNuisanceGap
    exact div_le_div₀
      (mul_nonneg (sq_nonneg T.cellMassMargin) (sq_nonneg sep)) hnum
      (mul_pos (by norm_num) hgeomActual)
      (mul_le_mul_of_nonneg_left hgeomLe (by norm_num))
  have hexp0 : 0 ≤ Real.exp (-2 * (Kceiling * a)) :=
    (Real.exp_pos _).le
  have hgap0 : 0 ≤ B.uniformNuisanceGap T.cellMassMargin sep R := by
    unfold uniformNuisanceGap
    positivity
  have hfloorGap0 : 0 ≤
      marginFloor ^ 2 * sep ^ 2 /
        (2 * nuisanceGeometryCeiling Head sep R) := by positivity
  unfold canonicalEffectiveNuisanceGammaFloor canonicalEffectiveNuisanceGamma
  dsimp only [sep, R, Kactual, Kceiling] at hexp hgap ⊢
  exact mul_le_mul hexp hgap hfloorGap0 (Real.exp_pos _).le

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalBandSchurInverseFromFull -/
section


/-!
# Uniform raw band-Schur inverse from a full projected inverse

This file is the exact finite connector between the moving-low-cell output
of Lemma 8.4 and the raw-gauge interface used by the two-stage solve.  A
family of literal full projected inverses and one coordinatewise reciprocal
nuisance row are converted, uniformly on the preselected effective ball,
into linear equivalences whose maps are the actual finite band Schur maps.

No continuum limit, eventual estimate, or smallness assertion is hidden:
the Neumann smallness inequality and every constant occur in the statement.
-/

open Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperGuardCensus
open PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Ball-uniform attachment of the literal nuisance Schur correction to a
given family of full projected inverses. -/
theorem exists_uniform_actualBandSchurEquiv_of_full_of_marked_on_closedBall
    [Nonempty Head] [Nonempty Band]
    (I : PhysicalIntervals) {U : ℝ}
    (hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      ArithmeticModel.physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      ArithmeticModel.physicalBound (I.upper sigma) B.sampleData.n)
    (T : BarycentricTarget B.sampleData)
    (hbaseline : B.baseline = T.baseline)
    (hW : 1 < B.sampleData.W)
    (a : NNReal)
    (fullEquiv : ∀ (z : B.EffectiveParamSpace),
      z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
        SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
          SharpGaugeSpace B.partition.mass B.partition.center)
    (hfull : ∀ (z : B.EffectiveParamSpace)
        (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) q,
      fullEquiv z hz q =
        B.actualFullProjectedCLM (B.effectiveParamEquiv z) q)
    {Cfull Cmarked amin : ℝ}
    (hCfull : 0 ≤ Cfull) (hCmarked : 0 ≤ Cmarked)
    (hamin : 0 < amin)
    (hcenter : ∀ i : Band, amin ≤ B.bandCenter i)
    (hinvFull : ∀ (z : B.EffectiveParamSpace)
        (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) v,
      ‖(fullEquiv z hz).symm v‖ ≤ Cfull * ‖v‖)
    (hsmall : Cfull *
      (2 * B.nuisanceMarkedSchurRate Cmarked
        (B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T)
        amin) < 1)
    (hmarked : ∀ (z : B.EffectiveParamSpace)
        (_hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
        (c : NuisanceCoord B.HeadIndex)
        (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw (B.effectiveParamEquiv z)).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ))) :
    ∃ e : ∀ (z : B.EffectiveParamSpace),
        z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
          B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge,
      (∀ (z : B.EffectiveParamSpace)
          (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) q,
        e z hz q =
          B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
            (B.canonicalEffectiveNuisanceGamma_pos
              I U (3 * (a : ℝ)) T)
            (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
              hlowerOne hupperU hlo hhi T hbaseline hW z hz) q) ∧
      ∀ (z : B.EffectiveParamSpace)
          (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) v,
        paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) ((e z hz).symm v) ≤
          (Cfull / (1 - Cfull *
            (2 * B.nuisanceMarkedSchurRate Cmarked
              (B.canonicalEffectiveNuisanceGamma
                I U (3 * (a : ℝ)) T) amin))) *
            paperSharpNorm B.harmonicMass B.bandCenter
              (B.partition.center_ne_zero B.n_gt_one) v := by
  let gamma :=
    B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
  have hgamma : 0 < gamma := by
    exact B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
  have hgap : ∀ z
      (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) v,
      gamma * ‖v‖ ^ 2 ≤
        inner ℝ v
          (B.nuisanceCovarianceOperator (B.effectiveParamEquiv z) v) := by
    intro z hz v
    exact B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
      hlowerOne hupperU hlo hhi T hbaseline hW z hz v
  have hexists : ∀ z
      (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
      ∃ rawEquiv : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge,
        (∀ b, rawEquiv b =
          B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
            hgamma (hgap z hz) b) ∧
        ∀ u,
          paperSharpNorm B.harmonicMass B.bandCenter
              (B.partition.center_ne_zero B.n_gt_one)
              (rawEquiv.symm u) ≤
            (Cfull / (1 - Cfull *
              (2 * B.nuisanceMarkedSchurRate Cmarked gamma amin))) *
              paperSharpNorm B.harmonicMass B.bandCenter
                (B.partition.center_ne_zero B.n_gt_one) u := by
    intro z hz
    exact B.exists_actualBandSchurEquiv_of_full_of_marked
      (B.effectiveParamEquiv z) (fullEquiv z hz) (hfull z hz)
      hgamma (hgap z hz) hCfull hCmarked hamin hcenter
      (hinvFull z hz) (by simpa only [gamma] using hsmall)
      (hmarked z hz)
  choose e he hinv using hexists
  refine ⟨e, ?_, ?_⟩
  · intro z hz q
    simpa only [gamma] using he z hz q
  · intro z hz v
    simpa only [gamma] using hinv z hz v

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperSelectedMeshSchurRateEventually -/
section


/-!
# Vanishing nuisance-Schur rate at the moving-low scale

This file isolates the rate calculation needed after the selected-mesh
full-band inverse.  A reciprocal nuisance row of size `epsilon n / p`,
with both `epsilon n -> 0` and `epsilon n * log (log n) -> 0`, survives the
moving-low loss `amin = c / log (log n)`: the resulting Schur perturbation
still tends to zero.  All dimension, moment, and nuisance-gap constants are
explicit.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

open ArithmeticBandGeometry PaperWeightedInverseExport MovingLowGaugeTransfer

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

/-- The normalized first band moment is literally the prime sum
`sum t_p / p`; this removes a separate moment hypothesis from the eventual
Schur estimate. -/
theorem sum_harmonicMass_mul_bandCenter_eq_bandTReciprocalSum
    (B : BridgeData Head Band) :
    (∑ j : Band, B.harmonicMass j * B.bandCenter j) =
      PrimeSums.bandTReciprocalSum B.sampleData.n B.sampleData.W := by
  unfold harmonicMass bandCenter ArithmeticBandGeometry.Partition.center
    Erdos390.Lemma84.WeightedBandData.center
  have hmass : ∀ j : Band, B.partition.data.mass j ≠ 0 :=
    fun j ↦ ne_of_gt (B.partition.data.mass_pos j)
  simp_rw [mul_div_cancel₀ _ (hmass _)]
  change (∑ j : Band, ∑ p ∈ B.partition.data.fiber j,
      (1 / (p.1 : ℝ)) * ArithmeticModel.tPrime B.sampleData.n p.1) = _
  unfold Erdos390.Lemma84.WeightedBandData.fiber
  rw [Finset.sum_fiberwise Finset.univ B.partition.data.band
    (fun p : BandPrime B.sampleData.n B.sampleData.W ↦
      (1 / (p.1 : ℝ)) * ArithmeticModel.tPrime B.sampleData.n p.1)]
  unfold PrimeSums.bandTReciprocalSum
  calc
    (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        (1 / (p.1 : ℝ)) * ArithmeticModel.tPrime B.sampleData.n p.1) =
        ∑ p ∈ ArithmeticModel.primeBand B.sampleData.n B.sampleData.W,
          (1 / (p : ℝ)) * ArithmeticModel.tPrime B.sampleData.n p := by
      simpa only [Finset.univ_eq_attach] using
        (Finset.sum_attach
          (ArithmeticModel.primeBand B.sampleData.n B.sampleData.W)
          (fun p ↦ (1 / (p : ℝ)) *
            ArithmeticModel.tPrime B.sampleData.n p))
    _ = ∑ p ∈ ArithmeticModel.primeBand B.sampleData.n B.sampleData.W,
          ArithmeticModel.tPrime B.sampleData.n p / (p : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      ring



/-- A nonnegative row rate whose product with `log (log n)` tends to zero
already tends to zero.  This small lemma lets the analytic marked-row API
expose only its genuinely sharp rate. -/
theorem tendsto_zero_of_nonneg_mul_logL_zero
    (epsilon : ℕ → ℝ)
    (hepsilonNonneg : ∀ n, 0 ≤ epsilon n)
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
        atTop (nhds 0)) :
    Tendsto epsilon atTop (nhds 0) := by
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogOne : ∀ᶠ n : ℕ in atTop,
      1 ≤ Real.log (Scale.L n) :=
    (Real.tendsto_log_atTop.comp hLTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  have hlower : ∀ᶠ n : ℕ in atTop, 0 ≤ epsilon n :=
    Filter.Eventually.of_forall hepsilonNonneg
  have hupper : ∀ᶠ n : ℕ in atTop,
      epsilon n ≤ epsilon n * Real.log (Scale.L n) := by
    filter_upwards [hlogOne] with n hn
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hn (hepsilonNonneg n)
  exact squeeze_zero' hlower hupper hepsilonRate

/-- The moving-low loss is harmless at the sharp marked-row rate. -/
theorem tendsto_selectedMeshSchurRateMajorant_zero
    (epsilon : ℕ → ℝ) {droot momentBound gammaFloor centerScale : ℝ}
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
        atTop (nhds 0))
    (hgamma : 0 < gammaFloor) (hcenter : 0 < centerScale) :
    Tendsto
      (selectedMeshSchurRateMajorant epsilon droot momentBound
        gammaFloor centerScale) atTop (nhds 0) := by
  have hproduct : Tendsto (fun n : ℕ ↦
      (epsilon n * Real.log (Scale.L n)) * epsilon n)
      atTop (nhds 0) := by
    simpa only [zero_mul] using hepsilonRate.mul hepsilon
  let C : ℝ := droot ^ 2 * momentBound / (gammaFloor * centerScale)
  have hscaled : Tendsto (fun n : ℕ ↦
      C * ((epsilon n * Real.log (Scale.L n)) * epsilon n))
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hproduct
  apply hscaled.congr'
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogTop : Tendsto (fun n : ℕ ↦ Real.log (Scale.L n))
      atTop atTop := Real.tendsto_log_atTop.comp hLTop
  filter_upwards [hlogTop.eventually (eventually_gt_atTop (0 : ℝ))]
      with n hlog
  unfold selectedMeshSchurRateMajorant
  dsimp only [C]
  field_simp [hgamma.ne', hcenter.ne', hlog.ne']

/-- Reserving half of the Neumann denominator leaves the structural factor
two and removes every moving-low or mesh parameter from the retained inverse
constant. -/
theorem schurInverseConstant_le_two_mul
    {C rate : ℝ} (hC : 0 < C)
    (hhalf : C * (2 * rate) ≤ 1 / 2) :
    C / (1 - C * (2 * rate)) ≤ 2 * C := by
  have hdenHalf : 1 / 2 ≤ 1 - C * (2 * rate) := by linarith
  calc
    C / (1 - C * (2 * rate)) ≤ C / (1 / 2) :=
      div_le_div_of_nonneg_left hC.le (by norm_num) hdenHalf
    _ = 2 * C := by ring

/-- Literal comparison between the finite nuisance-Schur rate and the
preceding scalar majorant. -/
theorem nuisanceMarkedSchurRate_le_selectedMeshSchurRateMajorant
    (B : BridgeData Head Band)
    {epsilon droot momentBound gammaFloor gamma centerScale : ℝ}
    {n : ℕ}
    (hepsilon : 0 ≤ epsilon) (hdroot : 0 ≤ droot)
    (hmomentBound : 0 ≤ momentBound)
    (hgammaFloor : 0 < gammaFloor) (hgamma : gammaFloor ≤ gamma)
    (hcenterScale : 0 < centerScale)
    (hlog : 0 < Real.log (Scale.L n))
    (hdimension : Real.sqrt
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤ droot)
    (hmoment : (∑ j : Band,
      B.harmonicMass j * B.bandCenter j) ≤ momentBound) :
    B.nuisanceMarkedSchurRate epsilon gamma
        (centerScale / Real.log (Scale.L n)) ≤
      selectedMeshSchurRateMajorant (fun _ ↦ epsilon) droot
        momentBound gammaFloor centerScale n := by
  have hgammaPos : 0 < gamma := hgammaFloor.trans_le hgamma
  have hcenterPos : 0 < centerScale / Real.log (Scale.L n) :=
    div_pos hcenterScale hlog
  have hdim0 : 0 ≤ Real.sqrt
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) := Real.sqrt_nonneg _
  have hmoment0 : 0 ≤ ∑ j : Band,
      B.harmonicMass j * B.bandCenter j := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (B.harmonicMass_pos j).le (B.bandCenter_pos j).le
  unfold nuisanceMarkedSchurRate selectedMeshSchurRateMajorant
  dsimp only
  gcongr

/-- Finite ball-uniform Schur inverse together with its literal arithmetic
quadratic-form gap.  The nuisance gap is constructed from the canonical
baseline; the quadratic gap is derived from the inverse and covariance
Cauchy--Schwarz, not assumed. -/
theorem exists_uniform_actualBandSchurEquiv_and_quadratic_of_full_of_marked
    (B : BridgeData Head Band) [Nonempty Head] [Nonempty Band]
    (I : PaperGuardCensus.PhysicalIntervals) {U : ℝ}
    (hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      ArithmeticModel.physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      ArithmeticModel.physicalBound (I.upper sigma) B.sampleData.n)
    (T : PaperGuardCensus.BarycentricTarget B.sampleData)
    (hbaseline : B.baseline = T.baseline)
    (hW : 1 < B.sampleData.W)
    (a : NNReal)
    (fullEquiv : ∀ (z : B.EffectiveParamSpace),
      z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
        SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
          SharpGaugeSpace B.partition.mass B.partition.center)
    (hfull : ∀ (z : B.EffectiveParamSpace)
        (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) q,
      fullEquiv z hz q =
        B.actualFullProjectedCLM (B.effectiveParamEquiv z) q)
    {Cfull Cmarked amin : ℝ}
    (hCfull : 0 < Cfull) (hCmarked : 0 ≤ Cmarked)
    (hamin : 0 < amin)
    (hcenter : ∀ i : Band, amin ≤ B.bandCenter i)
    (hinvFull : ∀ (z : B.EffectiveParamSpace)
        (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) v,
      ‖(fullEquiv z hz).symm v‖ ≤ Cfull * ‖v‖)
    (hsmall : Cfull *
      (2 * B.nuisanceMarkedSchurRate Cmarked
        (B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T)
        amin) < 1)
    (hmarked : ∀ (z : B.EffectiveParamSpace)
        (_hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
        (c : NuisanceCoord B.HeadIndex)
        (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw (B.effectiveParamEquiv z)).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ))) :
    let gamma :=
      B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
    let Cschur := Cfull / (1 - Cfull *
      (2 * B.nuisanceMarkedSchurRate Cmarked gamma amin))
    ∃ e : ∀ (z : B.EffectiveParamSpace),
        z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
          B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge,
      (∀ (z : B.EffectiveParamSpace)
          (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) q,
        e z hz q =
          B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
            (B.canonicalEffectiveNuisanceGamma_pos
              I U (3 * (a : ℝ)) T)
            (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
              hlowerOne hupperU hlo hhi T hbaseline hW z hz) q) ∧
      (∀ (z : B.EffectiveParamSpace)
          (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) v,
        paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) ((e z hz).symm v) ≤
          Cschur * paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) v) ∧
      ∀ (z : B.EffectiveParamSpace)
          (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
          (q : B.RawBandGauge),
        (rawDLowerWeight B.harmonicMass B.bandCenter ^ 2 /
            (sharpWeightTotal B.harmonicMass B.bandCenter * Cschur)) *
            paperSharpNorm B.harmonicMass B.bandCenter
              (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
          (B.tiltedLaw (B.effectiveParamEquiv z)).covariance
            (B.nuisanceResidualScore (B.effectiveParamEquiv z)
              (B.canonicalEffectiveNuisanceGamma_pos
                I U (3 * (a : ℝ)) T)
              (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                hlowerOne hupperU hlo hhi T hbaseline hW z hz)
              (B.bandRegressionScore q))
            (B.nuisanceResidualScore (B.effectiveParamEquiv z)
              (B.canonicalEffectiveNuisanceGamma_pos
                I U (3 * (a : ℝ)) T)
              (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                hlowerOne hupperU hlo hhi T hbaseline hW z hz)
              (B.bandRegressionScore q)) := by
  let gamma :=
    B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
  let Cschur := Cfull / (1 - Cfull *
    (2 * B.nuisanceMarkedSchurRate Cmarked gamma amin))
  obtain ⟨e, he, hinv⟩ :=
    B.exists_uniform_actualBandSchurEquiv_of_full_of_marked_on_closedBall
      I hU hlowerOne hupperU hlo hhi T hbaseline hW a
      fullEquiv hfull hCfull.le hCmarked hamin hcenter hinvFull
      (by simpa only [gamma] using hsmall) hmarked
  have hden : 0 < 1 - Cfull *
      (2 * B.nuisanceMarkedSchurRate Cmarked gamma amin) :=
    sub_pos.mpr (by simpa only [gamma] using hsmall)
  have hCschur : 0 < Cschur := by
    dsimp only [Cschur]
    exact div_pos hCfull hden
  refine ⟨e, he, ?_, ?_⟩
  · intro z hz v
    simpa only [gamma, Cschur] using hinv z hz v
  · intro z hz q
    exact B.actualBandSchur_quadratic_lower_of_inverse_arithmetic
      (B.effectiveParamEquiv z)
      (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
      (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
        hlowerOne hupperU hlo hhi T hbaseline hW z hz)
      (e z hz) (he z hz) hCschur
      (by
        intro v
        simpa only [gamma, Cschur] using hinv z hz v)
      q

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperSelectedMeshSchurEventually -/
section


/-!
# Eventual nuisance--Schur closure on a selected arithmetic mesh

This file combines the exact finite Schur connector with the moving-low
rate calculation.  The statement retains only the two analytic inputs that
are genuinely specific to the selected mesh: a lower envelope for every
arithmetic band center and the sharp `epsilon n / p` marked nuisance rows.
The band first moment, nuisance dimension, and positive nuisance floor are
derived internally from the canonical arithmetic objects.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

open ArithmeticModel ArithmeticBandGeometry PaperWeightedInverseExport
  MovingLowGaugeTransfer

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

/-- Once the actual-full inverse, sharp marked rows, moving-low center
envelope, and a fixed positive barycentric mass floor are available, the
literal arithmetic nuisance Schur complement is eventually invertible on
the whole effective ball.  Its retained inverse constant is at most
`2 * Cfull`; in particular it is independent of the moving low cell and of
the arithmetic mesh.

No continuum convergence or covariance estimate is assumed in this
connector.  Those analytic inputs enter only through `fullEquiv`, `hcenter`,
and `hmarked` in the displayed finite arithmetic statement. -/
theorem eventually_exists_uniform_actualBandSchurEquiv_and_quadratic
    [Nonempty Head] [Nonempty Band]
    (I : PaperGuardCensus.PhysicalIntervals) {U : ℝ}
    (hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (W : ℕ) (hW : 1 < W)
    (a : NNReal)
    (marginFloor centerScale Cfull : ℝ)
    (hmarginFloor : 0 < marginFloor)
    (hcenterScale : 0 < centerScale)
    (hCfull : 0 < Cfull)
    (epsilon : ℕ → ℝ)
    (hepsilonNonneg : ∀ n, 0 ≤ epsilon n)
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
        atTop (nhds 0)) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (B : BridgeData Head Band)
        (hBn : B.sampleData.n = n)
        (hBW : B.sampleData.W = W)
        (T : PaperGuardCensus.BarycentricTarget B.sampleData)
        (hTmargin : marginFloor ≤ T.cellMassMargin)
        (hbaseline : B.baseline = T.baseline)
        (hlo : ∀ sigma, B.sampleData.lo sigma =
          ArithmeticModel.physicalBound (I.lower sigma) B.sampleData.n)
        (hhi : ∀ sigma, B.sampleData.hi sigma =
          ArithmeticModel.physicalBound (I.upper sigma) B.sampleData.n),
      ∀ (fullEquiv : ∀ (z : B.EffectiveParamSpace),
          z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
            SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
              SharpGaugeSpace B.partition.mass B.partition.center),
        (∀ (z : B.EffectiveParamSpace)
            (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) q,
          fullEquiv z hz q =
            B.actualFullProjectedCLM (B.effectiveParamEquiv z) q) →
        (∀ (z : B.EffectiveParamSpace)
            (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) v,
          ‖(fullEquiv z hz).symm v‖ ≤ Cfull * ‖v‖) →
        (∀ i : Band,
          centerScale / Real.log (Scale.L B.sampleData.n) ≤
            B.bandCenter i) →
        (∀ (z : B.EffectiveParamSpace)
            (_hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
            (c : NuisanceCoord B.HeadIndex)
            (p : BandPrime B.sampleData.n B.sampleData.W),
          |(B.tiltedLaw (B.effectiveParamEquiv z)).covariance
            (fun m ↦ B.nuisanceStatistic m c)
            (fun m ↦ ArithmeticModel.valuation p.1
              (B.sampleData.value m))| ≤
            epsilon B.sampleData.n * (1 / (p.1 : ℝ))) →
      let gamma :=
        B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
      let rate := B.nuisanceMarkedSchurRate
        (epsilon B.sampleData.n) gamma
          (centerScale / Real.log (Scale.L B.sampleData.n))
      let Cschur := Cfull / (1 - Cfull * (2 * rate))
      ∃ e : ∀ (z : B.EffectiveParamSpace),
          z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
            B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge,
        (∀ (z : B.EffectiveParamSpace)
            (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) q,
          e z hz q =
            B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
              (B.canonicalEffectiveNuisanceGamma_pos
                I U (3 * (a : ℝ)) T)
              (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                hlowerOne hupperU hlo hhi T hbaseline (by omega) z hz) q) ∧
        (∀ (z : B.EffectiveParamSpace)
            (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) v,
          paperSharpNorm B.harmonicMass B.bandCenter
              (B.partition.center_ne_zero B.n_gt_one) ((e z hz).symm v) ≤
            Cschur * paperSharpNorm B.harmonicMass B.bandCenter
              (B.partition.center_ne_zero B.n_gt_one) v) ∧
        Cschur ≤ 2 * Cfull ∧
        ∀ (z : B.EffectiveParamSpace)
            (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
            (q : B.RawBandGauge),
          (rawDLowerWeight B.harmonicMass B.bandCenter ^ 2 /
              (sharpWeightTotal B.harmonicMass B.bandCenter * Cschur)) *
              paperSharpNorm B.harmonicMass B.bandCenter
                (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
            (B.tiltedLaw (B.effectiveParamEquiv z)).covariance
              (B.nuisanceResidualScore (B.effectiveParamEquiv z)
                (B.canonicalEffectiveNuisanceGamma_pos
                  I U (3 * (a : ℝ)) T)
                (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                  hlowerOne hupperU hlo hhi T hbaseline (by omega) z hz)
                (B.bandRegressionScore q))
              (B.nuisanceResidualScore (B.effectiveParamEquiv z)
                (B.canonicalEffectiveNuisanceGamma_pos
                  I U (3 * (a : ℝ)) T)
                (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                  hlowerOne hupperU hlo hhi T hbaseline (by omega) z hz)
                (B.bandRegressionScore q)) := by
  let droot : ℝ := nuisanceDimensionCeiling Head
  let momentBound : ℝ := 2 * Real.log 4
  let gammaFloor : ℝ := canonicalEffectiveNuisanceGammaFloor
    Head I U (3 * (a : ℝ)) W marginFloor
  have hdroot : 0 ≤ droot := by
    dsimp only [droot, nuisanceDimensionCeiling]
    positivity
  have hmomentBound : 0 ≤ momentBound := by
    dsimp only [momentBound]
    positivity
  have hgammaFloor : 0 < gammaFloor := by
    dsimp only [gammaFloor]
    exact canonicalEffectiveNuisanceGammaFloor_pos
      (Head := Head) I hmarginFloor
  have hepsilon : Tendsto epsilon atTop (nhds 0) :=
    tendsto_zero_of_nonneg_mul_logL_zero epsilon
      hepsilonNonneg hepsilonRate
  have hmajorT : Tendsto
      (selectedMeshSchurRateMajorant epsilon droot momentBound
        gammaFloor centerScale) atTop (nhds 0) :=
    tendsto_selectedMeshSchurRateMajorant_zero epsilon
      hepsilon hepsilonRate hgammaFloor hcenterScale
  have hscaledT : Tendsto (fun n : ℕ ↦
      Cfull * (2 * selectedMeshSchurRateMajorant epsilon droot
        momentBound gammaFloor centerScale n)) atTop (nhds 0) := by
    simpa only [mul_zero] using
      tendsto_const_nhds.mul (tendsto_const_nhds.mul hmajorT)
  have hsmallEvent : ∀ᶠ n : ℕ in atTop,
      Cfull * (2 * selectedMeshSchurRateMajorant epsilon droot
        momentBound gammaFloor centerScale n) < 1 / 2 :=
    hscaledT.eventually (eventually_lt_nhds (by norm_num))
  have hbandTEvent := PrimeSums.eventually_bandTReciprocalSum_le W
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogEvent : ∀ᶠ n : ℕ in atTop,
      0 < Real.log (Scale.L n) :=
    (Real.tendsto_log_atTop.comp hLTop).eventually
      (eventually_gt_atTop (0 : ℝ))
  filter_upwards [hsmallEvent, hbandTEvent, hlogEvent] with n hsmallMajor
      hbandT hlog
  intro B hBn hBW T hTmargin hbaseline hlo hhi fullEquiv hfull hinvFull
    hcenter hmarked
  subst n
  let gamma :=
    B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
  let rate := B.nuisanceMarkedSchurRate
    (epsilon B.sampleData.n) gamma
      (centerScale / Real.log (Scale.L B.sampleData.n))
  let Cschur := Cfull / (1 - Cfull * (2 * rate))
  have hdimension : Real.sqrt
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤ droot := by
    simpa only [droot] using B.sqrt_nuisanceCoord_card_le_ceiling
  have hmoment : (∑ j : Band,
      B.harmonicMass j * B.bandCenter j) ≤ momentBound := by
    rw [B.sum_harmonicMass_mul_bandCenter_eq_bandTReciprocalSum]
    rw [hBW]
    simpa only [momentBound] using hbandT
  have hgamma : gammaFloor ≤ gamma := by
    have h := B.canonicalEffectiveNuisanceGammaFloor_le I hU
      (by positivity : 0 ≤ 3 * (a : ℝ)) hmarginFloor T hTmargin
    rw [hBW] at h
    simpa only [gammaFloor, gamma] using h
  have hrateLe : rate ≤
      selectedMeshSchurRateMajorant epsilon droot momentBound
        gammaFloor centerScale B.sampleData.n := by
    dsimp only [rate]
    exact B.nuisanceMarkedSchurRate_le_selectedMeshSchurRateMajorant
      (hepsilonNonneg B.sampleData.n) hdroot hmomentBound hgammaFloor
      (by simpa only [gamma] using hgamma) hcenterScale hlog hdimension hmoment
  have hsmallHalf : Cfull * (2 * rate) < 1 / 2 := by
    have hmul : (2 * Cfull) * rate ≤
        (2 * Cfull) *
          selectedMeshSchurRateMajorant epsilon droot momentBound
            gammaFloor centerScale B.sampleData.n :=
      mul_le_mul_of_nonneg_left hrateLe (by positivity)
    nlinarith
  have hsmall : Cfull * (2 * rate) < 1 := by linarith
  obtain ⟨e, he, hinv, hquadratic⟩ :=
    B.exists_uniform_actualBandSchurEquiv_and_quadratic_of_full_of_marked
      I hU hlowerOne hupperU hlo hhi T hbaseline (by omega) a
      fullEquiv hfull hCfull (hepsilonNonneg B.sampleData.n)
      (div_pos hcenterScale hlog) hcenter hinvFull
      (by simpa only [gamma, rate] using hsmall) hmarked
  have hCschur : Cschur ≤ 2 * Cfull := by
    dsimp only [Cschur]
    exact schurInverseConstant_le_two_mul hCfull hsmallHalf.le
  refine ⟨e, ?_, ?_, hCschur, ?_⟩
  · simpa only [gamma, rate, Cschur] using he
  · simpa only [gamma, rate, Cschur] using hinv
  · simpa only [gamma, rate, Cschur] using hquadratic





end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band] [inst_4 : Nonempty.{u_1 + 1} Head]
  [inst_5 : Nonempty.{u_2 + 1} Band] (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) {U : Real}
  (hU : LE.le.{0} (1 : Real) U)
  (hlowerOne :
    ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
      LE.le.{0} (1 : Real) (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma))
  (hupperU :
    ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
      LE.le.{0} (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma) U)
  (W : Nat) (hW : LT.lt.{0} (1 : Nat) W) (a : NNReal) (marginFloor centerScale Cfull : Real),
  LT.lt.{0} (0 : Real) marginFloor →
    LT.lt.{0} (0 : Real) centerScale →
      LT.lt.{0} (0 : Real) Cfull →
        ∀ (epsilon : Nat → Real),
          (∀ (n : Nat), LE.le.{0} (0 : Real) (epsilon n)) →
            Filter.Tendsto.{0, 0}
                (fun (n : Nat) => HMul.hMul.{0, 0, 0} (epsilon n) (Real.log (Erdos390.Full.Scale.L n))) Filter.atTop.{0}
                (nhds.{0} (0 : Real)) →
              ∀ᶠ (n : Nat) in Filter.atTop.{0},
                ∀ (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band),
                  Eq.{1}
                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                      n →
                    ∀
                      (hBW :
                        Eq.{1}
                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                          W)
                      (T :
                        Erdos390.Full.PaperGuardCensus.BarycentricTarget.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
                      LE.le.{0} marginFloor (Erdos390.Full.PaperGuardCensus.BarycentricTarget.cellMassMargin.{u_1} T) →
                        ∀
                          (hbaseline :
                            Eq.{u_1 + 1} (Erdos390.Full.PaperBridgeFit.BridgeData.baseline.{u_1, u_2} B)
                              (Erdos390.Full.PaperGuardCensus.BarycentricTarget.baseline.{u_1} T))
                          (hlo :
                            ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                              Eq.{1}
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) sigma)
                                (Erdos390.Full.ArithmeticModel.physicalBound
                                  (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))))
                          (hhi :
                            ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                              Eq.{1}
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) sigma)
                                (Erdos390.Full.ArithmeticModel.physicalBound
                                  (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))))
                          (fullEquiv :
                            (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B)) →
                              Membership.mem.{u_1, u_1}
                                  (Metric.closedBall.{u_1}
                                    (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                    (↑a : Real))
                                  z →
                                ContinuousLinearEquiv.{0, 0, u_2, u_2} (RingHom.id.{0} Real)
                                  ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))
                                  ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))),
                          (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                              (hz :
                                Membership.mem.{u_1, u_1}
                                  (Metric.closedBall.{u_1}
                                    (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                    (↑a : Real))
                                  z)
                              (q :
                                ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))),
                              Eq.{u_2 + 1}
                                ((fullEquiv z hz :
                                    ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                          (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                          (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))) →
                                      ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                          (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                          (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))))
                                  q)
                                ((Erdos390.Full.PaperBridgeFit.BridgeData.actualFullProjectedCLM.{u_1, u_2} B
                                      ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, u_2} B :
                                          ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B) →
                                            Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
                                        z) :
                                    ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                          (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                          (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))) →
                                      ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                          (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                          (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))))
                                  q)) →
                            (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                (hz :
                                  Membership.mem.{u_1, u_1}
                                    (Metric.closedBall.{u_1}
                                      (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                      (↑a : Real))
                                    z)
                                (v :
                                  ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))),
                                LE.le.{0}
                                  (Norm.norm.{u_2}
                                    ((ContinuousLinearEquiv.symm.{0, 0, u_2, u_2} (fullEquiv z hz) :
                                        ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))) →
                                          ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))))
                                      v))
                                  (HMul.hMul.{0, 0, 0} Cfull (Norm.norm.{u_2} v))) →
                              (∀ (i : Band),
                                  LE.le.{0}
                                    (HDiv.hDiv.{0, 0, 0} centerScale
                                      (Real.log
                                        (Erdos390.Full.Scale.L
                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))))
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B i)) →
                                (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B)),
                                    Membership.mem.{u_1, u_1}
                                        (Metric.closedBall.{u_1}
                                          (0 :
                                            ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                          (↑a : Real))
                                        z →
                                      ∀
                                        (c :
                                          Erdos390.Full.PaperBridgeFit.NuisanceCoord.{u_1}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1, u_2} B))
                                        (p :
                                          Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                                        LE.le.{0}
                                          (abs.{0}
                                            (Erdos390.Full.FiniteProbability.covariance.{u_1}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.tiltedLaw.{u_1, u_2} B
                                                ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, u_2}
                                                      B :
                                                    ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                            u_2}
                                                          B) →
                                                      Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
                                                  z))
                                              (fun
                                                  (m :
                                                    Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                        B)) =>
                                                WithLp.ofLp.{u_1}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceStatistic.{u_1, u_2}
                                                    B m)
                                                  c)
                                              fun
                                                (m :
                                                  Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                      B)) =>
                                              Erdos390.Full.ArithmeticModel.valuation (↑p : Nat)
                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{u_1}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) m)))
                                          (HMul.hMul.{0, 0, 0}
                                            (epsilon
                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                            (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑(↑p : Nat) : Real)))) →
                                  let gamma :=
                                    Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma.{u_1, u_2} B
                                      I U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T;
                                  let rate :=
                                    Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceMarkedSchurRate.{u_1, u_2} B
                                      (epsilon
                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                      gamma
                                      (HDiv.hDiv.{0, 0, 0} centerScale
                                        (Real.log
                                          (Erdos390.Full.Scale.L
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))));
                                  let Cschur :=
                                    HDiv.hDiv.{0, 0, 0} Cfull
                                      (HSub.hSub.{0, 0, 0} (1 : Real)
                                        (HMul.hMul.{0, 0, 0} Cfull (HMul.hMul.{0, 0, 0} (2 : Real) rate)));
                                  ∃ (e :
                                    (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B)) →
                                      Membership.mem.{u_1, u_1}
                                          (Metric.closedBall.{u_1}
                                            (0 :
                                              ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2}
                                                  B))
                                            (↑a : Real))
                                          z →
                                        LinearEquiv.{0, 0, u_2, u_2} (RingHom.id.{0} Real)
                                          ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)
                                          ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)),
                                    And
                                      (∀
                                        (z :
                                          ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                        (hz :
                                          Membership.mem.{u_1, u_1}
                                            (Metric.closedBall.{u_1}
                                              (0 :
                                                ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2}
                                                    B))
                                              (↑a : Real))
                                            z)
                                        (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)),
                                        Eq.{u_2 + 1}
                                          ((e z hz :
                                              ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B) →
                                                ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B))
                                            q)
                                          ((Erdos390.Full.PaperBridgeFit.BridgeData.actualBandSchurLinearMap.{u_1, u_2}
                                                B
                                                ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, u_2}
                                                      B :
                                                    ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                            u_2}
                                                          B) →
                                                      Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
                                                  z)
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1,
                                                    u_2}
                                                  B I U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                    u_2}
                                                  B I a hU hlowerOne hupperU hlo hhi T hbaseline
                                                  (Decidable.byContradiction
                                                    fun
                                                      (a :
                                                        Not
                                                          (LT.lt.{0} (1 : Nat)
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                  u_2}
                                                                B)))) =>
                                                    Erdos390.Full.PaperBridgeFit.BridgeData.eventually_exists_uniform_actualBandSchurEquiv_and_quadratic._proof_1.{u_1,
                                                        u_2}
                                                      W hW n B hBW a)
                                                  z hz) :
                                              ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B) →
                                                ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B))
                                            q))
                                      (And
                                        (∀
                                          (z :
                                            ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                          (hz :
                                            Membership.mem.{u_1, u_1}
                                              (Metric.closedBall.{u_1}
                                                (0 :
                                                  ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                        u_2}
                                                      B))
                                                (↑a : Real))
                                              z)
                                          (v : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)),
                                          LE.le.{0}
                                            (Erdos390.Full.PaperWeightedInverseExport.paperSharpNorm.{u_2}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2} B)
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B)
                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.center_ne_zero.{u_2}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, u_2} B))
                                              ((LinearEquiv.symm.{0, 0, u_2, u_2} (e z hz) :
                                                  ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B) →
                                                    ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2}
                                                        B))
                                                v))
                                            (HMul.hMul.{0, 0, 0} Cschur
                                              (Erdos390.Full.PaperWeightedInverseExport.paperSharpNorm.{u_2}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2} B)
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B)
                                                (Erdos390.Full.ArithmeticBandGeometry.Partition.center_ne_zero.{u_2}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, u_2} B))
                                                v)))
                                        (And (LE.le.{0} Cschur (HMul.hMul.{0, 0, 0} (2 : Real) Cfull))
                                          (∀
                                            (z :
                                              ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2}
                                                  B))
                                            (hz :
                                              Membership.mem.{u_1, u_1}
                                                (Metric.closedBall.{u_1}
                                                  (0 :
                                                    ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                          u_2}
                                                        B))
                                                  (↑a : Real))
                                                z)
                                            (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)),
                                            LE.le.{0}
                                              (HMul.hMul.{0, 0, 0}
                                                (HDiv.hDiv.{0, 0, 0}
                                                  (HPow.hPow.{0, 0, 0}
                                                    (Erdos390.Full.PaperWeightedInverseExport.rawDLowerWeight.{u_2}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2}
                                                        B)
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B))
                                                    (2 : Nat))
                                                  (HMul.hMul.{0, 0, 0}
                                                    (Erdos390.Full.MovingLowGaugeTransfer.sharpWeightTotal.{u_2}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2}
                                                        B)
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B))
                                                    Cschur))
                                                (HPow.hPow.{0, 0, 0}
                                                  (Erdos390.Full.PaperWeightedInverseExport.paperSharpNorm.{u_2}
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2} B)
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B)
                                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.center_ne_zero.{u_2}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, u_2} B))
                                                    q)
                                                  (2 : Nat)))
                                              (Erdos390.Full.FiniteProbability.covariance.{u_1}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.tiltedLaw.{u_1, u_2} B
                                                  ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1,
                                                          u_2}
                                                        B :
                                                      ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                              u_2}
                                                            B) →
                                                        Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
                                                    z))
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceResidualScore.{u_1,
                                                    u_2}
                                                  B
                                                  ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1,
                                                          u_2}
                                                        B :
                                                      ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                              u_2}
                                                            B) →
                                                        Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
                                                    z)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1,
                                                      u_2}
                                                    B I U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                      u_2}
                                                    B I a hU hlowerOne hupperU hlo hhi T hbaseline
                                                    (Decidable.byContradiction
                                                      fun
                                                        (a :
                                                          Not
                                                            (LT.lt.{0} (1 : Nat)
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                    u_2}
                                                                  B)))) =>
                                                      Erdos390.Full.PaperBridgeFit.BridgeData.eventually_exists_uniform_actualBandSchurEquiv_and_quadratic._proof_1.{u_1,
                                                          u_2}
                                                        W hW n B hBW a)
                                                    z hz)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.bandRegressionScore.{u_1,
                                                      u_2}
                                                    B q))
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceResidualScore.{u_1,
                                                    u_2}
                                                  B
                                                  ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1,
                                                          u_2}
                                                        B :
                                                      ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                              u_2}
                                                            B) →
                                                        Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
                                                    z)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1,
                                                      u_2}
                                                    B I U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                      u_2}
                                                    B I a hU hlowerOne hupperU hlo hhi T hbaseline
                                                    (Decidable.byContradiction
                                                      fun
                                                        (a :
                                                          Not
                                                            (LT.lt.{0} (1 : Nat)
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                    u_2}
                                                                  B)))) =>
                                                      Erdos390.Full.PaperBridgeFit.BridgeData.eventually_exists_uniform_actualBandSchurEquiv_and_quadratic._proof_1.{u_1,
                                                          u_2}
                                                        W hW n B hBW a)
                                                    z hz)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.bandRegressionScore.{u_1,
                                                      u_2}
                                                    B q)))))) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.eventually_exists_uniform_actualBandSchurEquiv_and_quadratic
