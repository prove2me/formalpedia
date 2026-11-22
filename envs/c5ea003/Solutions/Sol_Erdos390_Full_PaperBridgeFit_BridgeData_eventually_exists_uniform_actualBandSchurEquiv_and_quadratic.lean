-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.eventually_exists_uniform_actualBandSchurEquiv_and_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T12:12:17.894619+00:00
-- url     : https://prove2.me/submissions/de69ba29-dc95-47af-a412-34bc856cb390

import Mathlib
import Definitions.Def_erdos390_analytic_statement_auxiliaries
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Definitions.Def_erdos390_analytic_foundations_001
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

set_option autoImplicit false

universe u_1 u_2

namespace C1d397

open Erdos390.Full

section Cov
variable {Ω : Type*} [Fintype Ω]

theorem cov_centered (μ : FiniteProbability Ω) (F G : Ω → ℝ) :
    μ.covariance F G = ∑ ω, μ.mass ω * (F ω - μ.expect F) * G ω := by
  unfold FiniteProbability.covariance FiniteProbability.expect
  have h1 : (∑ ω, μ.mass ω * (F ω - ∑ ω', μ.mass ω' * F ω') * G ω) =
      (∑ ω, μ.mass ω * (F ω * G ω)) - (∑ ω', μ.mass ω' * F ω') * ∑ ω, μ.mass ω * G ω := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  rw [h1]

theorem cov_centered2 (μ : FiniteProbability Ω) (F G : Ω → ℝ) :
    μ.covariance F G = ∑ ω, μ.mass ω * (F ω - μ.expect F) * (G ω - μ.expect G) := by
  rw [cov_centered]
  have h0 : (∑ ω, μ.mass ω * (F ω - μ.expect F)) = 0 := by
    unfold FiniteProbability.expect
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, μ.mass_sum, one_mul, sub_self]
  have : (∑ ω, μ.mass ω * (F ω - μ.expect F) * (G ω - μ.expect G)) =
      (∑ ω, μ.mass ω * (F ω - μ.expect F) * G ω) -
        (∑ ω, μ.mass ω * (F ω - μ.expect F)) * μ.expect G := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  rw [this, h0, zero_mul, sub_zero]

theorem cov_comm (μ : FiniteProbability Ω) (F G : Ω → ℝ) :
    μ.covariance F G = μ.covariance G F := by
  unfold FiniteProbability.covariance
  rw [mul_comm (μ.expect F)]
  congr 2
  funext ω
  ring

theorem cov_sum_right (μ : FiniteProbability Ω) {ι : Type*} (s : Finset ι)
    (F : Ω → ℝ) (c : ι → ℝ) (G : ι → Ω → ℝ) :
    μ.covariance F (fun ω => ∑ k ∈ s, c k * G k ω) =
      ∑ k ∈ s, c k * μ.covariance F (G k) := by
  rw [cov_centered]
  simp_rw [cov_centered μ F, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem cov_sum_left (μ : FiniteProbability Ω) {ι : Type*} (s : Finset ι)
    (F : Ω → ℝ) (c : ι → ℝ) (G : ι → Ω → ℝ) :
    μ.covariance (fun ω => ∑ k ∈ s, c k * G k ω) F =
      ∑ k ∈ s, c k * μ.covariance (G k) F := by
  rw [cov_comm, cov_sum_right]
  simp_rw [cov_comm μ F]

theorem cov_sub_right (μ : FiniteProbability Ω) (F G H : Ω → ℝ) :
    μ.covariance F (fun ω => G ω - H ω) = μ.covariance F G - μ.covariance F H := by
  simp only [cov_centered μ F, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem cov_sub_left (μ : FiniteProbability Ω) (F G H : Ω → ℝ) :
    μ.covariance (fun ω => G ω - H ω) F = μ.covariance G F - μ.covariance H F := by
  rw [cov_comm, cov_sub_right, cov_comm μ F, cov_comm μ F]

theorem cov_self_nonneg (μ : FiniteProbability Ω) (F : Ω → ℝ) :
    0 ≤ μ.covariance F F := by
  rw [cov_centered2]
  apply Finset.sum_nonneg
  intro ω _
  have := μ.mass_nonneg ω
  have h2 := mul_self_nonneg (F ω - μ.expect F)
  nlinarith

theorem cov_sq_le (μ : FiniteProbability Ω) (F G : Ω → ℝ) :
    μ.covariance F G ^ 2 ≤ μ.covariance F F * μ.covariance G G := by
  rw [cov_centered2, cov_centered2, cov_centered2]
  have key := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun ω => Real.sqrt (μ.mass ω) * (F ω - μ.expect F))
    (fun ω => Real.sqrt (μ.mass ω) * (G ω - μ.expect G))
  have hs : ∀ ω, Real.sqrt (μ.mass ω) * Real.sqrt (μ.mass ω) = μ.mass ω :=
    fun ω => Real.mul_self_sqrt (μ.mass_nonneg ω)
  have e1 : (∑ ω, Real.sqrt (μ.mass ω) * (F ω - μ.expect F) *
      (Real.sqrt (μ.mass ω) * (G ω - μ.expect G))) =
      ∑ ω, μ.mass ω * (F ω - μ.expect F) * (G ω - μ.expect G) := by
    apply Finset.sum_congr rfl; intro ω _
    linear_combination (F ω - μ.expect F) * (G ω - μ.expect G) * hs ω
  have e2 : (∑ ω, (Real.sqrt (μ.mass ω) * (F ω - μ.expect F)) ^ 2) =
      ∑ ω, μ.mass ω * (F ω - μ.expect F) * (F ω - μ.expect F) := by
    apply Finset.sum_congr rfl; intro ω _
    linear_combination (F ω - μ.expect F) * (F ω - μ.expect F) * hs ω
  have e3 : (∑ ω, (Real.sqrt (μ.mass ω) * (G ω - μ.expect G)) ^ 2) =
      ∑ ω, μ.mass ω * (G ω - μ.expect G) * (G ω - μ.expect G) := by
    apply Finset.sum_congr rfl; intro ω _
    linear_combination (G ω - μ.expect G) * (G ω - μ.expect G) * hs ω
  rw [e1, e2, e3] at key
  exact key

end Cov

section Jac
variable {Omega E : Type*} [Fintype Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem inner_jacobian_bilin (vf : VectorExponentialFamily Omega E) (xi x y : E) :
    inner ℝ y (vf.jacobian xi x) =
      (vf.baseMass / vf.scale) *
        (vf.scalarFamily.tiltedProbability xi).covariance
          (fun omega => inner ℝ y (vf.statistic omega))
          (fun omega => inner ℝ x (vf.statistic omega)) := by
  let F : Omega → ℝ := fun omega => inner ℝ y (vf.statistic omega)
  have hleft : HasFDerivAt
      (fun eta => inner ℝ y (vf.vectorMoment eta))
      (((innerSL ℝ) y).comp (vf.jacobian xi)) xi := by
    exact ((innerSL ℝ) y).hasFDerivAt.comp xi
      (vf.hasFDerivAt_vectorMoment xi)
  have hright : HasFDerivAt
      (vf.scalarFamily.moment F)
      ((vf.baseMass / vf.scale) •
        vf.scalarFamily.covarianceScore F xi) xi :=
    vf.scalarFamily.hasFDerivAt_moment_covariance F xi
  have hfun : (fun eta => inner ℝ y (vf.vectorMoment eta)) =
      vf.scalarFamily.moment F := by
    funext eta
    exact vf.inner_vectorMoment y eta
  have hmaps : ((innerSL ℝ) y).comp (vf.jacobian xi) =
      (vf.baseMass / vf.scale) •
        vf.scalarFamily.covarianceScore F xi := by
    exact hleft.unique (hfun ▸ hright)
  have happ := congrArg (fun T : E →L[ℝ] ℝ => T x) hmaps
  change inner ℝ y (vf.jacobian xi x) =
    (vf.baseMass / vf.scale) *
      vf.scalarFamily.covarianceScore F xi x at happ
  rw [vf.scalarFamily.covarianceScore_apply F xi x] at happ
  have hscore : (fun omega => vf.scalarFamily.score omega x) =
      (fun omega => inner ℝ x (vf.statistic omega)) := by
    funext omega
    simp only [VectorExponentialFamily.scalarFamily, innerSL_apply_apply]
    exact real_inner_comm _ _
  rw [hscore] at happ
  exact happ

end Jac

section Bridge
open PaperBridgeFit
variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

theorem gamma_bilin (B : BridgeData Head Band) [Nonempty Head]
    (xi : B.ParamSpace) (z1 z2 : B.NuisanceSpace) :
    inner ℝ z1 (B.nuisanceCovarianceOperator xi z2) =
      (B.tiltedLaw xi).covariance
        (fun m => inner ℝ z1 (B.nuisanceStatistic m))
        (fun m => inner ℝ z2 (B.nuisanceStatistic m)) := by
  have hinter : inner ℝ z1 (B.nuisanceCovarianceOperator xi z2) =
      inner ℝ (B.nuisanceEmbed z1)
        (B.covarianceOperator xi (B.nuisanceEmbed z2)) := by
    simpa only [BridgeData.nuisanceCovarianceOperator,
      ContinuousLinearMap.comp_apply] using
      (ContinuousLinearMap.adjoint_inner_right B.nuisanceEmbeddingCLM z1
        (B.covarianceOperator xi (B.nuisanceEmbeddingCLM z2)))
  rw [hinter, BridgeData.covarianceOperator, ContinuousLinearMap.smul_apply, inner_smul_right,
    inner_jacobian_bilin, B.vectorFamily_baseMass]
  have hL : B.L ≠ 0 := ne_of_gt B.L_pos
  have hq : B.q ≠ 0 := ne_of_gt B.q_pos
  have hsc : B.vectorFamily.scale = B.L := rfl
  rw [hsc]
  have hf : ∀ z : B.NuisanceSpace, (fun omega => inner ℝ (B.nuisanceEmbed z) (B.vectorFamily.statistic omega)) =
      (fun m => inner ℝ z (B.nuisanceStatistic m)) := by
    intro z
    funext m
    rw [show B.vectorFamily.statistic m = B.statistic m by rfl,
      B.statistic_eq_combine m,
      B.inner_nuisanceEmbed_combine z (B.nuisanceStatistic m) (B.mainStatistic m)]
  rw [hf z1, hf z2]
  change B.L / B.q * (B.q / B.L * (B.tiltedLaw xi).covariance _ _) = _
  field_simp


end Bridge

theorem cov_sum_right1 {Ω : Type*} [Fintype Ω] (μ : FiniteProbability Ω) {ι : Type*} (s : Finset ι)
    (F : Ω → ℝ) (G : ι → Ω → ℝ) :
    μ.covariance F (fun ω => ∑ k ∈ s, G k ω) = ∑ k ∈ s, μ.covariance F (G k) := by
  have h := cov_sum_right μ s F (fun _ => (1:ℝ)) G
  simp only [one_mul] at h
  exact h

theorem cov_sum_left1 {Ω : Type*} [Fintype Ω] (μ : FiniteProbability Ω) {ι : Type*} (s : Finset ι)
    (F : Ω → ℝ) (G : ι → Ω → ℝ) :
    μ.covariance (fun ω => ∑ k ∈ s, G k ω) F = ∑ k ∈ s, μ.covariance (G k) F := by
  have h := cov_sum_left μ s F (fun _ => (1:ℝ)) G
  simp only [one_mul] at h
  exact h

theorem inner_eucl {ι : Type*} [Fintype ι] (a w : EuclideanSpace ℝ ι) :
    inner ℝ a w = ∑ c, a c * w c := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro c _
  simp [mul_comm]

theorem eucl_norm_le {ι : Type*} [Fintype ι] (v : EuclideanSpace ℝ ι) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ c, |v c| ≤ K) :
    ‖v‖ ≤ Real.sqrt (Fintype.card ι) * K := by
  rw [EuclideanSpace.norm_eq]
  have hs : ∑ c, ‖v c‖ ^ 2 ≤ (Fintype.card ι : ℝ) * K ^ 2 := by
    calc ∑ c, ‖v c‖ ^ 2 ≤ ∑ _c : ι, K ^ 2 :=
          Finset.sum_le_sum (fun c _ => by
            rw [Real.norm_eq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (h c) 2)
      _ = _ := by simp
  calc Real.sqrt (∑ c, ‖v c‖ ^ 2) ≤ Real.sqrt ((Fintype.card ι : ℝ) * K ^ 2) :=
        Real.sqrt_le_sqrt hs
    _ = Real.sqrt (Fintype.card ι) * K := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hK]

section Bridge2
open PaperBridgeFit
variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

theorem gamma_coord (B : BridgeData Head Band) [Nonempty Head]
    (xi : B.ParamSpace) (a : B.NuisanceSpace) (c : NuisanceCoord B.HeadIndex) :
    (B.nuisanceCovarianceOperator xi a) c =
      (B.tiltedLaw xi).covariance (fun m => B.nuisanceStatistic m c)
        (fun m => inner ℝ a (B.nuisanceStatistic m)) := by
  have h := gamma_bilin B xi (EuclideanSpace.single c 1) a
  simp only [EuclideanSpace.inner_single_left, map_one, one_mul] at h
  exact h

variable (B : BridgeData Head Band) [Nonempty Head] (xi : B.ParamSpace) {γ : ℝ} (hγ : 0 < γ)
  (hgap : ∀ z, γ * ‖z‖ ^ 2 ≤ inner ℝ z (B.nuisanceCovarianceOperator xi z))

include hγ hgap in
theorem coef_gamma (F : B.sampleData.Sample → ℝ) :
    B.nuisanceCovarianceOperator xi (B.nuisanceCoefficientOfScore xi hγ hgap F) =
      B.nuisanceCovarianceVector xi F := by
  have h := (B.nuisanceCovarianceEquiv xi hγ hgap).apply_symm_apply (B.nuisanceCovarianceVector xi F)
  exact h

include hγ hgap in
theorem resid_eq (F : B.sampleData.Sample → ℝ) :
    B.nuisanceResidualScore xi hγ hgap F = fun m => F m -
      ∑ c, B.nuisanceCoefficientOfScore xi hγ hgap F c * B.nuisanceStatistic m c := by
  funext m
  rw [BridgeData.nuisanceResidualScore, inner_eucl]

include hγ hgap in
theorem resid_orth (F : B.sampleData.Sample → ℝ) (c : NuisanceCoord B.HeadIndex) :
    (B.tiltedLaw xi).covariance (fun m => B.nuisanceStatistic m c)
      (B.nuisanceResidualScore xi hγ hgap F) = 0 := by
  have h1 : B.nuisanceResidualScore xi hγ hgap F = fun m => F m -
      inner ℝ (B.nuisanceCoefficientOfScore xi hγ hgap F) (B.nuisanceStatistic m) := rfl
  rw [h1, cov_sub_right, ← gamma_coord, coef_gamma, BridgeData.nuisanceCovarianceVector_apply,
    sub_self]

include hγ hgap in
theorem resid_cov (G F : B.sampleData.Sample → ℝ) :
    (B.tiltedLaw xi).covariance G (B.nuisanceResidualScore xi hγ hgap F) =
      (B.tiltedLaw xi).covariance G F -
        ∑ c, B.nuisanceCoefficientOfScore xi hγ hgap F c *
          (B.tiltedLaw xi).covariance G (fun m => B.nuisanceStatistic m c) := by
  rw [resid_eq, cov_sub_right, cov_sum_right]

include hγ hgap in
theorem resid_self (F G : B.sampleData.Sample → ℝ) :
    (B.tiltedLaw xi).covariance (B.nuisanceResidualScore xi hγ hgap F)
      (B.nuisanceResidualScore xi hγ hgap G) =
    (B.tiltedLaw xi).covariance F (B.nuisanceResidualScore xi hγ hgap G) := by
  conv_lhs => rw [resid_eq B xi hγ hgap F]
  rw [cov_sub_left, cov_sum_left]
  simp only [resid_orth, mul_zero, Finset.sum_const_zero, sub_zero]

include hγ hgap in
theorem coef_norm_le (F : B.sampleData.Sample → ℝ) :
    γ * ‖B.nuisanceCoefficientOfScore xi hγ hgap F‖ ≤ ‖B.nuisanceCovarianceVector xi F‖ := by
  have h1 := hgap (B.nuisanceCoefficientOfScore xi hγ hgap F)
  rw [coef_gamma] at h1
  have h2 := real_inner_le_norm (B.nuisanceCoefficientOfScore xi hγ hgap F)
    (B.nuisanceCovarianceVector xi F)
  set a := ‖B.nuisanceCoefficientOfScore xi hγ hgap F‖
  set u := ‖B.nuisanceCovarianceVector xi F‖
  have ha : 0 ≤ a := norm_nonneg _
  have hu : 0 ≤ u := norm_nonneg _
  rcases eq_or_lt_of_le ha with h0 | hpos
  · rw [← h0]; simp [hu]
  · have : γ * a * a ≤ u * a := by nlinarith
    exact le_of_mul_le_mul_right this hpos

end Bridge2

section Band
open PaperBridgeFit ArithmeticBandGeometry PaperWeightedInverseExport MovingLowGaugeTransfer
  FiniteGraphQuotientInverse ArithmeticModel
variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
variable (B : BridgeData Head Band)

def Vp (p : BandPrime B.sampleData.n B.sampleData.W) : B.sampleData.Sample → ℝ :=
  fun m => valuation p.1 (B.sampleData.value m)

theorem bandScore_eq (j : Band) :
    B.bandScore j = fun m => ∑ p ∈ B.partition.data.fiber j, Vp B p m := rfl

theorem harmonicMass_eq (j : Band) :
    B.harmonicMass j = ∑ p ∈ B.partition.data.fiber j, 1 / (p.1 : ℝ) := rfl

theorem sum_fiber (f : BandPrime B.sampleData.n B.sampleData.W → ℝ) :
    ∑ j, ∑ p ∈ B.partition.data.fiber j, f p = ∑ p, f p := by
  exact Finset.sum_fiberwise Finset.univ B.partition.band f

theorem mass_center (j : Band) :
    B.harmonicMass j * B.bandCenter j =
      ∑ p ∈ B.partition.data.fiber j, 1 / (p.1 : ℝ) * tPrime B.sampleData.n p.1 := by
  have h : B.partition.data.mass j ≠ 0 := (B.partition.data.mass_pos j).ne'
  change B.partition.data.mass j *
    ((∑ p ∈ B.partition.data.fiber j, (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) /
      B.partition.data.mass j) = _
  field_simp

theorem moment_eq :
    ∑ j, B.harmonicMass j * B.bandCenter j =
      ∑ p : BandPrime B.sampleData.n B.sampleData.W, 1 / (p.1 : ℝ) * tPrime B.sampleData.n p.1 := by
  simp_rw [mass_center]
  exact sum_fiber B _

theorem X_eq (q : B.RawBandGauge) :
    B.bandRegressionScore q = fun m =>
      ∑ s : BandPrime B.sampleData.n B.sampleData.W, q.1 (B.partition.band s) * Vp B s m := by
  funext m
  unfold BridgeData.bandRegressionScore
  rw [← sum_fiber B]
  apply Finset.sum_congr rfl
  intro j _
  rw [bandScore_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have : B.partition.band s = j := (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff _).mp hs
  rw [this]

variable [Nonempty Head]

theorem cov_Omega_X (xi : B.ParamSpace) (i : Band) (q : B.RawBandGauge) :
    (B.tiltedLaw xi).covariance (B.bandScore i) (B.bandRegressionScore q) =
      ∑ p ∈ B.partition.data.fiber i, ∑ s : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band s) * (B.tiltedLaw xi).covariance (Vp B p) (Vp B s) := by
  rw [bandScore_eq, cov_sum_left1]
  apply Finset.sum_congr rfl
  intro p _
  rw [X_eq, cov_sum_right]

theorem fullBandRow_eq (xi : B.ParamSpace) (b : Band → ℝ) (i : Band) :
    PrimePowerSharpBandTransfer.fullBandRow (B.actualValuationLaw xi) B.partition b i =
      (1 / B.harmonicMass i) * ∑ p ∈ B.partition.data.fiber i,
        ∑ s : BandPrime B.sampleData.n B.sampleData.W,
          b (B.partition.band s) * (B.tiltedLaw xi).covariance (Vp B p) (Vp B s) := rfl

theorem symm_project [Nonempty Band] (hα : ∀ j, B.bandCenter j ≠ 0) (x : Band → ℝ) (i : Band) :
    (((scaleGaugeLinearEquiv B.harmonicMass B.bandCenter hα).symm (B.projectRawBandVector x) :
        SharpGaugeSpace B.harmonicMass B.bandCenter) : Band → ℝ) i =
      meanProjection (sharpWeight B.harmonicMass B.bandCenter)
        (fun j => x j / B.bandCenter j) i := by
  rw [scaleGaugeLinearEquiv_symm_apply]
  change weightedGaugeProjection B.harmonicMass B.bandCenter x i / B.bandCenter i = _
  have hTot : (∑ j, B.harmonicMass j * B.bandCenter j ^ 2) ≠ 0 := by
    have := B.sharpBandWeightTotal_pos
    unfold sharpWeightTotal sharpWeight at this
    exact this.ne'
  have hs : (∑ j, sharpWeight B.harmonicMass B.bandCenter j * (x j / B.bandCenter j)) =
      ∑ j, B.harmonicMass j * B.bandCenter j * x j := by
    apply Finset.sum_congr rfl
    intro j _
    unfold sharpWeight
    field_simp [hα j]
  unfold meanProjection weightedMean weightTotal
  rw [hs]
  unfold weightedGaugeProjection sharpWeightTotal
  simp only [sharpWeight]
  field_simp [hα i]

theorem meanProjection_sub' (ω x x' : Band → ℝ) (i : Band) :
    meanProjection ω x i - meanProjection ω x' i = meanProjection ω (fun j => x j - x' j) i := by
  unfold meanProjection weightedMean
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

theorem meanProjection_bound (ω g : Band → ℝ) (hω : ∀ j, 0 ≤ ω j) (hpos : 0 < ∑ j, ω j)
    (K : ℝ) (hg : ∀ j, |g j| ≤ K) (i : Band) :
    |meanProjection ω g i| ≤ 2 * K := by
  unfold meanProjection weightedMean weightTotal
  have h1 : |(∑ j, ω j * g j)| ≤ K * ∑ j, ω j := by
    calc |(∑ j, ω j * g j)| ≤ ∑ j, |ω j * g j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, ω j * K := Finset.sum_le_sum (fun j _ => by
          rw [abs_mul, abs_of_nonneg (hω j)]
          exact mul_le_mul_of_nonneg_left (hg j) (hω j))
      _ = K * ∑ j, ω j := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  have h2 : |(∑ j, ω j * g j) / ∑ j, ω j| ≤ K := by
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    exact h1
  calc |g i - (∑ j, ω j * g j) / ∑ j, ω j| ≤ |g i| + |(∑ j, ω j * g j) / ∑ j, ω j| :=
        abs_sub _ _
    _ ≤ K + K := add_le_add (hg i) h2
    _ = 2 * K := by ring


theorem diff_coord [Nonempty Band] (hα : ∀ j, B.bandCenter j ≠ 0) (xi : B.ParamSpace) {γ : ℝ}
    (hγ : 0 < γ)
    (hgap : ∀ z, γ * ‖z‖ ^ 2 ≤ inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (y : SharpGaugeSpace B.harmonicMass B.bandCenter) (i : Band) :
    (((scaleGaugeLinearEquiv B.harmonicMass B.bandCenter hα).symm
        (B.actualBandSchurLinearMap xi hγ hgap
          (scaleGaugeLinearEquiv B.harmonicMass B.bandCenter hα y)) :
          SharpGaugeSpace B.harmonicMass B.bandCenter) : Band → ℝ) i -
      ((B.actualFullProjectedCLM xi y : SharpGaugeSpace B.partition.mass B.partition.center) :
        Band → ℝ) i =
    meanProjection (sharpWeight B.harmonicMass B.bandCenter)
      (fun j => -(∑ c, B.nuisanceCoefficientOfScore xi hγ hgap
          (B.bandRegressionScore (scaleGaugeLinearEquiv B.harmonicMass B.bandCenter hα y)) c *
          (B.tiltedLaw xi).covariance (B.bandScore j) (fun m => B.nuisanceStatistic m c)) /
        (B.harmonicMass j * B.bandCenter j)) i := by
  set S := scaleGaugeLinearEquiv B.harmonicMass B.bandCenter hα
  have h1 : B.actualBandSchurLinearMap xi hγ hgap (S y) =
      B.projectRawBandVector (B.schurBandRow xi hγ hgap (S y)) := rfl
  rw [h1, symm_project]
  have h2 : ((B.actualFullProjectedCLM xi y : SharpGaugeSpace B.partition.mass B.partition.center) :
        Band → ℝ) i =
      meanProjection (sharpWeight B.harmonicMass B.bandCenter)
        (fun j => PrimePowerSharpBandTransfer.fullSharpRow (B.actualValuationLaw xi)
          B.partition y.1 j) i := rfl
  rw [h2, meanProjection_sub']
  congr 1
  funext j
  have h3 : B.schurBandRow xi hγ hgap (S y) j =
      (B.tiltedLaw xi).covariance (B.bandScore j)
        (B.nuisanceResidualScore xi hγ hgap (B.bandRegressionScore (S y))) /
          B.harmonicMass j := rfl
  rw [h3, resid_cov, cov_Omega_X]
  unfold PrimePowerSharpBandTransfer.fullSharpRow
  rw [fullBandRow_eq]
  have hH := (B.harmonicMass_pos j).ne'
  have hA := hα j
  have e1 : ∀ k, ((S y : B.RawBandGauge) : Band → ℝ) k = B.bandCenter k * y.1 k := fun k => rfl
  simp only [e1]
  have e2 : ∀ k, B.partition.center k = B.bandCenter k := fun k => rfl
  simp only [e2]
  field_simp
  ring


theorem g_bound [Nonempty Band] (hα : ∀ j, B.bandCenter j ≠ 0) (xi : B.ParamSpace) {γ : ℝ}
    (hγ : 0 < γ)
    (hgap : ∀ z, γ * ‖z‖ ^ 2 ≤ inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (ε amin : ℝ) (hε : 0 ≤ ε) (hamin : 0 < amin) (hcent : ∀ i, amin ≤ B.bandCenter i)
    (hcov : ∀ (c : NuisanceCoord B.HeadIndex) (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance (fun m => B.nuisanceStatistic m c)
        (fun m => valuation p.1 (B.sampleData.value m))| ≤ ε * (1 / (p.1 : ℝ)))
    (y : SharpGaugeSpace B.harmonicMass B.bandCenter) (j : Band) :
    |-(∑ c, B.nuisanceCoefficientOfScore xi hγ hgap
          (B.bandRegressionScore (scaleGaugeLinearEquiv B.harmonicMass B.bandCenter hα y)) c *
          (B.tiltedLaw xi).covariance (B.bandScore j) (fun m => B.nuisanceStatistic m c)) /
        (B.harmonicMass j * B.bandCenter j)| ≤ B.nuisanceMarkedSchurRate ε γ amin * ‖y‖ := by
  set S := scaleGaugeLinearEquiv B.harmonicMass B.bandCenter hα
  set a := B.nuisanceCoefficientOfScore xi hγ hgap (B.bandRegressionScore (S y))
  set M := ∑ k, B.harmonicMass k * B.bandCenter k with hM
  set r := Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) with hr
  have hrate : B.nuisanceMarkedSchurRate ε γ amin = ((r * (ε * M)) / γ * (r * ε)) / amin := rfl
  have hαpos : ∀ k, 0 < B.bandCenter k := fun k => B.bandCenter_pos k
  have hHpos : ∀ k, 0 < B.harmonicMass k := fun k => B.harmonicMass_pos k
  have hMnn : 0 ≤ M := Finset.sum_nonneg (fun k _ => (mul_pos (hHpos k) (hαpos k)).le)
  have hY : 0 ≤ ‖y‖ := norm_nonneg _
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  -- coordinate bounds
  have hOmega : ∀ c k, |(B.tiltedLaw xi).covariance (fun m => B.nuisanceStatistic m c)
      (B.bandScore k)| ≤ ε * B.harmonicMass k := by
    intro c k
    rw [bandScore_eq, cov_sum_right1, harmonicMass_eq, Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun p _ => hcov c p))
  have hycoord : ∀ k, |y.1 k| ≤ ‖y‖ := by
    intro k
    have := norm_le_pi_norm (y.1) k
    rw [Real.norm_eq_abs] at this
    exact this
  have hX : ∀ c, |(B.tiltedLaw xi).covariance (fun m => B.nuisanceStatistic m c)
      (B.bandRegressionScore (S y))| ≤ ε * M * ‖y‖ := by
    intro c
    have hXe : B.bandRegressionScore (S y) =
        fun m => ∑ k, ((S y : B.RawBandGauge) : Band → ℝ) k * B.bandScore k m := rfl
    rw [hXe, cov_sum_right]
    calc |∑ k, ((S y : B.RawBandGauge) : Band → ℝ) k *
            (B.tiltedLaw xi).covariance (fun m => B.nuisanceStatistic m c) (B.bandScore k)|
        ≤ ∑ k, |((S y : B.RawBandGauge) : Band → ℝ) k *
            (B.tiltedLaw xi).covariance (fun m => B.nuisanceStatistic m c) (B.bandScore k)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, (B.bandCenter k * ‖y‖) * (ε * B.harmonicMass k) := by
          apply Finset.sum_le_sum
          intro k _
          rw [abs_mul]
          have e1 : ((S y : B.RawBandGauge) : Band → ℝ) k = B.bandCenter k * y.1 k := rfl
          rw [e1, abs_mul, abs_of_pos (hαpos k)]
          apply mul_le_mul (mul_le_mul_of_nonneg_left (hycoord k) (hαpos k).le) (hOmega c k)
            (abs_nonneg _) (mul_nonneg (hαpos k).le hY)
      _ = ε * M * ‖y‖ := by
          rw [hM, Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          ring
  have hu : ‖B.nuisanceCovarianceVector xi (B.bandRegressionScore (S y))‖ ≤ r * (ε * M * ‖y‖) :=
    eucl_norm_le _ _ (by positivity) (fun c => by
      rw [BridgeData.nuisanceCovarianceVector_apply]; exact hX c)
  have hw : ‖B.nuisanceCovarianceVector xi (B.bandScore j)‖ ≤ r * (ε * B.harmonicMass j) :=
    eucl_norm_le _ _ (mul_nonneg hε (hHpos j).le) (fun c => by
      rw [BridgeData.nuisanceCovarianceVector_apply]; exact hOmega c j)
  have ha : γ * ‖a‖ ≤ ‖B.nuisanceCovarianceVector xi (B.bandRegressionScore (S y))‖ :=
    coef_norm_le B xi hγ hgap _
  have hIe : (∑ c, a c * (B.tiltedLaw xi).covariance (B.bandScore j)
      (fun m => B.nuisanceStatistic m c)) =
      inner ℝ a (B.nuisanceCovarianceVector xi (B.bandScore j)) := by
    rw [inner_eucl]
    apply Finset.sum_congr rfl
    intro c _
    rw [BridgeData.nuisanceCovarianceVector_apply, cov_comm]
  rw [hIe]
  have hin := abs_real_inner_le_norm a (B.nuisanceCovarianceVector xi (B.bandScore j))
  set I := inner ℝ a (B.nuisanceCovarianceVector xi (B.bandScore j))
  set A := ‖a‖
  set Uw := ‖B.nuisanceCovarianceVector xi (B.bandScore j)‖
  have hA0 : 0 ≤ A := norm_nonneg _
  have hHa : 0 < B.harmonicMass j * B.bandCenter j := mul_pos (hHpos j) (hαpos j)
  rw [abs_div, abs_neg, abs_of_pos hHa, div_le_iff₀ hHa]
  have hAle : A ≤ r * (ε * M * ‖y‖) / γ := by
    rw [le_div_iff₀ hγ]; linarith
  have hstep : |I| ≤ (r * (ε * M * ‖y‖) / γ) * (r * (ε * B.harmonicMass j)) :=
    hin.trans (mul_le_mul hAle hw (norm_nonneg _) (by positivity))
  set K0 := (r * (ε * M)) / γ * (r * ε) * ‖y‖ * B.harmonicMass j with hK0
  have hK0nn : 0 ≤ K0 := mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg
    (mul_nonneg hr0 (mul_nonneg hε hMnn)) hγ.le) (mul_nonneg hr0 hε)) hY) (hHpos j).le
  have hstep' : (r * (ε * M * ‖y‖) / γ) * (r * (ε * B.harmonicMass j)) = K0 := by
    rw [hK0]; field_simp
  have hratio : 1 ≤ B.bandCenter j / amin := by
    rw [le_div_iff₀ hamin]; linarith [hcent j]
  have hfin : ((r * (ε * M)) / γ * (r * ε)) / amin * ‖y‖ * (B.harmonicMass j * B.bandCenter j) =
      K0 * (B.bandCenter j / amin) := by
    rw [hK0]; field_simp
  rw [hrate, hfin]
  calc |I| ≤ K0 := hstep.trans hstep'.le
    _ = K0 * 1 := (mul_one _).symm
    _ ≤ K0 * (B.bandCenter j / amin) := mul_le_mul_of_nonneg_left hratio hK0nn


theorem core [Nonempty Band] (hα : ∀ j, B.bandCenter j ≠ 0) (xi : B.ParamSpace) {γ : ℝ}
    (hγ : 0 < γ)
    (hgap : ∀ z, γ * ‖z‖ ^ 2 ≤ inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (ε amin : ℝ) (hε : 0 ≤ ε) (hamin : 0 < amin) (hcent : ∀ i, amin ≤ B.bandCenter i)
    (hcov : ∀ (c : NuisanceCoord B.HeadIndex) (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance (fun m => B.nuisanceStatistic m c)
        (fun m => valuation p.1 (B.sampleData.value m))| ≤ ε * (1 / (p.1 : ℝ)))
    (Cfull : ℝ) (hC : 0 < Cfull)
    (Fe : SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
      SharpGaugeSpace B.partition.mass B.partition.center)
    (hFe : ∀ q, Fe q = B.actualFullProjectedCLM xi q)
    (hFinv : ∀ v, ‖Fe.symm v‖ ≤ Cfull * ‖v‖)
    (hκ : Cfull * (2 * B.nuisanceMarkedSchurRate ε γ amin) ≤ 1 / 2)
    (q : B.RawBandGauge) :
    ‖(scaleGaugeLinearEquiv B.harmonicMass B.bandCenter hα).symm q‖ ≤
      Cfull / (1 - Cfull * (2 * B.nuisanceMarkedSchurRate ε γ amin)) *
        ‖(scaleGaugeLinearEquiv B.harmonicMass B.bandCenter hα).symm
          (B.actualBandSchurLinearMap xi hγ hgap q)‖ := by
  set S := scaleGaugeLinearEquiv B.harmonicMass B.bandCenter hα
  set rate := B.nuisanceMarkedSchurRate ε γ amin
  set y := S.symm q
  have hq : S y = q := S.apply_symm_apply q
  set a := S.symm (B.actualBandSchurLinearMap xi hγ hgap (S y))
  have hrate_y : 0 ≤ rate * ‖y‖ := (abs_nonneg _).trans
    (g_bound B hα xi hγ hgap ε amin hε hamin hcent hcov y (Classical.arbitrary Band))
  set Fy : SharpGaugeSpace B.harmonicMass B.bandCenter := B.actualFullProjectedCLM xi y with hFy
  have hD : ‖a - Fy‖ ≤ 2 * (rate * ‖y‖) := by
    rw [Submodule.coe_norm]
    refine (pi_norm_le_iff_of_nonneg (by linarith)).mpr ?_
    intro i
    rw [Submodule.coe_sub, Pi.sub_apply, Real.norm_eq_abs]
    rw [diff_coord B hα xi hγ hgap y i]
    refine meanProjection_bound _ _ (fun j => ?_) ?_ _ (fun j => g_bound B hα xi hγ hgap ε amin hε
      hamin hcent hcov y j) i
    · exact mul_nonneg (B.harmonicMass_pos j).le (sq_nonneg _)
    · have := B.sharpBandWeightTotal_pos
      exact this
  have hy : ‖y‖ ≤ Cfull * ‖Fy‖ := by
    have h := hFinv (Fe y)
    rw [Fe.symm_apply_apply, hFe] at h
    exact h
  have htri : ‖Fy‖ ≤ ‖a‖ + ‖a - Fy‖ := by
    have := norm_sub_le a (a - Fy)
    rwa [sub_sub_cancel] at this
  have hpos : 0 < 1 - Cfull * (2 * rate) := by linarith
  have hmain : (1 - Cfull * (2 * rate)) * ‖y‖ ≤ Cfull * ‖a‖ := by
    have h1 : ‖y‖ ≤ Cfull * (‖a‖ + 2 * (rate * ‖y‖)) :=
      hy.trans (mul_le_mul_of_nonneg_left (htri.trans (by linarith)) hC.le)
    nlinarith
  have ha : a = S.symm (B.actualBandSchurLinearMap xi hγ hgap q) := by
    simp only [a]; rw [hq]
  rw [← ha, div_mul_eq_mul_div, le_div_iff₀ hpos]
  linarith


theorem dpair [Nonempty Band] (xi : B.ParamSpace) {γ : ℝ} (hγ : 0 < γ)
    (hgap : ∀ z, γ * ‖z‖ ^ 2 ≤ inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u w : B.RawBandGauge) :
    ∑ j, B.harmonicMass j * u.1 j * (B.actualBandSchurLinearMap xi hγ hgap w).1 j =
      (B.tiltedLaw xi).covariance (B.nuisanceResidualScore xi hγ hgap (B.bandRegressionScore u))
        (B.nuisanceResidualScore xi hγ hgap (B.bandRegressionScore w)) := by
  rw [resid_self]
  have hA : ∀ j, (B.actualBandSchurLinearMap xi hγ hgap w).1 j =
      weightedGaugeProjection B.harmonicMass B.bandCenter (B.schurBandRow xi hγ hgap w) j :=
    fun j => rfl
  simp only [hA]
  unfold weightedGaugeProjection
  set c := (∑ k, B.harmonicMass k * B.bandCenter k * B.schurBandRow xi hγ hgap w k) /
    sharpWeightTotal B.harmonicMass B.bandCenter
  have hg : ∑ j, rawGaugeWeight B.harmonicMass B.bandCenter j * u.1 j = 0 := u.2
  unfold rawGaugeWeight at hg
  have hs : ∀ j, B.schurBandRow xi hγ hgap w j =
      (B.tiltedLaw xi).covariance (B.bandScore j)
        (B.nuisanceResidualScore xi hγ hgap (B.bandRegressionScore w)) / B.harmonicMass j :=
    fun j => rfl
  have e1 : ∑ j, B.harmonicMass j * u.1 j *
      (B.schurBandRow xi hγ hgap w j - B.bandCenter j * c) =
      ∑ j, u.1 j * (B.tiltedLaw xi).covariance (B.bandScore j)
        (B.nuisanceResidualScore xi hγ hgap (B.bandRegressionScore w)) -
        c * ∑ j, B.harmonicMass j * B.bandCenter j * u.1 j := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hs]
    have := (B.harmonicMass_pos j).ne'
    field_simp
  rw [e1, hg, mul_zero, sub_zero]
  have hX : B.bandRegressionScore u = fun m => ∑ j, u.1 j * B.bandScore j m := rfl
  rw [hX, cov_sum_left]

theorem quad [Nonempty Band] (hα : ∀ j, B.bandCenter j ≠ 0) (xi : B.ParamSpace) {γ : ℝ}
    (hγ : 0 < γ)
    (hgap : ∀ z, γ * ‖z‖ ^ 2 ≤ inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (Cs : ℝ) (hCs : 0 < Cs)
    (hbound : ∀ v : B.RawBandGauge,
      ‖(scaleGaugeLinearEquiv B.harmonicMass B.bandCenter hα).symm v‖ ≤
        Cs * ‖(scaleGaugeLinearEquiv B.harmonicMass B.bandCenter hα).symm
          (B.actualBandSchurLinearMap xi hγ hgap v)‖)
    (hsurj : ∀ q, ∃ v, B.actualBandSchurLinearMap xi hγ hgap v = q)
    (q : B.RawBandGauge) :
    rawDLowerWeight B.harmonicMass B.bandCenter ^ 2 /
        (sharpWeightTotal B.harmonicMass B.bandCenter * Cs) *
        ‖(scaleGaugeLinearEquiv B.harmonicMass B.bandCenter hα).symm q‖ ^ 2 ≤
      (B.tiltedLaw xi).covariance (B.nuisanceResidualScore xi hγ hgap (B.bandRegressionScore q))
        (B.nuisanceResidualScore xi hγ hgap (B.bandRegressionScore q)) := by
  set S := scaleGaugeLinearEquiv B.harmonicMass B.bandCenter hα
  obtain ⟨v, hv⟩ := hsurj q
  set y := S.symm q
  set yt := S.symm v
  have hyt : ‖yt‖ ≤ Cs * ‖y‖ := by
    have := hbound v
    rwa [hv] at this
  have hqc : ∀ j, q.1 j = B.bandCenter j * y.1 j := by
    intro j
    have h : S y = q := S.apply_symm_apply q
    rw [← h]
    rfl
  have hvc : ∀ j, v.1 j = B.bandCenter j * yt.1 j := by
    intro j
    have h : S yt = v := S.apply_symm_apply v
    rw [← h]
    rfl
  have hQd := dpair B xi hγ hgap q v
  rw [hv] at hQd
  have hBvv := dpair B xi hγ hgap v v
  rw [hv] at hBvv
  have hCS := cov_sq_le (B.tiltedLaw xi)
    (B.nuisanceResidualScore xi hγ hgap (B.bandRegressionScore q))
    (B.nuisanceResidualScore xi hγ hgap (B.bandRegressionScore v))
  rw [← hQd, ← hBvv] at hCS
  set V := (B.tiltedLaw xi).covariance (B.nuisanceResidualScore xi hγ hgap (B.bandRegressionScore q))
        (B.nuisanceResidualScore xi hγ hgap (B.bandRegressionScore q))
  have hV : 0 ≤ V := cov_self_nonneg _ _
  have hycoord : ∀ k, |y.1 k| ≤ ‖y‖ := by
    intro k
    have := norm_le_pi_norm (y.1) k
    rw [Real.norm_eq_abs] at this
    exact this
  have hytcoord : ∀ k, |yt.1 k| ≤ ‖yt‖ := by
    intro k
    have := norm_le_pi_norm (yt.1) k
    rw [Real.norm_eq_abs] at this
    exact this
  have hωpos : ∀ k, 0 < B.harmonicMass k * B.bandCenter k ^ 2 :=
    fun k => mul_pos (B.harmonicMass_pos k) (sq_pos_of_pos (B.bandCenter_pos k))
  have hW : 0 < sharpWeightTotal B.harmonicMass B.bandCenter := B.sharpBandWeightTotal_pos
  -- upper bound on Bvv
  have hBle : ∑ j, B.harmonicMass j * v.1 j * q.1 j ≤
      sharpWeightTotal B.harmonicMass B.bandCenter * Cs * ‖y‖ ^ 2 := by
    calc ∑ j, B.harmonicMass j * v.1 j * q.1 j
        = ∑ j, (B.harmonicMass j * B.bandCenter j ^ 2) * (yt.1 j * y.1 j) := by
          apply Finset.sum_congr rfl; intro j _; rw [hqc, hvc]; ring
      _ ≤ ∑ j, (B.harmonicMass j * B.bandCenter j ^ 2) * (‖yt‖ * ‖y‖) := by
          apply Finset.sum_le_sum; intro j _
          apply mul_le_mul_of_nonneg_left _ (hωpos j).le
          calc yt.1 j * y.1 j ≤ |yt.1 j * y.1 j| := le_abs_self _
            _ = |yt.1 j| * |y.1 j| := abs_mul _ _
            _ ≤ ‖yt‖ * ‖y‖ := mul_le_mul (hytcoord j) (hycoord j) (abs_nonneg _) (norm_nonneg _)
      _ = sharpWeightTotal B.harmonicMass B.bandCenter * (‖yt‖ * ‖y‖) := by
          rw [← Finset.sum_mul]; rfl
      _ ≤ sharpWeightTotal B.harmonicMass B.bandCenter * ((Cs * ‖y‖) * ‖y‖) := by
          apply mul_le_mul_of_nonneg_left _ hW.le
          exact mul_le_mul_of_nonneg_right hyt (norm_nonneg _)
      _ = sharpWeightTotal B.harmonicMass B.bandCenter * Cs * ‖y‖ ^ 2 := by ring
  -- lower bound on Qd
  obtain ⟨j0, hj0⟩ := Finite.exists_max (fun j => |y.1 j|)
  have hynorm : ‖y‖ ≤ |y.1 j0| := by
    rw [Submodule.coe_norm]
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr ?_
    intro j
    rw [Real.norm_eq_abs]
    exact hj0 j
  set wmin := rawDLowerWeight B.harmonicMass B.bandCenter
  have hwmin_le : wmin ≤ B.harmonicMass j0 * B.bandCenter j0 ^ 2 := by
    unfold wmin rawDLowerWeight
    exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ j0))
  have hwmin_pos : 0 < wmin := by
    unfold wmin rawDLowerWeight
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (Finset.min'_mem
      (Finset.univ.image (fun j ↦ B.harmonicMass j * B.bandCenter j ^ 2))
      (by classical exact Finset.univ_nonempty.image _))
    rw [← hk]
    exact hωpos k
  have hQle : wmin * ‖y‖ ^ 2 ≤ ∑ j, B.harmonicMass j * q.1 j * q.1 j := by
    have hterm : ∀ j, 0 ≤ B.harmonicMass j * q.1 j * q.1 j := fun j => by
      have := (B.harmonicMass_pos j).le
      rw [mul_assoc]; exact mul_nonneg this (mul_self_nonneg _)
    have hsingle := Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ j0)
    have e : B.harmonicMass j0 * q.1 j0 * q.1 j0 =
        (B.harmonicMass j0 * B.bandCenter j0 ^ 2) * (y.1 j0) ^ 2 := by rw [hqc]; ring
    have hy2 : ‖y‖ ^ 2 ≤ (y.1 j0) ^ 2 := by
      rw [← sq_abs (y.1 j0)]
      exact pow_le_pow_left₀ (norm_nonneg _) hynorm 2
    calc wmin * ‖y‖ ^ 2 ≤ (B.harmonicMass j0 * B.bandCenter j0 ^ 2) * (y.1 j0) ^ 2 :=
          mul_le_mul hwmin_le hy2 (sq_nonneg _) (hωpos j0).le
      _ = B.harmonicMass j0 * q.1 j0 * q.1 j0 := e.symm
      _ ≤ _ := hsingle
  set Qd := ∑ j, B.harmonicMass j * q.1 j * q.1 j
  set N := ‖y‖ ^ 2
  have hN : 0 ≤ N := sq_nonneg _
  have hK : 0 < sharpWeightTotal B.harmonicMass B.bandCenter * Cs := mul_pos hW hCs
  have hsq : (wmin * N) ^ 2 ≤ V * (sharpWeightTotal B.harmonicMass B.bandCenter * Cs * N) := by
    calc (wmin * N) ^ 2 ≤ Qd ^ 2 := pow_le_pow_left₀ (mul_nonneg hwmin_pos.le hN) hQle 2
      _ ≤ V * ∑ j, B.harmonicMass j * v.1 j * q.1 j := hCS
      _ ≤ V * (sharpWeightTotal B.harmonicMass B.bandCenter * Cs * N) :=
          mul_le_mul_of_nonneg_left hBle hV
  rcases eq_or_lt_of_le hN with h0 | hNpos
  · rw [← h0, mul_zero]; exact hV
  · rw [div_mul_eq_mul_div, div_le_iff₀ hK]
    have : wmin ^ 2 * N * N ≤ V * (sharpWeightTotal B.harmonicMass B.bandCenter * Cs) * N := by
      nlinarith
    have := le_of_mul_le_mul_right this hNpos
    linarith

end Band

theorem mertens1 (N : ℕ) (hN : 1 ≤ N) :
    ∑ p ∈ (N + 1).primesBelow, Real.log p / p ≤ Real.log N + Real.log 4 := by
  set P := (N + 1).primesBelow with hPdef
  have hprime : ∀ p ∈ P, p.Prime := fun p hp => (Nat.mem_primesBelow.mp hp).2
  have hA : ∑ p ∈ P, Real.log p * ((N / p : ℕ) : ℝ) ≤ N * Real.log N := by
    have h1 : ∀ p ∈ P, Real.log p * ((N / p : ℕ) : ℝ) =
        ∑ m ∈ Finset.Ioc 0 N, if p ∣ m then Real.log p else 0 := by
      intro p _
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
        ← Nat.Ioc_filter_dvd_card_eq_div]
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    calc ∑ m ∈ Finset.Ioc 0 N, ∑ p ∈ P, (if p ∣ m then Real.log p else 0)
        ≤ ∑ _m ∈ Finset.Ioc 0 N, Real.log N := by
          apply Finset.sum_le_sum
          intro m hm
          have hm0 : 0 < m := (Finset.mem_Ioc.mp hm).1
          have hmN : m ≤ N := (Finset.mem_Ioc.mp hm).2
          rw [← Finset.sum_filter]
          have hprod0 : 0 < ∏ p ∈ m.primeFactors, p :=
            Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
          calc ∑ p ∈ P with p ∣ m, Real.log p ≤ ∑ p ∈ m.primeFactors, Real.log p := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro p hp
                  rw [Finset.mem_filter] at hp
                  exact Nat.mem_primeFactors.mpr ⟨hprime p hp.1, hp.2, hm0.ne'⟩
                · intro p _ _
                  exact Real.log_natCast_nonneg p
            _ = Real.log ((∏ p ∈ m.primeFactors, p : ℕ) : ℝ) := by
                rw [Nat.cast_prod, Real.log_prod]
                intro p hp
                exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
            _ ≤ Real.log m := by
                apply Real.log_le_log
                · exact_mod_cast hprod0
                · exact_mod_cast Nat.le_of_dvd hm0 (Nat.prod_primeFactors_dvd m)
            _ ≤ Real.log N := Real.log_le_log (by exact_mod_cast hm0) (by exact_mod_cast hmN)
      _ = N * Real.log N := by rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]; simp
  have hC : ∑ p ∈ P, Real.log p ≤ N * Real.log 4 := by
    have h := primorial_le_four_pow N
    have hP : primorial N = ∏ p ∈ P, p := rfl
    have hpos : 0 < ∏ p ∈ P, p := Finset.prod_pos (fun p hp => (hprime p hp).pos)
    calc ∑ p ∈ P, Real.log p = Real.log ((∏ p ∈ P, p : ℕ) : ℝ) := by
          rw [Nat.cast_prod, Real.log_prod]
          intro p hp
          exact_mod_cast (hprime p hp).ne_zero
      _ ≤ Real.log ((4 : ℝ) ^ N) := by
          apply Real.log_le_log (by exact_mod_cast hpos)
          rw [← hP]; exact_mod_cast h
      _ = N * Real.log 4 := by rw [Real.log_pow]
  have hB : ∀ p ∈ P, (N : ℝ) / p ≤ ((N / p : ℕ) : ℝ) + 1 := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
    rw [div_le_iff₀ hp0]
    have h1 := Nat.div_add_mod N p
    have h2 := Nat.mod_lt N (hprime p hp).pos
    have h3 : N ≤ (N / p + 1) * p := by nlinarith
    exact_mod_cast h3
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have key : (N : ℝ) * ∑ p ∈ P, Real.log p / p ≤ N * Real.log N + N * Real.log 4 := by
    calc (N : ℝ) * ∑ p ∈ P, Real.log p / p = ∑ p ∈ P, Real.log p * ((N : ℝ) / p) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
      _ ≤ ∑ p ∈ P, Real.log p * (((N / p : ℕ) : ℝ) + 1) := by
          apply Finset.sum_le_sum; intro p hp
          exact mul_le_mul_of_nonneg_left (hB p hp) (Real.log_natCast_nonneg p)
      _ = ∑ p ∈ P, Real.log p * ((N / p : ℕ) : ℝ) + ∑ p ∈ P, Real.log p := by
          rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro p _; ring
      _ ≤ N * Real.log N + N * Real.log 4 := add_le_add hA hC
  have : (N : ℝ) * ∑ p ∈ P, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by linarith
  exact le_of_mul_le_mul_left this hN0

section Moment
open ArithmeticModel ArithmeticBandGeometry

theorem moment_le (n W : ℕ) (hy4 : 4 ≤ y n) :
    ∑ p : BandPrime n W, 1 / (p.1 : ℝ) * tPrime n p.1 ≤ 2 := by
  rw [← Finset.sum_subtype (primeBand n W) (fun _ => Iff.rfl) (fun p => 1 / (p : ℝ) * tPrime n p)]
  have hly : Real.log 4 ≤ Real.log (y n) := Real.log_le_log (by norm_num) hy4
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlypos : 0 < Real.log (y n) := lt_of_lt_of_le hl4 hly
  have hy0 : 0 ≤ y n := by linarith
  have hyN : 1 ≤ yNat n := by
    have : (4 : ℕ) ≤ yNat n := Nat.le_floor (by exact_mod_cast hy4)
    omega
  have hyNle : (yNat n : ℝ) ≤ y n := Nat.floor_le hy0
  calc ∑ p ∈ primeBand n W, 1 / (p : ℝ) * tPrime n p
      = (∑ p ∈ primeBand n W, Real.log p / p) / Real.log (y n) := by
        rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro p _
        unfold tPrime; ring
    _ ≤ (∑ p ∈ (yNat n + 1).primesBelow, Real.log p / p) / Real.log (y n) := by
        apply div_le_div_of_nonneg_right _ hlypos.le
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro p _ _
        exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
    _ ≤ (Real.log (yNat n) + Real.log 4) / Real.log (y n) :=
        div_le_div_of_nonneg_right (mertens1 _ hyN) hlypos.le
    _ ≤ (Real.log (y n) + Real.log 4) / Real.log (y n) := by
        apply div_le_div_of_nonneg_right _ hlypos.le
        have : Real.log (yNat n) ≤ Real.log (y n) :=
          Real.log_le_log (by exact_mod_cast hyN) hyNle
        linarith
    _ ≤ 2 := by rw [div_le_iff₀ hlypos]; linarith

end Moment

section Gamma
open PaperBridgeFit PaperGuardCensus
variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

theorem card_nuis_le (B : BridgeData Head Band) :
    (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤ Fintype.card Head + 1 := by
  let f : NuisanceCoord B.HeadIndex → Option Head := fun c =>
    match c with
    | .physical => none
    | .head h => some h.1
  have hf : Function.Injective f := by
    intro c1 c2 h
    cases c1 <;> cases c2 <;> simp_all [f, Subtype.ext_iff]
  have := Fintype.card_le_of_injective f hf
  rw [Fintype.card_option] at this
  exact_mod_cast this

theorem card_head_le (B : BridgeData Head Band) :
    (Fintype.card B.HeadIndex : ℝ) ≤ Fintype.card Head := by
  exact_mod_cast Fintype.card_subtype_le _

noncomputable def gamma0 (I : PhysicalIntervals) (U : ℝ) (a : NNReal) (W : ℕ) (mf : ℝ) (K : ℕ) : ℝ :=
  Real.exp (-2 * ((PaperStatisticNorm.valuationLogCoefficient U W +
      Real.sqrt ((K : ℝ) + 1) * max (PaperStatisticNorm.physicalLogCoefficient U) (3 / Real.log 2)) *
        (3 * (a : ℝ)))) *
    (mf ^ 2 * (Real.log (I.lower .plus) - Real.log (I.upper .minus)) ^ 2 /
      (2 * (2 * (Real.log (I.lower .plus) - Real.log (I.upper .minus)) ^ 2 + 1 +
        8 * Real.log U ^ 2 * (K : ℝ))))

theorem gamma0_pos (I : PhysicalIntervals) (U : ℝ) (a : NNReal) (W : ℕ) (mf : ℝ) (hmf : 0 < mf)
    (K : ℕ) : 0 < gamma0 I U a W mf K := by
  unfold gamma0
  have hsep := BridgeData.fixedInterval_separation_pos I
  apply mul_pos (Real.exp_pos _)
  apply div_pos
  · exact mul_pos (pow_pos hmf 2) (pow_pos hsep 2)
  · positivity

theorem gamma_lower (B : BridgeData Head Band) [Nonempty Head] (I : PhysicalIntervals) {U : ℝ}
    (a : NNReal) (W : ℕ) (hBW : B.sampleData.W = W)
    (T : BarycentricTarget B.sampleData) (mf : ℝ) (hmf : 0 < mf) (hmfT : mf ≤ T.cellMassMargin) :
    gamma0 I U a W mf (Fintype.card Head) ≤ B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T := by
  unfold gamma0 BridgeData.canonicalEffectiveNuisanceGamma BridgeData.uniformNuisanceGap
    BridgeData.nuisanceGeometryConstant BridgeData.nuisanceStatisticCoefficient
  rw [hBW]
  have hsep := BridgeData.fixedInterval_separation_pos I
  set sep := Real.log (I.lower .plus) - Real.log (I.upper .minus)
  have hplc : 0 ≤ max (PaperStatisticNorm.physicalLogCoefficient U) (3 / Real.log 2) :=
    le_max_of_le_right (div_nonneg (by norm_num) (Real.log_nonneg (by norm_num)))
  have hd := card_nuis_le B
  have hk := card_head_le B
  have ha : (0 : ℝ) ≤ a := a.2
  have hsq : Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤
      Real.sqrt ((Fintype.card Head : ℝ) + 1) := Real.sqrt_le_sqrt hd
  have hexp : Real.exp (-2 * ((PaperStatisticNorm.valuationLogCoefficient U W +
      Real.sqrt ((Fintype.card Head : ℝ) + 1) *
        max (PaperStatisticNorm.physicalLogCoefficient U) (3 / Real.log 2)) * (3 * (a : ℝ)))) ≤
      Real.exp (-2 * ((PaperStatisticNorm.valuationLogCoefficient U W +
        Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          max (PaperStatisticNorm.physicalLogCoefficient U) (3 / Real.log 2)) * (3 * (a : ℝ)))) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right hsq hplc
    nlinarith
  apply mul_le_mul hexp _ (by positivity) (Real.exp_pos _).le
  have hlam : mf ^ 2 ≤ T.cellMassMargin ^ 2 := pow_le_pow_left₀ hmf.le hmfT 2
  have hG : 2 * sep ^ 2 + 1 + 8 * Real.log U ^ 2 * (Fintype.card B.HeadIndex : ℝ) ≤
      2 * sep ^ 2 + 1 + 8 * Real.log U ^ 2 * (Fintype.card Head : ℝ) := by
    have : 0 ≤ 8 * Real.log U ^ 2 := by positivity
    nlinarith
  apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hlam (by positivity))
    (by positivity) (by linarith)

end Gamma

section Final
open PaperBridgeFit ArithmeticBandGeometry PaperWeightedInverseExport MovingLowGaugeTransfer
  FiniteGraphQuotientInverse ArithmeticModel
variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
variable (B : BridgeData Head Band) [Nonempty Head]

theorem rate_nonneg (ε γ amin : ℝ) (hε : 0 ≤ ε) (hγ : 0 < γ) (hamin : 0 < amin) :
    0 ≤ B.nuisanceMarkedSchurRate ε γ amin := by
  have hM : 0 ≤ ∑ k, B.harmonicMass k * B.bandCenter k :=
    Finset.sum_nonneg (fun k _ => (mul_pos (B.harmonicMass_pos k) (B.bandCenter_pos k)).le)
  unfold BridgeData.nuisanceMarkedSchurRate
  have hr := Real.sqrt_nonneg (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  apply div_nonneg _ hamin.le
  apply mul_nonneg _ (mul_nonneg hr hε)
  exact div_nonneg (mul_nonneg hr (mul_nonneg hε hM)) hγ.le

theorem rate_le (ε γ g0 cs ℓ : ℝ) (hε : 0 ≤ ε) (hg0 : 0 < g0) (hγ : g0 ≤ γ) (hcs : 0 < cs)
    (hℓ : 1 ≤ ℓ) (hM : ∑ k, B.harmonicMass k * B.bandCenter k ≤ 2) :
    B.nuisanceMarkedSchurRate ε γ (cs / ℓ) ≤
      2 * ((Fintype.card Head : ℝ) + 1) * (ε * ℓ) ^ 2 / (g0 * cs) := by
  set M := ∑ k, B.harmonicMass k * B.bandCenter k with hMdef
  have hM0 : 0 ≤ M :=
    Finset.sum_nonneg (fun k _ => (mul_pos (B.harmonicMass_pos k) (B.bandCenter_pos k)).le)
  set d : ℝ := (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hd : d ≤ (Fintype.card Head : ℝ) + 1 := card_nuis_le B
  have hγpos : 0 < γ := lt_of_lt_of_le hg0 hγ
  have hℓpos : 0 < ℓ := lt_of_lt_of_le one_pos hℓ
  have hrate : B.nuisanceMarkedSchurRate ε γ (cs / ℓ) = (d * M) * (ε ^ 2 * ℓ) / (γ * cs) := by
    have hrr : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt hd0
    show (((Real.sqrt d * (ε * M)) / γ) * (Real.sqrt d * ε)) / (cs / ℓ) = _
    have h1 : (((Real.sqrt d * (ε * M)) / γ) * (Real.sqrt d * ε)) / (cs / ℓ) =
        (Real.sqrt d * Real.sqrt d) * M * (ε ^ 2 * ℓ) / (γ * cs) := by
      field_simp
    rw [h1, hrr]
  rw [hrate]
  have hnum : (d * M) * (ε ^ 2 * ℓ) ≤ (((Fintype.card Head : ℝ) + 1) * 2) * (ε * ℓ) ^ 2 := by
    have h1 : d * M ≤ ((Fintype.card Head : ℝ) + 1) * 2 :=
      mul_le_mul hd hM hM0 (by positivity)
    have h2 : ε ^ 2 * ℓ ≤ (ε * ℓ) ^ 2 := by
      have : ε ^ 2 * ℓ ≤ ε ^ 2 * ℓ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg ε)
        nlinarith
      nlinarith
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  calc (d * M) * (ε ^ 2 * ℓ) / (γ * cs) ≤ (d * M) * (ε ^ 2 * ℓ) / (g0 * cs) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hγ hcs.le
    _ ≤ (((Fintype.card Head : ℝ) + 1) * 2) * (ε * ℓ) ^ 2 / (g0 * cs) :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ = 2 * ((Fintype.card Head : ℝ) + 1) * (ε * ℓ) ^ 2 / (g0 * cs) := by ring

theorem perz [Nonempty Band] (hα : ∀ j, B.bandCenter j ≠ 0) (xi : B.ParamSpace) {γ : ℝ}
    (hγ : 0 < γ)
    (hgap : ∀ z, γ * ‖z‖ ^ 2 ≤ inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (ε amin : ℝ) (hε : 0 ≤ ε) (hamin : 0 < amin) (hcent : ∀ i, amin ≤ B.bandCenter i)
    (hcov : ∀ (c : NuisanceCoord B.HeadIndex) (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance (fun m => B.nuisanceStatistic m c)
        (fun m => valuation p.1 (B.sampleData.value m))| ≤ ε * (1 / (p.1 : ℝ)))
    (Cfull : ℝ) (hC : 0 < Cfull)
    (Fe : SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
      SharpGaugeSpace B.partition.mass B.partition.center)
    (hFe : ∀ q, Fe q = B.actualFullProjectedCLM xi q)
    (hFinv : ∀ v, ‖Fe.symm v‖ ≤ Cfull * ‖v‖)
    (hκ : Cfull * (2 * B.nuisanceMarkedSchurRate ε γ amin) ≤ 1 / 2) :
    ∃ e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge,
      (∀ q, e q = B.actualBandSchurLinearMap xi hγ hgap q) ∧
      (∀ v, ‖(scaleGaugeLinearEquiv B.harmonicMass B.bandCenter hα).symm (e.symm v)‖ ≤
        Cfull / (1 - Cfull * (2 * B.nuisanceMarkedSchurRate ε γ amin)) *
          ‖(scaleGaugeLinearEquiv B.harmonicMass B.bandCenter hα).symm v‖) ∧
      (∀ q, rawDLowerWeight B.harmonicMass B.bandCenter ^ 2 /
        (sharpWeightTotal B.harmonicMass B.bandCenter *
          (Cfull / (1 - Cfull * (2 * B.nuisanceMarkedSchurRate ε γ amin)))) *
        ‖(scaleGaugeLinearEquiv B.harmonicMass B.bandCenter hα).symm q‖ ^ 2 ≤
      (B.tiltedLaw xi).covariance (B.nuisanceResidualScore xi hγ hgap (B.bandRegressionScore q))
        (B.nuisanceResidualScore xi hγ hgap (B.bandRegressionScore q))) := by
  set S := scaleGaugeLinearEquiv B.harmonicMass B.bandCenter hα
  have hcore := core B hα xi hγ hgap ε amin hε hamin hcent hcov Cfull hC Fe hFe hFinv hκ
  have hinj : Function.Injective (B.actualBandSchurLinearMap xi hγ hgap) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    have h := hcore q
    rw [hq, map_zero, norm_zero, mul_zero] at h
    have h0 : S.symm q = 0 := norm_le_zero_iff.mp h
    have := congrArg S h0
    rwa [S.apply_symm_apply, map_zero] at this
  let e := LinearEquiv.ofInjectiveEndo (B.actualBandSchurLinearMap xi hγ hgap) hinj
  have he : ∀ q, e q = B.actualBandSchurLinearMap xi hγ hgap q := fun q => rfl
  have hbound : ∀ v, ‖S.symm (e.symm v)‖ ≤
      Cfull / (1 - Cfull * (2 * B.nuisanceMarkedSchurRate ε γ amin)) * ‖S.symm v‖ := by
    intro v
    have h := hcore (e.symm v)
    rwa [← he, e.apply_symm_apply] at h
  have hrate0 : 0 ≤ B.nuisanceMarkedSchurRate ε γ amin := rate_nonneg B ε γ amin hε hγ hamin
  have hCs : 0 < Cfull / (1 - Cfull * (2 * B.nuisanceMarkedSchurRate ε γ amin)) :=
    div_pos hC (by linarith)
  refine ⟨e, he, hbound, ?_⟩
  intro q
  exact quad B hα xi hγ hgap _ hCs hcore (fun q => ⟨e.symm q, by rw [← he, e.apply_symm_apply]⟩) q

end Final

end C1d397

set_option maxHeartbeats 4000000 in
open Erdos390.Full in
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
  intro Head Band _ _ _ _ _ _ I U hU hlowerOne hupperU W hW a mf cs Cfull hmf hcs hC ε hε hlim
  have hg0 := C1d397.gamma0_pos I U a W mf hmf (Fintype.card Head)
  set g0 := C1d397.gamma0 I U a W mf (Fintype.card Head) with hg0def
  set δ : ℝ := g0 * cs / (8 * ((Fintype.card Head : ℝ) + 1) * Cfull) with hδdef
  have hδ : 0 < δ := by positivity
  have ev1 : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ Real.log (Erdos390.Full.Scale.L n) := by
    have h : Filter.Tendsto (fun n : ℕ => Real.log (Erdos390.Full.Scale.L n)) Filter.atTop
        Filter.atTop := by
      unfold Erdos390.Full.Scale.L
      exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    exact h.eventually_ge_atTop 1
  have ev2 : ∀ᶠ n : ℕ in Filter.atTop, (4 : ℝ) ≤ Erdos390.Full.ArithmeticModel.y n := by
    have h : Filter.Tendsto (fun n : ℕ => Erdos390.Full.ArithmeticModel.y n) Filter.atTop
        Filter.atTop := by
      unfold Erdos390.Full.ArithmeticModel.y
      exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp tendsto_natCast_atTop_atTop
    exact h.eventually_ge_atTop 4
  have ev3 : ∀ᶠ n : ℕ in Filter.atTop, (ε n * Real.log (Erdos390.Full.Scale.L n)) ^ 2 < δ := by
    have h := hlim.pow 2
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
    exact h.eventually (gt_mem_nhds hδ)
  filter_upwards [ev1, ev2, ev3] with n h1 h2 h3
  intro B hBn hBW T hmfT hbaseline hlo hhi fullEquiv hfull hinv hcent hcov
  subst hBn
  intro gamma rate Cschur
  have hα : ∀ j, B.bandCenter j ≠ 0 := fun j => (B.bandCenter_pos j).ne'
  have hγ : 0 < gamma := B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
  have hγlow : g0 ≤ gamma := C1d397.gamma_lower B I a W hBW T mf hmf hmfT
  have hM : ∑ k, B.harmonicMass k * B.bandCenter k ≤ 2 := by
    rw [C1d397.moment_eq]; exact C1d397.moment_le _ _ h2
  have hrate : rate ≤ 2 * ((Fintype.card Head : ℝ) + 1) *
      (ε B.sampleData.n * Real.log (Erdos390.Full.Scale.L B.sampleData.n)) ^ 2 / (g0 * cs) :=
    C1d397.rate_le B (ε _) gamma g0 cs (Real.log (Erdos390.Full.Scale.L _)) (hε _) hg0 hγlow hcs h1 hM
  have hK : (0 : ℝ) < (Fintype.card Head : ℝ) + 1 := by positivity
  have hκ : Cfull * (2 * rate) ≤ 1 / 2 := by
    have hX := h3.le
    have hb : 2 * ((Fintype.card Head : ℝ) + 1) *
        (ε B.sampleData.n * Real.log (Erdos390.Full.Scale.L B.sampleData.n)) ^ 2 / (g0 * cs) ≤
        1 / (4 * Cfull) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      rw [hδdef, le_div_iff₀ (by positivity)] at hX
      nlinarith
    have : rate ≤ 1 / (4 * Cfull) := hrate.trans hb
    have h4 : Cfull * (1 / (4 * Cfull)) = 1 / 4 := by field_simp
    nlinarith
  have hamin : 0 < cs / Real.log (Erdos390.Full.Scale.L B.sampleData.n) := div_pos hcs (by linarith)
  have hW1 : 1 < B.sampleData.W := hBW ▸ hW
  have key := fun (z : B.EffectiveParamSpace)
      (hz : z ∈ Metric.closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) =>
    C1d397.perz B hα (B.effectiveParamEquiv z) hγ
      (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU hlowerOne hupperU hlo hhi T hbaseline
        hW1 z hz)
      (ε B.sampleData.n) (cs / Real.log (Erdos390.Full.Scale.L B.sampleData.n)) (hε _) hamin hcent
      (hcov z hz) Cfull hC (fullEquiv z hz) (hfull z hz) (hinv z hz) hκ
  choose e he1 he2 he3 using key
  refine ⟨e, he1, he2, ?_, he3⟩
  show Cfull / (1 - Cfull * (2 * rate)) ≤ 2 * Cfull
  rw [div_le_iff₀ (by linarith)]
  nlinarith
