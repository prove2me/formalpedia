-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceResidual_bandRegression_markedRow_le_of_profiles
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:52:21.956195+00:00
-- url     : https://prove2.me/submissions/c3e4c961-0987-4179-a2a4-d4f58c906018

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
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_bandReferenceMarkedRow_le_product
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_bandSquarefreeRegression_sub_reference_marked_le
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

















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperExactTwoStageOrdinaryFast -/
section


/-!
# Ordinary-fast / sharp-slow form of the exact two-stage solve

The fast target in Proposition 8.7 is bounded in the ordinary raw-band
supremum norm: its unprojected coordinates are
`(L / q) * Delta_j / H_j = O(1)`.  They are not, in general, bounded after
division by the moving centre `alpha_j`; in particular `alpha_0 -> 0`.

The slow regression is different.  Lemma 8.5 supplies a sharp inverse for
that right-hand side and hence a regression vector of size `O(w alpha_j)`.
This file records the exact finite algebra with those two norms kept
separate.  It is the norm-correct form of the block calculation in the
proof of Proposition 8.7.
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















/-- A reciprocal marked family controls an ordinary-bounded raw band score.
Unlike the sharp version, its finite factor is `sum_j H_j`; this is exactly
the `O(log L / L)` nuisance coefficient used for the fast target in the
paper. -/
theorem nuisanceCovarianceVector_rawBandRegression_norm_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace)
    {Cmarked : ℝ} (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (q : B.RawBandGauge) :
    ‖B.nuisanceCovarianceVector xi (B.bandRegressionScore q)‖ ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        ((Cmarked * ∑ j : Band, B.harmonicMass j) * ‖q‖) := by
  have hmass : 0 ≤ ∑ j : Band, B.harmonicMass j := by
    apply Finset.sum_nonneg
    intro j hj
    exact (B.harmonicMass_pos j).le
  have hK : 0 ≤ (Cmarked * ∑ j : Band, B.harmonicMass j) * ‖q‖ :=
    mul_nonneg (mul_nonneg hCmarked hmass) (norm_nonneg q)
  apply B.nuisanceCovarianceVector_norm_le_sqrt_card_mul
    xi (B.bandRegressionScore q) hK
  intro c
  let mu := B.tiltedLaw xi
  let Z : B.sampleData.Sample → ℝ :=
    fun m ↦ B.nuisanceStatistic m c
  have hsum :
      mu.covariance Z (B.bandRegressionScore q) =
        ∑ j : Band, q.1 j * mu.covariance Z (B.bandScore j) := by
    unfold bandRegressionScore
    rw [show (fun m ↦ ∑ j : Band, q.1 j * B.bandScore j m) =
      fun m ↦ ∑ j ∈ (Finset.univ : Finset Band),
        q.1 j * B.bandScore j m by simp]
    rw [mu.covariance_sum_right]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mu.covariance_smul_right]
  change |mu.covariance Z (B.bandRegressionScore q)| ≤ _
  rw [hsum]
  calc
    |∑ j : Band, q.1 j * mu.covariance Z (B.bandScore j)| ≤
        ∑ j : Band, |q.1 j * mu.covariance Z (B.bandScore j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Band, ‖q‖ * (Cmarked * B.harmonicMass j) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      have hq : |q.1 j| ≤ ‖q‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm q.1 j
      exact mul_le_mul hq
        (B.abs_covariance_nuisance_bandScore_le_of_marked
          xi c j (fun p ↦ hmarked c p))
        (abs_nonneg _) (norm_nonneg q)
    _ = (Cmarked * ∑ j : Band, B.harmonicMass j) * ‖q‖ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring



















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualSquarefreeMarkedRow -/
section


/-!
# The squarefree marked row at the paper's relative scale

This file records the finite row calculation used in Lemma 8.6 and
Proposition 8.7.  A signed product-reciprocal comparison with the
Poisson--Dickman reference matrix is summed against the literal compensated
coefficient.  The result is pointwise in the marked prime and therefore does
not follow from a band-averaged operator estimate.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerRelativeQuadratic
open PaperWeightedInverseExport
open SquarefreeCovarianceReference

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)









/-- The canonical signed one- and two-divisor profiles give the literal
actual-law entry comparison.  The equality between the sigma mixture and the
global guarded tilted law keeps all between-cell covariance terms. -/
theorem actualSquarefreeEntry_bound_of_profiles [Nonempty Head]
    (xi : B.ParamSpace) {Eprofile CKernel : ℝ}
    (hEprofile : 0 ≤ Eprofile)
    (hpair : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (OmittedTiltPairChamber.pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (OmittedTiltPairChamber.pairPower p r 1 1)| ≤
        Eprofile * PaperPrimePowerChamberError.pairWeight p r 1 1)
    (hsingle : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
          Eprofile * PaperPrimePowerChamberError.singleWeight p 1)
    (hKernelDiag : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤ CKernel) :
    ∀ p r,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      r ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualValuationLaw xi).covII p r -
          squarefreeReferenceEntry B.sampleData.n p r| ≤
        (4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
            (1 / (p : ℝ)) * (1 / (r : ℝ)) +
          if p = r then
            (2 * Eprofile) * (1 / (p : ℝ)) +
              ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
                CKernel) * (1 / (p : ℝ)) ^ 2
          else 0 := by
  let weight := tiltedSigmaWeight B.baselineCellProbability
    B.guardedCellProbability (B.scaledBridgeScore xi)
  have hraw :=
    SquarefreeCovarianceReference.sigmaMixture_squarefree_reference_entry_bound_of_squarefree_profiles
      hEprofile weight (B.actualComponentValuationLaw xi) B.n_gt_one
      hpair hsingle hKernelDiag
  have hlaw := B.sigmaMixture_actualComponentValuationLaw_eq_actualValuationLaw xi
  dsimp only at hlaw
  rw [hlaw] at hraw
  intro p r hp hr
  have h := hraw ⟨p, hp⟩ ⟨r, hr⟩
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (prime_of_mem_primeBand hp).ne_zero
  have hr0 : (r : ℝ) ≠ 0 := by
    exact_mod_cast (prime_of_mem_primeBand hr).ne_zero
  by_cases hpr : p = r
  · subst r
    convert h using 1
    field_simp [hp0]
  · have hsub : (⟨p, hp⟩ : BandPrime B.sampleData.n B.sampleData.W) ≠
        ⟨r, hr⟩ := by
      intro heq
      exact hpr (congrArg Subtype.val heq)
    simp only [if_neg hsub] at h
    convert h using 1
    simp only [if_neg hpr]
    field_simp [hp0, hr0]



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualFastMarkedRowProfiles -/
section


/-!
# Ordinary-fast marked rows from the literal analytic inputs

The fast solve is bounded in the ordinary raw-band norm.  Its reference
kernel row is nevertheless `O(1/p)`: the product bound for the Dickman
kernel supplies the missing factor `t_r`, whose prime sum is bounded.  Only
the signed profile error pays the full harmonic mass, exactly as in the
paper's `epsilon(n) log L -> 0` bookkeeping.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PaperWeightedInverseExport
open SquarefreeCovarianceReference

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



theorem bandRegression_markedRows_eq_sums [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge) (p : ℕ) :
    (B.tiltedLaw xi).covariance
        (fun m ↦ valuation p (B.sampleData.value m))
        (B.bandRegressionScore q) =
      ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          (B.actualValuationLaw xi).covVV p r.1 ∧
    (B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.bandSquarefreeRegressionScore q) =
      ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          (B.actualValuationLaw xi).covII p r.1 := by
  constructor
  · have hscore : B.bandRegressionScore q =
        fun m ↦ ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          q.1 (B.partition.band r) *
            valuation r.1 (B.sampleData.value m) := by
      funext m
      exact B.bandRegressionScore_eq_primeSum q m
    rw [hscore]
    rw [(B.tiltedLaw xi).covariance_sum_right]
    apply Finset.sum_congr rfl
    intro r hr
    rw [(B.tiltedLaw xi).covariance_smul_right]
    rfl
  · unfold bandSquarefreeRegressionScore
    rw [(B.tiltedLaw xi).covariance_sum_right]
    apply Finset.sum_congr rfl
    intro r hr
    rw [(B.tiltedLaw xi).covariance_smul_right]
    rfl

/-- The full-versus-squarefree weighted row applies to an ordinary raw-band
coefficient without any moving-centre loss. -/
theorem bandRegression_full_sub_squarefree_marked_le_of_weightedRow
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge) {R : ℝ}
    (hrow : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      (r.1 : ℝ) *
        ∑ s : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV r.1 s.1 -
            (B.actualValuationLaw xi).covII r.1 s.1| ≤ R)
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    |(B.tiltedLaw xi).covariance
        (fun m ↦ valuation p (B.sampleData.value m))
        (B.bandRegressionScore q) -
      (B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.bandSquarefreeRegressionScore q)| ≤
      ‖q‖ * R * (1 / (p : ℝ)) := by
  rw [(B.bandRegression_markedRows_eq_sums xi q p).1,
    (B.bandRegression_markedRows_eq_sums xi q p).2]
  rw [← Finset.sum_sub_distrib]
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (prime_of_mem_primeBand hp).pos
  have hrowp := hrow ⟨p, hp⟩
  calc
    |∑ r : BandPrime B.sampleData.n B.sampleData.W,
        (q.1 (B.partition.band r) *
            (B.actualValuationLaw xi).covVV p r.1 -
          q.1 (B.partition.band r) *
            (B.actualValuationLaw xi).covII p r.1)| =
      |∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          ((B.actualValuationLaw xi).covVV p r.1 -
            (B.actualValuationLaw xi).covII p r.1)| := by
        congr 1
        apply Finset.sum_congr rfl
        intro r hr
        ring
    _ ≤ ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        |q.1 (B.partition.band r)| *
          |(B.actualValuationLaw xi).covVV p r.1 -
            (B.actualValuationLaw xi).covII p r.1| := by
      calc
        _ ≤ ∑ r : BandPrime B.sampleData.n B.sampleData.W,
            |q.1 (B.partition.band r) *
              ((B.actualValuationLaw xi).covVV p r.1 -
                (B.actualValuationLaw xi).covII p r.1)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by simp only [abs_mul]
    _ ≤ ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        ‖q‖ * |(B.actualValuationLaw xi).covVV p r.1 -
          (B.actualValuationLaw xi).covII p r.1| := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_right
        (by simpa only [Real.norm_eq_abs] using
          (norm_le_pi_norm q.1 (B.partition.band r))) (abs_nonneg _)
    _ = ‖q‖ * ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        |(B.actualValuationLaw xi).covVV p r.1 -
          (B.actualValuationLaw xi).covII p r.1| := by rw [Finset.mul_sum]
    _ ≤ ‖q‖ * (R / (p : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg q)
      exact (le_div_iff₀ hpR).2 (by simpa only [mul_comm] using hrowp)
    _ = ‖q‖ * R * (1 / (p : ℝ)) := by ring





/-- Full nuisance-residual fast marked row.  Every term on the right is a
literal finite conclusion; there is no assumed fast or vector-field row. -/
theorem nuisanceResidual_bandRegression_markedRow_le_of_profiles
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge)
    {H K Eprofile CF Cprod R Cmarked : ℝ}
    (hH0 : 0 ≤ H) (hCmarked : 0 ≤ Cmarked)
    (hEprofile : 0 ≤ Eprofile)
    (hCprod : 0 ≤ Cprod)
    (hW : 0 < B.sampleData.W)
    (hH : (∑ j : Band, B.harmonicMass j) ≤ H)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hpair : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (OmittedTiltPairChamber.pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (OmittedTiltPairChamber.pairPower p r 1 1)| ≤
        Eprofile * PaperPrimePowerChamberError.pairWeight p r 1 1)
    (hsingle : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
          Eprofile * PaperPrimePowerChamberError.singleWeight p 1)
    (hF : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |DickmanBasic.F (tPrime B.sampleData.n r.1)| ≤ CF)
    (hKernelProduct : ∀ r s : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n r.1)
          (tPrime B.sampleData.n s.1)| ≤
        Cprod * tPrime B.sampleData.n r.1 * tPrime B.sampleData.n s.1)
    (hrow : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      (r.1 : ℝ) *
        ∑ s : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV r.1 s.1 -
            (B.actualValuationLaw xi).covII r.1 s.1| ≤ R)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (r : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation r.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (r.1 : ℝ)))
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    |(B.tiltedLaw xi).covariance
        (fun m ↦ valuation p (B.sampleData.value m))
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q))| ≤
      ((Cprod * K + CF) +
          ((4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
              H + 2 * Eprofile +
            ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
              Cprod) * (1 / (B.sampleData.W : ℝ))) + R +
          (((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
                (Cmarked * H)) / gamma) *
            (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
              Cmarked))) * ‖q‖ * (1 / (p : ℝ)) := by
  have hentry := B.actualSquarefreeEntry_bound_of_profiles xi hEprofile
    hpair hsingle (fun r hr ↦ by
      have ht0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand
        B.n_gt_one hr
      have ht1 := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
        B.n_gt_one hr
      have hk := hKernelProduct ⟨r, hr⟩ ⟨r, hr⟩
      calc
        _ ≤ Cprod * tPrime B.sampleData.n r * tPrime B.sampleData.n r := hk
        _ ≤ Cprod := by
          nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1), hCprod])
  have hsfDiff := B.bandSquarefreeRegression_sub_reference_marked_le
    xi q
    (mul_nonneg (by norm_num)
      (PaperPrimePowerChamberError.pairCovarianceScale_nonneg hEprofile))
    hH hentry hp
  have href := B.bandReferenceMarkedRow_le_product q hCprod
    hbandT hF hKernelProduct hp
  have hpow := B.bandRegression_full_sub_squarefree_marked_le_of_weightedRow
    xi q hrow hp
  let full := (B.tiltedLaw xi).covariance
    (fun m ↦ valuation p (B.sampleData.value m))
    (B.bandRegressionScore q)
  let squarefree := (B.tiltedLaw xi).covariance
    (fun m ↦ divInd p (B.sampleData.value m))
    (B.bandSquarefreeRegressionScore q)
  let reference := ∑ r : BandPrime B.sampleData.n B.sampleData.W,
    q.1 (B.partition.band r) *
      squarefreeReferenceEntry B.sampleData.n p r.1
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (prime_of_mem_primeBand hp).pos
  have hWR : (0 : ℝ) < B.sampleData.W := by exact_mod_cast hW
  have hWp : (B.sampleData.W : ℝ) ≤ p := by
    exact_mod_cast (cutoff_lt_of_mem_primeBand hp).le
  have hinv : 1 / (p : ℝ) ≤ 1 / (B.sampleData.W : ℝ) :=
    one_div_le_one_div_of_le hWR hWp
  let second :=
    (1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 + Cprod
  have hsecond : 0 ≤ second := by
    dsimp only [second]
    exact add_nonneg (sq_nonneg _) hCprod
  have hsfDiff' : |squarefree - reference| ≤
      ‖q‖ * ((4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
          H + 2 * Eprofile + second * (1 / (B.sampleData.W : ℝ))) *
        (1 / (p : ℝ)) := by
    have hraw : |squarefree - reference| ≤
        ‖q‖ * ((4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
            H + 2 * Eprofile + second * (1 / (p : ℝ))) *
          (1 / (p : ℝ)) := by
      simpa only [squarefree, reference, second] using hsfDiff
    have hinside :
        (4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) * H +
            2 * Eprofile + second * (1 / (p : ℝ)) ≤
          (4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) * H +
            2 * Eprofile + second * (1 / (B.sampleData.W : ℝ)) := by
      gcongr
    exact hraw.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hinside (norm_nonneg q))
      (one_div_nonneg.mpr hpR.le))
  have hfull : |full| ≤
      ‖q‖ * ((Cprod * K + CF) +
        ((4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
            H + 2 * Eprofile + second * (1 / (B.sampleData.W : ℝ))) + R) *
          (1 / (p : ℝ)) := by
    have htriangle : |full| ≤
        |full - squarefree| + |squarefree - reference| + |reference| := by
      calc
        |full| = |(full - squarefree) + (squarefree - reference) + reference| :=
          by ring_nf
        _ ≤ |full - squarefree| + |squarefree - reference| + |reference| :=
          (abs_add_three _ _ _)
    calc
      _ ≤ |full - squarefree| + |squarefree - reference| + |reference| :=
        htriangle
      _ ≤ ‖q‖ * R * (1 / (p : ℝ)) +
          ‖q‖ * ((4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
            H + 2 * Eprofile + second * (1 / (B.sampleData.W : ℝ))) *
              (1 / (p : ℝ)) +
          ‖q‖ * (Cprod * K + CF) * (1 / (p : ℝ)) :=
        add_le_add (add_le_add (by simpa only [full, squarefree] using hpow)
          hsfDiff') (by simpa only [reference] using href)
      _ = _ := by ring
  have hsource := B.nuisanceCovarianceVector_rawBandRegression_norm_le_of_marked
    xi hCmarked hmarked q
  have hmarkedCoord : ∀ c : NuisanceCoord B.HeadIndex,
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p (B.sampleData.value m))| ≤
          Cmarked * (1 / (p : ℝ)) := fun c ↦ hmarked c ⟨p, hp⟩
  have hmarkedZ : ‖B.nuisanceCovarianceVector xi
      (fun m ↦ valuation p (B.sampleData.value m))‖ ≤
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        Cmarked) * (1 / (p : ℝ)) := by
    have hraw := B.nuisanceCovarianceVector_norm_le_sqrt_card_mul
      xi (fun m ↦ valuation p (B.sampleData.value m))
      (mul_nonneg hCmarked (one_div_nonneg.mpr hpR.le)) hmarkedCoord
    simpa only [mul_assoc] using hraw
  let d : ℝ := Real.sqrt
    (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  let Cz : ℝ := d * (Cmarked * H)
  let Crow : ℝ := d * Cmarked
  have hsourceH : ‖B.nuisanceCovarianceVector xi
      (B.bandRegressionScore q)‖ ≤ Cz * ‖q‖ := by
    calc
      _ ≤ d * ((Cmarked * ∑ j : Band, B.harmonicMass j) * ‖q‖) := by
        simpa only [d] using hsource
      _ ≤ d * ((Cmarked * H) * ‖q‖) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg q)
        exact mul_le_mul_of_nonneg_left hH hCmarked
      _ = Cz * ‖q‖ := by simp only [Cz]; ring
  have hCz : 0 ≤ Cz := by
    dsimp only [Cz, d]
    positivity
  let a := B.nuisanceCoefficientOfScore xi hgamma hgap
    (B.bandRegressionScore q)
  have ha : ‖a‖ ≤ (Cz / gamma) * ‖q‖ := by
    calc
      ‖a‖ ≤ ‖B.nuisanceCovarianceVector xi
          (B.bandRegressionScore q)‖ / gamma :=
        B.nuisanceCoefficientOfScore_norm_le xi hgamma hgap _
      _ ≤ (Cz * ‖q‖) / gamma :=
        div_le_div_of_nonneg_right hsourceH hgamma.le
      _ = (Cz / gamma) * ‖q‖ := by ring
  have hnuisance :
      |(B.tiltedLaw xi).covariance
        (fun m ↦ valuation p (B.sampleData.value m))
        (fun m ↦ inner ℝ a (B.nuisanceStatistic m))| ≤
      ((Cz / gamma) * Crow) * ‖q‖ * (1 / (p : ℝ)) := by
    rw [B.covariance_marked_nuisanceScore_eq_inner]
    calc
      |inner ℝ a (B.nuisanceCovarianceVector xi
          (fun m ↦ valuation p (B.sampleData.value m)))| ≤
        ‖a‖ * ‖B.nuisanceCovarianceVector xi
          (fun m ↦ valuation p (B.sampleData.value m))‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ ((Cz / gamma) * ‖q‖) *
          (Crow * (1 / (p : ℝ))) := by
        exact mul_le_mul ha (by simpa only [Crow, d] using hmarkedZ)
          (norm_nonneg _) (mul_nonneg (div_nonneg hCz hgamma.le)
            (norm_nonneg q))
      _ = _ := by ring
  have hdecomp :
      (B.tiltedLaw xi).covariance
          (fun m ↦ valuation p (B.sampleData.value m))
          (B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore q)) = full -
        (B.tiltedLaw xi).covariance
          (fun m ↦ valuation p (B.sampleData.value m))
          (fun m ↦ inner ℝ
            (B.nuisanceCoefficientOfScore xi hgamma hgap
              (B.bandRegressionScore q))
            (B.nuisanceStatistic m)) := by
    unfold nuisanceResidualScore
    have hfun :
        (fun m ↦ B.bandRegressionScore q m -
          inner ℝ a (B.nuisanceStatistic m)) =
        fun m ↦ B.bandRegressionScore q m + (-1 : ℝ) *
          inner ℝ a (B.nuisanceStatistic m) := by
      funext m
      ring
    rw [hfun, (B.tiltedLaw xi).covariance_add_right,
      (B.tiltedLaw xi).covariance_smul_right]
    dsimp only [a]
    ring
  rw [hdecomp]
  calc
    |full - (B.tiltedLaw xi).covariance
        (fun m ↦ valuation p (B.sampleData.value m))
        (fun m ↦ inner ℝ
          (B.nuisanceCoefficientOfScore xi hgamma hgap
            (B.bandRegressionScore q))
          (B.nuisanceStatistic m))| ≤
      |full| + |(B.tiltedLaw xi).covariance
        (fun m ↦ valuation p (B.sampleData.value m))
        (fun m ↦ inner ℝ
          (B.nuisanceCoefficientOfScore xi hgamma hgap
            (B.bandRegressionScore q))
          (B.nuisanceStatistic m))| := abs_sub _ _
    _ ≤ ‖q‖ * ((Cprod * K + CF) +
          ((4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
              H + 2 * Eprofile + second * (1 / (B.sampleData.W : ℝ))) + R) *
            (1 / (p : ℝ)) +
        (((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
              (Cmarked * H)) / gamma) *
          (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            Cmarked)) * ‖q‖ * (1 / (p : ℝ)) :=
      add_le_add hfull hnuisance
    _ = _ := by dsimp only [second, Cz, Crow, d]; ring

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B) {gamma : Real}
  (hgamma : LT.lt.{0} (0 : Real) gamma)
  (hgap :
    ∀ (z : Erdos390.Full.PaperBridgeFit.BridgeData.NuisanceSpace.{u_1, u_2} B),
      LE.le.{0} (HMul.hMul.{0, 0, 0} gamma (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} z) (2 : Nat)))
        (Inner.inner.{0, u_1} Real z
          ((Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceCovarianceOperator.{u_1, u_2} B xi :
              Erdos390.Full.PaperBridgeFit.BridgeData.NuisanceSpace.{u_1, u_2} B →
                Erdos390.Full.PaperBridgeFit.BridgeData.NuisanceSpace.{u_1, u_2} B)
            z)))
  (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)) {H K Eprofile CF Cprod R Cmarked : Real},
  LE.le.{0} (0 : Real) H →
    LE.le.{0} (0 : Real) Cmarked →
      LE.le.{0} (0 : Real) Eprofile →
        LE.le.{0} (0 : Real) Cprod →
          LT.lt.{0} (0 : Nat)
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) →
            LE.le.{0} (∑ j : Band, Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2} B j) H →
              LE.le.{0}
                  (Erdos390.Full.PrimeSums.bandTReciprocalSum
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                  K →
                (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) (p : Nat),
                    Membership.mem.{0, 0}
                        (Erdos390.Full.ArithmeticModel.primeBand
                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                        p →
                      ∀ (r : Nat),
                        Membership.mem.{0, 0}
                            (Finset.erase.{0}
                              (Erdos390.Full.ArithmeticModel.primeBand
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                              p)
                            r →
                          LE.le.{0}
                            (abs.{0}
                              (HSub.hSub.{0, 0, 0}
                                (Erdos390.Full.FiniteProbability.expect.{0}
                                  (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{0}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1, u_2} B xi
                                      c))
                                  fun
                                    (omega :
                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) c) =>
                                  Erdos390.Full.ArithmeticModel.divInd
                                    (Erdos390.Full.OmittedTiltPairChamber.pairPower p r (1 : Nat) (1 : Nat))
                                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{0}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1, u_2} B
                                        xi c)
                                      omega))
                                (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                  (Erdos390.Full.OmittedTiltPairChamber.pairPower p r (1 : Nat) (1 : Nat)))))
                            (HMul.hMul.{0, 0, 0} Eprofile
                              (Erdos390.Full.PaperPrimePowerChamberError.pairWeight p r (1 : Nat) (1 : Nat)))) →
                  (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) (p : Nat),
                      Membership.mem.{0, 0}
                          (Erdos390.Full.ArithmeticModel.primeBand
                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                          p →
                        LE.le.{0}
                          (abs.{0}
                            (HSub.hSub.{0, 0, 0}
                              (Erdos390.Full.FiniteProbability.expect.{0}
                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{0}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1, u_2} B xi
                                    c))
                                fun
                                  (omega :
                                    Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) c) =>
                                Erdos390.Full.ArithmeticModel.divInd p
                                  (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{0}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1, u_2} B xi
                                      c)
                                    omega))
                              (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                p)))
                          (HMul.hMul.{0, 0, 0} Eprofile
                            (Erdos390.Full.PaperPrimePowerChamberError.singleWeight p (1 : Nat)))) →
                    (∀
                        (r :
                          Erdos390.Full.ArithmeticBandGeometry.BandPrime
                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                        LE.le.{0}
                          (abs.{0}
                            (Erdos390.Full.DickmanBasic.F
                              (Erdos390.Full.ArithmeticModel.tPrime
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                (↑r : Nat))))
                          CF) →
                      (∀
                          (r s :
                            Erdos390.Full.ArithmeticBandGeometry.BandPrime
                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                          LE.le.{0}
                            (abs.{0}
                              (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel
                                (Erdos390.Full.ArithmeticModel.tPrime
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                  (↑r : Nat))
                                (Erdos390.Full.ArithmeticModel.tPrime
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                  (↑s : Nat))))
                            (HMul.hMul.{0, 0, 0}
                              (HMul.hMul.{0, 0, 0} Cprod
                                (Erdos390.Full.ArithmeticModel.tPrime
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                  (↑r : Nat)))
                              (Erdos390.Full.ArithmeticModel.tPrime
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                (↑s : Nat)))) →
                        (∀
                            (r :
                              Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                            LE.le.{0}
                              (HMul.hMul.{0, 0, 0} (↑(↑r : Nat) : Real)
                                (∑ s :
                                  Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
                                  abs.{0}
                                    (HSub.hSub.{0, 0, 0}
                                      (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_1}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B xi)
                                        (↑r : Nat) (↑s : Nat))
                                      (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B xi)
                                        (↑r : Nat) (↑s : Nat)))))
                              R) →
                          (∀
                              (c :
                                Erdos390.Full.PaperBridgeFit.NuisanceCoord.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1, u_2} B))
                              (r :
                                Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                              LE.le.{0}
                                (abs.{0}
                                  (Erdos390.Full.FiniteProbability.covariance.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.tiltedLaw.{u_1, u_2} B xi)
                                    (fun
                                        (m :
                                          Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) =>
                                      WithLp.ofLp.{u_1}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceStatistic.{u_1, u_2} B m) c)
                                    fun
                                      (m :
                                        Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) =>
                                    Erdos390.Full.ArithmeticModel.valuation (↑r : Nat)
                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{u_1}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) m)))
                                (HMul.hMul.{0, 0, 0} Cmarked (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑(↑r : Nat) : Real)))) →
                            ∀ {p : Nat},
                              Membership.mem.{0, 0}
                                  (Erdos390.Full.ArithmeticModel.primeBand
                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                  p →
                                LE.le.{0}
                                  (abs.{0}
                                    (Erdos390.Full.FiniteProbability.covariance.{u_1}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.tiltedLaw.{u_1, u_2} B xi)
                                      (fun
                                          (m :
                                            Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) =>
                                        Erdos390.Full.ArithmeticModel.valuation p
                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{u_1}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) m))
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceResidualScore.{u_1, u_2} B xi
                                        hgamma hgap
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.bandRegressionScore.{u_1, u_2} B q))))
                                  (HMul.hMul.{0, 0, 0}
                                    (HMul.hMul.{0, 0, 0}
                                      (HAdd.hAdd.{0, 0, 0}
                                        (HAdd.hAdd.{0, 0, 0}
                                          (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} Cprod K) CF)
                                            (HAdd.hAdd.{0, 0, 0}
                                              (HAdd.hAdd.{0, 0, 0}
                                                (HMul.hMul.{0, 0, 0}
                                                  (HMul.hMul.{0, 0, 0} (4 : Real)
                                                    (Erdos390.Full.PaperPrimePowerChamberError.pairCovarianceScale
                                                      Eprofile))
                                                  H)
                                                (HMul.hMul.{0, 0, 0} (2 : Real) Eprofile))
                                              (HMul.hMul.{0, 0, 0}
                                                (HAdd.hAdd.{0, 0, 0}
                                                  (HPow.hPow.{0, 0, 0}
                                                    (HAdd.hAdd.{0, 0, 0}
                                                      (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                        (Erdos390.Full.DickmanBasic.rho Erdos390.Full.DickmanBasic.U))
                                                      (HMul.hMul.{0, 0, 0} (2 : Real) Eprofile))
                                                    (2 : Nat))
                                                  Cprod)
                                                (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                  (↑(Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                          B)) :
                                                    Real)))))
                                          R)
                                        (HMul.hMul.{0, 0, 0}
                                          (HDiv.hDiv.{0, 0, 0}
                                            (HMul.hMul.{0, 0, 0}
                                              (Real.sqrt
                                                (↑(Fintype.card.{u_1}
                                                      (Erdos390.Full.PaperBridgeFit.NuisanceCoord.{u_1}
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1, u_2}
                                                          B))) :
                                                  Real))
                                              (HMul.hMul.{0, 0, 0} Cmarked H))
                                            gamma)
                                          (HMul.hMul.{0, 0, 0}
                                            (Real.sqrt
                                              (↑(Fintype.card.{u_1}
                                                    (Erdos390.Full.PaperBridgeFit.NuisanceCoord.{u_1}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1, u_2}
                                                        B))) :
                                                Real))
                                            Cmarked)))
                                      (Norm.norm.{u_2} q))
                                    (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑p : Real))) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceResidual_bandRegression_markedRow_le_of_profiles
