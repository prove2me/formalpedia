-- Prove2me | Definitions.Def_erdos390_analytic_foundations_005
-- name    : erdos390_analytic_foundations_005
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-17T14:53:58.17891+00:00
-- url     : https://prove2.me/theorems/85b79f5c-0fed-4594-be5c-66415cfcc77f
-- title:
--   Two-stage regression and the quantitative Proposition 8.7 interfaces
-- statement:
--   This bundle defines the actual two-stage band/nuisance regression scores and coordinate maps, squarefree and full valuation quadratic forms, anchored graph energies, endpoint-mesh error quantities, power-correction and marked-row majorants, and the canonical path/conclusion predicates for Proposition 8.7. It also supplies finite head-simplex reserves and physical interpolation target constructors.
--
--   For finite indices $i$, weights $w_i$, diagonal coefficients $d_i$ and a signed kernel $k_{ij}$, the reference quadratic and associated Dirichlet expression are
--   $$Q(x)=\sum_iw_id_ix_i^2+\sum_{i,j}w_iw_jk_{ij}x_ix_j,\qquad \mathcal E(x)=\frac12\sum_{i,j}w_iw_j(-k_{ij})(x_i-x_j)^2.$$
--   The corresponding row residual is $d_i+\sum_jw_jk_{ij}$. Actual compensated scores are formed by applying nuisance compensation to the band-regressed score, using the covariance-gap and inverse data supplied to the constructors.
--
--   The many named constants and cutoffs organize the uniform analytic estimates, while the path predicates specify the exact physical, head, band, logarithmic and feasibility requirements. Defining those predicates does not assert their existence for arbitrary data; the separate assembly theorems provide the required implications.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperActualTwoStageRegression.lean; grouped definitions extracted from multiple source modules at this commit, including Erdos390.Full.PaperActualPrimePowerRelative, Erdos390.Full.PaperActualTwoStageRegression, Erdos390.Full.PaperVectorFieldSchur, with the remaining originating modules identified by source-module comments in the definition body.

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004


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

/-- One literal finite endpoint for both physical pools. -/
def sampleEndpoint : ℕ :=
  max (B.sampleData.hi .minus) (B.sampleData.hi .plus)

theorem sample_value_le_endpoint (m : B.sampleData.Sample) :
    B.sampleData.value m ≤ B.sampleEndpoint := by
  have hvalue := B.sampleData.value_le_hi m
  cases hsign : (B.sampleData.cellOf m).2 with
  | minus =>
      have hvalue' : B.sampleData.value m ≤ B.sampleData.hi .minus := by
        simpa only [hsign] using hvalue
      exact hvalue'.trans (Nat.le_max_left _ _)
  | plus =>
      have hvalue' : B.sampleData.value m ≤ B.sampleData.hi .plus := by
        simpa only [hsign] using hvalue
      exact hvalue'.trans (Nat.le_max_right _ _)

/-- The actual tilted bounded valuation law used by Lemmas 7.5 and 8.6. -/
def actualValuationLaw [Nonempty Head] (xi : B.ParamSpace) :
    BoundedValuationLaw B.sampleData.Sample B.sampleEndpoint where
  probability := B.tiltedLaw xi
  value := B.sampleData.value
  value_pos := B.sampleData.value_pos
  value_le := B.sample_value_le_endpoint

/-- Extend the literal subtype coefficient by zero outside the actual prime
band.  Every quadratic form below immediately restricts it back to the band. -/
def actualCompensatedNatCoefficient
    (q : B.RawBandGauge) (p : ℕ) : ℝ :=
  if hp : p ∈ primeBand B.sampleData.n B.sampleData.W then
    B.actualCompensatedCoefficient q ⟨p, hp⟩
  else 0

@[simp]
theorem actualCompensatedNatCoefficient_of_mem
    (q : B.RawBandGauge) {p : ℕ}
    (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    B.actualCompensatedNatCoefficient q p =
      B.actualCompensatedCoefficient q ⟨p, hp⟩ := by
  simp only [actualCompensatedNatCoefficient, dif_pos hp]





/-- Literal squarefree companion to the post-band prime score. -/
def postBandSquarefreeScore
    (q : B.RawBandGauge) (m : B.sampleData.Sample) : ℝ :=
  ∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
    B.actualCompensatedNatCoefficient q p *
      divInd p (B.sampleData.value m)









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

/-- Positivity of the exact projection denominator
`sum_j H_j alpha_j^2`. -/
theorem sharpBandWeightTotal_pos [Nonempty Band] :
    0 < sharpWeightTotal B.harmonicMass B.bandCenter := by
  unfold sharpWeightTotal sharpWeight
  apply Finset.sum_pos
  · intro j hj
    exact mul_pos (B.harmonicMass_pos j)
      (sq_pos_of_pos (B.bandCenter_pos j))
  · exact Finset.univ_nonempty

/-- Exact arithmetic projection of a raw band row to
`sum_j H_j alpha_j b_j = 0`. -/
def projectRawBandVector [Nonempty Band]
    (x : Band → ℝ) : B.RawBandGauge :=
  ⟨weightedGaugeProjection B.harmonicMass B.bandCenter x,
    weightedGaugeProjection_mem_rawGauge
      B.harmonicMass B.bandCenter x
      (ne_of_gt B.sharpBandWeightTotal_pos)⟩

theorem projectRawBandVector_add [Nonempty Band]
    (x y : Band → ℝ) :
    B.projectRawBandVector (x + y) =
      B.projectRawBandVector x + B.projectRawBandVector y := by
  apply Subtype.ext
  change weightedGaugeProjection B.harmonicMass B.bandCenter (x + y) =
    weightedGaugeProjection B.harmonicMass B.bandCenter x +
      weightedGaugeProjection B.harmonicMass B.bandCenter y
  exact weightedGaugeProjection_add
    B.harmonicMass B.bandCenter x y

theorem projectRawBandVector_smul [Nonempty Band]
    (a : ℝ) (x : Band → ℝ) :
    B.projectRawBandVector (a • x) =
      a • B.projectRawBandVector x := by
  apply Subtype.ext
  change weightedGaugeProjection B.harmonicMass B.bandCenter (a • x) =
    a • weightedGaugeProjection B.harmonicMass B.bandCenter x
  exact weightedGaugeProjection_smul
    B.harmonicMass B.bandCenter a x





/-- The literal normalized covariance row `D^{-1} Cov(Omega,F)`. -/
def normalizedBandCovarianceRow [Nonempty Head]
    (xi : B.ParamSpace) (F : B.sampleData.Sample → ℝ) (j : Band) : ℝ :=
  (B.tiltedLaw xi).covariance (B.bandScore j) F /
    B.harmonicMass j

theorem normalizedBandCovarianceRow_add [Nonempty Head]
    (xi : B.ParamSpace) (F G : B.sampleData.Sample → ℝ) :
    B.normalizedBandCovarianceRow xi (fun m ↦ F m + G m) =
      B.normalizedBandCovarianceRow xi F +
        B.normalizedBandCovarianceRow xi G := by
  funext j
  unfold normalizedBandCovarianceRow
  rw [FiniteProbability.covariance_add_right]
  simp only [Pi.add_apply]
  ring

theorem normalizedBandCovarianceRow_smul [Nonempty Head]
    (xi : B.ParamSpace) (a : ℝ) (F : B.sampleData.Sample → ℝ) :
    B.normalizedBandCovarianceRow xi (fun m ↦ a * F m) =
      a • B.normalizedBandCovarianceRow xi F := by
  funext j
  unfold normalizedBandCovarianceRow
  rw [FiniteProbability.covariance_smul_right]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring



theorem nuisanceCovarianceVector_add [Nonempty Head]
    (xi : B.ParamSpace) (F G : B.sampleData.Sample → ℝ) :
    B.nuisanceCovarianceVector xi (fun m ↦ F m + G m) =
      B.nuisanceCovarianceVector xi F +
        B.nuisanceCovarianceVector xi G := by
  apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).injective
  funext c
  change (B.tiltedLaw xi).covariance
      (fun m ↦ B.nuisanceStatistic m c) (fun m ↦ F m + G m) = _
  rw [FiniteProbability.covariance_add_right]
  rfl

theorem nuisanceCovarianceVector_smul [Nonempty Head]
    (xi : B.ParamSpace) (a : ℝ) (F : B.sampleData.Sample → ℝ) :
    B.nuisanceCovarianceVector xi (fun m ↦ a * F m) =
      a • B.nuisanceCovarianceVector xi F := by
  apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).injective
  funext c
  change (B.tiltedLaw xi).covariance
      (fun m ↦ B.nuisanceStatistic m c) (fun m ↦ a * F m) = _
  rw [FiniteProbability.covariance_smul_right]
  rfl

theorem nuisanceCoefficientOfScore_add [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F G : B.sampleData.Sample → ℝ) :
    B.nuisanceCoefficientOfScore xi hgamma hgap
        (fun m ↦ F m + G m) =
      B.nuisanceCoefficientOfScore xi hgamma hgap F +
        B.nuisanceCoefficientOfScore xi hgamma hgap G := by
  unfold nuisanceCoefficientOfScore
  rw [B.nuisanceCovarianceVector_add xi F G]
  exact (B.nuisanceCovarianceEquiv xi hgamma hgap).symm.map_add _ _

theorem nuisanceCoefficientOfScore_smul [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (a : ℝ) (F : B.sampleData.Sample → ℝ) :
    B.nuisanceCoefficientOfScore xi hgamma hgap (fun m ↦ a * F m) =
      a • B.nuisanceCoefficientOfScore xi hgamma hgap F := by
  unfold nuisanceCoefficientOfScore
  rw [B.nuisanceCovarianceVector_smul xi a F]
  exact (B.nuisanceCovarianceEquiv xi hgamma hgap).symm.map_smul a _

theorem nuisanceResidualScore_add [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F G : B.sampleData.Sample → ℝ) :
    B.nuisanceResidualScore xi hgamma hgap (fun m ↦ F m + G m) =
      fun m ↦ B.nuisanceResidualScore xi hgamma hgap F m +
        B.nuisanceResidualScore xi hgamma hgap G m := by
  funext m
  unfold nuisanceResidualScore
  rw [B.nuisanceCoefficientOfScore_add xi hgamma hgap F G,
    inner_add_left]
  ring

theorem nuisanceResidualScore_smul [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (a : ℝ) (F : B.sampleData.Sample → ℝ) :
    B.nuisanceResidualScore xi hgamma hgap (fun m ↦ a * F m) =
      fun m ↦ a * B.nuisanceResidualScore xi hgamma hgap F m := by
  funext m
  unfold nuisanceResidualScore
  rw [B.nuisanceCoefficientOfScore_smul xi hgamma hgap a F,
    inner_smul_left]
  simp only [conj_trivial]
  ring



theorem bandRegressionScore_add
    (q r : B.RawBandGauge) :
    B.bandRegressionScore (q + r) =
      fun m ↦ B.bandRegressionScore q m + B.bandRegressionScore r m := by
  funext m
  unfold bandRegressionScore
  simp only [Submodule.coe_add, Pi.add_apply, add_mul]
  rw [Finset.sum_add_distrib]

theorem bandRegressionScore_smul
    (a : ℝ) (q : B.RawBandGauge) :
    B.bandRegressionScore (a • q) =
      fun m ↦ a * B.bandRegressionScore q m := by
  funext m
  unfold bandRegressionScore
  simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring



/-- Actual Schur-projected normalized band row of a raw gauge score. -/
def schurBandRow [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge) : Band → ℝ :=
  B.normalizedBandCovarianceRow xi
    (B.nuisanceResidualScore xi hgamma hgap (B.bandRegressionScore q))

theorem schurBandRow_add [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q r : B.RawBandGauge) :
    B.schurBandRow xi hgamma hgap (q + r) =
      B.schurBandRow xi hgamma hgap q +
        B.schurBandRow xi hgamma hgap r := by
  unfold schurBandRow
  rw [B.bandRegressionScore_add q r,
    B.nuisanceResidualScore_add xi hgamma hgap,
    B.normalizedBandCovarianceRow_add xi]

theorem schurBandRow_smul [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (a : ℝ) (q : B.RawBandGauge) :
    B.schurBandRow xi hgamma hgap (a • q) =
      a • B.schurBandRow xi hgamma hgap q := by
  unfold schurBandRow
  rw [B.bandRegressionScore_smul a q,
    B.nuisanceResidualScore_smul xi hgamma hgap,
    B.normalizedBandCovarianceRow_smul xi]

/-- The exact projected operator
`P_{alpha,n} D^{-1} C^Z_{xi} P_{alpha,n}` on the arithmetic gauge. -/
def actualBandSchurLinearMap [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) :
    B.RawBandGauge →ₗ[ℝ] B.RawBandGauge where
  toFun q := B.projectRawBandVector (B.schurBandRow xi hgamma hgap q)
  map_add' q r := by
    rw [B.schurBandRow_add xi hgamma hgap q r,
      B.projectRawBandVector_add]
  map_smul' a q := by
    rw [B.schurBandRow_smul xi hgamma hgap a q,
      B.projectRawBandVector_smul]
    rfl

/-- Literal Schur-projected right side
`P_{alpha,n}D^{-1}b^Z`. -/
def actualBandRegressionTarget [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) : B.RawBandGauge :=
  B.projectRawBandVector
    (B.normalizedBandCovarianceRow xi
      (B.nuisanceResidualScore xi hgamma hgap B.slowScore))

/-- First-stage actual regression obtained from an inverse of the literal
operator just defined. -/
def actualBandRegression [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge) :
    B.RawBandGauge :=
  e.symm (B.actualBandRegressionTarget xi hgamma hgap)



















/-- The exact second-stage coefficient attached to the first-stage solve. -/
def actualTwoStageNuisanceCoefficient [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge) :
    B.NuisanceSpace :=
  B.actualNuisanceCoefficient xi hgamma hgap
    (B.actualBandRegression xi hgamma hgap e)

/-- The literal fully fitted `C_g` after the two displayed regression stages. -/
def actualTwoStageCompensatedScore [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge) :
    B.sampleData.Sample → ℝ :=
  B.actualCompensatedScore xi hgamma hgap
    (B.actualBandRegression xi hgamma hgap e)





end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperVectorFieldSchur -/
section


/-!
# Exact Schur decomposition of the paper vector field

The nonlinear ODE uses the literal vector field

`(D M(xi))^{-1} target`.

This file proves, for the actual finite covariance operator and the actual
paper coordinates, that its main and nuisance coordinate blocks are obtained
by the same exact Schur solve used in Lemmas 8.4 and 8.6.  No inverse estimate,
covariance gap, or marked-row estimate is packaged as data here.  The only
positivity hypotheses are the pointwise gaps needed to make the two displayed
finite linear maps invertible.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open scoped BigOperators

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Projection of a paper parameter onto the quotient/slow coordinates. -/
def mainPart (x : B.ParamSpace) : B.MainSpace :=
  (EuclideanSpace.equiv (MainCoord B.GaugeIndex) ℝ).symm
    (fun c => match c with
      | .gauge j => x (MomentCoord.gauge j)
      | .slow => x MomentCoord.slow)

/-- Projection of a paper parameter onto the physical/head coordinates. -/
def nuisancePart (x : B.ParamSpace) : B.NuisanceSpace :=
  (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).symm
    (fun c => match c with
      | .physical => x MomentCoord.physical
      | .head h => x (MomentCoord.head h))

@[simp] theorem mainPart_gauge (x : B.ParamSpace) (j : B.GaugeIndex) :
    B.mainPart x (MainCoord.gauge j) = x (MomentCoord.gauge j) := rfl

@[simp] theorem mainPart_slow (x : B.ParamSpace) :
    B.mainPart x MainCoord.slow = x MomentCoord.slow := rfl

@[simp] theorem nuisancePart_physical (x : B.ParamSpace) :
    B.nuisancePart x NuisanceCoord.physical = x MomentCoord.physical := rfl

@[simp] theorem nuisancePart_head (x : B.ParamSpace) (h : B.HeadIndex) :
    B.nuisancePart x (NuisanceCoord.head h) = x (MomentCoord.head h) := rfl













@[simp] theorem nuisancePart_normalizedTarget [Nonempty Head]
    (Delta : Band → ℝ) :
    B.nuisancePart (B.normalizedTarget Delta) = 0 := by
  apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).injective
  funext c
  cases c <;> simp [nuisancePart, normalizedTarget, targetVector,
    unscaledTarget, coordScale]







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

/-- The omitted low coordinate of an arithmetic raw-gauge vector is exactly
the weighted linear combination used by the concrete quotient basis.  This
is the finite identity which makes the paper's passage between intrinsic
gauge vectors and concrete coordinates invertible even for the moving low
cell. -/
theorem rawBandGauge_low_eq (q : B.RawBandGauge) :
    q.1 B.lowBand =
      -∑ j : B.GaugeIndex, B.lowRatio j * q.1 j.1 := by
  let d0 := B.harmonicMass B.lowBand * B.bandCenter B.lowBand
  have hd0 : d0 ≠ 0 := by
    exact ne_of_gt (mul_pos (B.harmonicMass_pos B.lowBand)
      (B.bandCenter_pos B.lowBand))
  have hq := q.2
  change (∑ j : Band,
    rawGaugeWeight B.harmonicMass B.bandCenter j * q.1 j) = 0 at hq
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun j : Band ↦
      rawGaugeWeight B.harmonicMass B.bandCenter j * q.1 j)
    B.lowBand] at hq
  simp only [rawGaugeWeight] at hq
  have hratio (j : B.GaugeIndex) :
      B.harmonicMass j.1 * B.bandCenter j.1 =
        d0 * B.lowRatio j := by
    unfold lowRatio d0
    exact (mul_div_cancel₀
      (B.harmonicMass j.1 * B.bandCenter j.1) hd0).symm
  simp_rw [hratio] at hq
  change d0 * q.1 B.lowBand +
      ∑ x : B.GaugeIndex, d0 * B.lowRatio x * q.1 x.1 = 0 at hq
  simp_rw [mul_assoc] at hq
  rw [← Finset.mul_sum] at hq
  have hsolve : q.1 B.lowBand =
      -(∑ j : B.GaugeIndex, B.lowRatio j * q.1 j.1) := by
    apply (mul_left_cancel₀ hd0)
    calc
      d0 * q.1 B.lowBand =
          -d0 * ∑ j : B.GaugeIndex, B.lowRatio j * q.1 j.1 := by
        linarith
      _ = d0 * -(∑ j : B.GaugeIndex,
          B.lowRatio j * q.1 j.1) := by ring
  exact hsolve

/-- The raw arithmetic-gauge vector represented by the gauge coordinates of
an actual main parameter. -/
def rawGaugeOfMain (u : B.MainSpace) : B.RawBandGauge := by
  refine ⟨fun j => B.bandParameter (B.mainEmbed u) j, ?_⟩
  change (∑ j : Band,
    rawGaugeWeight B.harmonicMass B.bandCenter j *
      B.bandParameter (B.mainEmbed u) j) = 0
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun j : Band =>
      rawGaugeWeight B.harmonicMass B.bandCenter j *
        B.bandParameter (B.mainEmbed u) j) B.lowBand]
  simp only [rawGaugeWeight, B.bandParameter_low,
    B.bandParameter_gauge, B.mainEmbed_gauge]
  have hden : B.harmonicMass B.lowBand * B.bandCenter B.lowBand ≠ 0 :=
    ne_of_gt (mul_pos (B.harmonicMass_pos B.lowBand)
      (B.bandCenter_pos B.lowBand))
  have hterm (j : B.GaugeIndex) :
      B.harmonicMass B.lowBand * B.bandCenter B.lowBand *
          (B.lowRatio j * u (MainCoord.gauge j)) =
        B.harmonicMass j.1 * B.bandCenter j.1 *
          u (MainCoord.gauge j) := by
    unfold lowRatio
    calc
      B.harmonicMass B.lowBand * B.bandCenter B.lowBand *
          ((B.harmonicMass j.1 * B.bandCenter j.1 /
              (B.harmonicMass B.lowBand * B.bandCenter B.lowBand)) *
            u (MainCoord.gauge j)) =
          (B.harmonicMass B.lowBand * B.bandCenter B.lowBand *
            ((B.harmonicMass j.1 * B.bandCenter j.1) /
              (B.harmonicMass B.lowBand * B.bandCenter B.lowBand))) *
            u (MainCoord.gauge j) := by ring
      _ = B.harmonicMass j.1 * B.bandCenter j.1 *
          u (MainCoord.gauge j) := by
        rw [mul_div_cancel₀ _ hden]
  rw [mul_neg, Finset.mul_sum]
  simp_rw [hterm]
  ring

@[simp] theorem rawGaugeOfMain_apply (u : B.MainSpace) (j : Band) :
    (B.rawGaugeOfMain u).1 j = B.bandParameter (B.mainEmbed u) j := rfl

@[simp] theorem rawGaugeOfMain_positive (u : B.MainSpace)
    (j : B.GaugeIndex) :
    (B.rawGaugeOfMain u).1 j.1 = u (MainCoord.gauge j) := by
  simp [rawGaugeOfMain]

@[simp] theorem rawGaugeOfMain_low (u : B.MainSpace) :
    (B.rawGaugeOfMain u).1 B.lowBand =
      -∑ j : B.GaugeIndex, B.lowRatio j * u (MainCoord.gauge j) := by
  simp [rawGaugeOfMain]

/-- The intrinsic arithmetic gauge together with the stored slow coordinate
is linearly equivalent to the actual `MainSpace` used by the exponential
family.  The inverse is the concrete basis from the paper; the low
coordinate is recovered by `rawBandGauge_low_eq`, not by a dimension or
mesh-dependent matrix inverse. -/
def mainRawSlowLinearEquiv :
    B.MainSpace ≃ₗ[ℝ] (B.RawBandGauge × ℝ) where
  toFun u := (B.rawGaugeOfMain u, u MainCoord.slow)
  invFun qr :=
    (EuclideanSpace.equiv (MainCoord B.GaugeIndex) ℝ).symm
      (fun c ↦ match c with
        | .gauge j => qr.1.1 j.1
        | .slow => qr.2)
  left_inv u := by
    apply (EuclideanSpace.equiv (MainCoord B.GaugeIndex) ℝ).injective
    funext c
    cases c with
    | gauge j => simp
    | slow => rfl
  right_inv qr := by
    apply Prod.ext
    · apply Subtype.ext
      funext j
      by_cases hj : j = B.lowBand
      · subst j
        rw [B.rawGaugeOfMain_low, B.rawBandGauge_low_eq]
        apply congrArg Neg.neg
        apply Finset.sum_congr rfl
        intro k hk
        rfl
      · let k : B.GaugeIndex := ⟨j, hj⟩
        change (B.rawGaugeOfMain _).1 k.1 = qr.1.1 j
        rw [B.rawGaugeOfMain_positive]
        change qr.1.1 j = qr.1.1 j
        rfl
    · rfl
  map_add' u v := by
    apply Prod.ext
    · apply Subtype.ext
      funext j
      exact B.bandParameter_add (B.mainEmbed u) (B.mainEmbed v) j
    · rfl
  map_smul' a u := by
    apply Prod.ext
    · apply Subtype.ext
      funext j
      exact B.bandParameter_smul a (B.mainEmbed u) j
    · rfl

@[simp] theorem mainRawSlowLinearEquiv_apply (u : B.MainSpace) :
    B.mainRawSlowLinearEquiv u =
      (B.rawGaugeOfMain u, u MainCoord.slow) := rfl

@[simp] theorem mainRawSlowLinearEquiv_symm_gauge
    (q : B.RawBandGauge) (s : ℝ) (j : B.GaugeIndex) :
    (B.mainRawSlowLinearEquiv.symm (q, s)) (MainCoord.gauge j) =
      q.1 j.1 := rfl

@[simp] theorem mainRawSlowLinearEquiv_symm_slow
    (q : B.RawBandGauge) (s : ℝ) :
    (B.mainRawSlowLinearEquiv.symm (q, s)) MainCoord.slow = s := rfl



/-- The slow coordinate of `MainSpace` is literally the stored coordinate
`w * lambda` in the full parameter space. -/
@[simp] theorem mainEmbed_effectivePrimeCoefficient
    (u : B.MainSpace)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    B.effectivePrimeCoefficient (B.mainEmbed u) p =
      (B.rawGaugeOfMain u).1 (B.partition.band p) +
        (u MainCoord.slow / B.w) * B.primeDeviation p := by
  rfl

/-- Nuisance coordinates do not alter any effective prime coefficient. -/
@[simp] theorem nuisanceEmbed_effectivePrimeCoefficient
    (z : B.NuisanceSpace)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    B.effectivePrimeCoefficient (B.nuisanceEmbed z) p = 0 := by
  unfold effectivePrimeCoefficient bandParameter
  by_cases h : B.partition.band p = B.lowBand
  · simp only [h, dite_true, B.nuisanceEmbed_gauge,
      B.nuisanceEmbed_slow, zero_div, zero_mul, add_zero]
    simp
  · simp [h]



/-- Exact nuisance block of a Schur residual. -/
@[simp] theorem nuisanceParameter_schurResidual
    (R : B.MainSpace → B.NuisanceSpace) (u : B.MainSpace) :
    B.nuisanceParameter (B.schurResidual R u) = -R u := by
  apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).injective
  funext c
  cases c <;> simp [schurResidual, combine, nuisanceParameter]

/-- Exact stored slow coordinate of a Schur residual. -/
@[simp] theorem schurResidual_slow
    (R : B.MainSpace → B.NuisanceSpace) (u : B.MainSpace) :
    B.schurResidual R u MomentCoord.slow = u MainCoord.slow := by
  simp [schurResidual]





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

/-- The arithmetic diagonal pairing on the raw gauge. -/
def rawDPairing (H alpha : Band → ℝ)
    (q r : RawGaugeSpace H alpha) : ℝ :=
  ∑ j, H j * q.1 j * r.1 j

/-- Smallest literal sharp diagonal weight of the finite arithmetic band
family. -/
def rawDLowerWeight (H alpha : Band → ℝ) : ℝ :=
  let s : Finset ℝ := Finset.univ.image (fun j ↦ H j * alpha j ^ 2)
  s.min' (by
    classical
    exact Finset.univ_nonempty.image _)









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

/-- The exact arithmetic `D` pairing on raw band rows. -/
def bandDPairing (q r : B.RawBandGauge) : ℝ :=
  ∑ j : Band, B.harmonicMass j * q.1 j * r.1 j





















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperMainFastSlowCoordinates -/
section


/-!
# Concrete main-coordinate bound for the fast/slow Schur split

This file discharges the finite coordinate comparison left explicit by
`exactSchurGap_of_fastSlow`.  The constant is literal and finite; it may
depend on the fixed arithmetic partition, but it is chosen before the ODE
and no continuum or asymptotic assertion enters its proof.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Sum of the squared actual arithmetic centres over the concrete gauge
coordinates (the low row is recovered from the gauge relation and is not a
coordinate of `MainSpace`). -/
def gaugeCenterSquareSum : ℝ :=
  ∑ j : B.GaugeIndex, B.bandCenter j.1 ^ 2











end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperBridgePrimewiseRate -/
section


/-!
# Primewise moment transport along the actual bridge ODE

The paper obtains the post-bridge bound for each marked prime by integrating
the covariance row along the nonlinear moment-fitting path.  This file proves
that passage for the genuine finite exponential family.  It is not an
asymptotic contract: the derivative is the exact covariance derivative of the
finite active moment, and the endpoint estimate is a direct mean-value bound
on the interval `[0,1]`.
-/

open Metric Set

namespace Erdos390.Full

noncomputable section

namespace FiniteExponentialFamily

variable {Omega Param : Type*} [Fintype Omega]
  [NormedAddCommGroup Param] [NormedSpace Real Param]
  [FiniteDimensional Real Param]



end FiniteExponentialFamily

namespace PaperBridgeFit

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The actual marked valuation statistic at the natural-number coordinate
represented by a structured sample. -/
def markedValuation (p : Nat) (m : B.sampleData.Sample) : Real :=
  ArithmeticModel.valuation p (B.sampleData.value m)







end BridgeData

end PaperBridgeFit

end

end Erdos390.Full

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



/-- Unprojected normalized band row represented by the paper target.  The
factor `1/H_j` is forced by the exact arithmetic `D` pairing. -/
def normalizedTargetBandRow [Nonempty Head]
    (Delta : Band → ℝ) (j : Band) : ℝ :=
  (B.L / B.q) * Delta j / B.harmonicMass j

/-- The literal arithmetic-gauge projection of the normalized target row. -/
def projectedNormalizedTargetBand [Nonempty Head] [Nonempty Band]
    (Delta : Band → ℝ) : B.RawBandGauge :=
  B.projectRawBandVector (B.normalizedTargetBandRow Delta)









/-- Main vector carrying only a raw arithmetic-gauge coefficient. -/
def rawOnlyMain (q : B.RawBandGauge) : B.MainSpace :=
  B.mainRawSlowLinearEquiv.symm (q, 0)

@[simp] theorem rawGaugeOfMain_rawOnlyMain (q : B.RawBandGauge) :
    B.rawGaugeOfMain (B.rawOnlyMain q) = q := by
  have h := B.mainRawSlowLinearEquiv.apply_symm_apply (q, 0)
  exact congrArg Prod.fst h

@[simp] theorem rawOnlyMain_slow (q : B.RawBandGauge) :
    B.rawOnlyMain q MainCoord.slow = 0 :=
  B.mainRawSlowLinearEquiv_symm_slow q 0



/-- The fast raw gauge associated with a main vector after the first-stage
slow-column regression. -/
def fastGaugeOfMain [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (u : B.MainSpace) : B.RawBandGauge :=
  B.rawGaugeOfMain u +
    (u MainCoord.slow / B.w) •
      B.actualBandRegression xi hgamma hgap e









/-- Main direction whose exact Schur residual is the fully compensated
two-stage slow score.  Its raw coordinate is `-qReg` and its stored slow
coordinate is exactly `w`. -/
def compensatedMainDirection [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge) : B.MainSpace :=
  B.mainRawSlowLinearEquiv.symm
    (-B.actualBandRegression xi hgamma hgap e, B.w)

@[simp] theorem rawGaugeOfMain_compensatedMainDirection
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge) :
    B.rawGaugeOfMain
        (B.compensatedMainDirection xi hgamma hgap e) =
      -B.actualBandRegression xi hgamma hgap e := by
  have h := B.mainRawSlowLinearEquiv.apply_symm_apply
    (-B.actualBandRegression xi hgamma hgap e, B.w)
  exact congrArg Prod.fst h

@[simp] theorem compensatedMainDirection_slow
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge) :
    B.compensatedMainDirection xi hgamma hgap e MainCoord.slow = B.w :=
  B.mainRawSlowLinearEquiv_symm_slow
    (-B.actualBandRegression xi hgamma hgap e) B.w



/-- Literal right side in the compensated slow equation. -/
def compensatedNormalizedTarget [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (Delta : Band → ℝ) : ℝ :=
  inner ℝ (B.compensatedMainDirection xi hgamma hgap e)
    (B.mainPart (B.normalizedTarget Delta))







/-- Literal finite variance in the compensated slow denominator. -/
def actualTwoStageCompensatedVariance
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge) : ℝ :=
  (B.tiltedLaw xi).covariance
    (B.actualTwoStageCompensatedScore xi hgamma hgap e)
    (B.actualTwoStageCompensatedScore xi hgamma hgap e)

















/-- Literal fast nuisance coefficient attached to the normalized target. -/
def targetFastNuisanceCoefficient
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (Delta : Band → ℝ) : B.NuisanceSpace :=
  B.nuisanceCoefficientOfScore xi hgamma hgap
    (B.bandRegressionScore
      (e.symm (B.projectedNormalizedTargetBand Delta)))











end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.LocalizedMarkedTiltCovariance -/
section


/-!
# Localized covariance stability under a small exponential tilt

The physical/head residual in the paper is a second, small tilt of each
medium-prime cell law.  A total-variation estimate would lose the divisibility
mark.  This file instead keeps the marginal and joint-event scales visible.

Everything below is an exact statement about finite probability laws.  The
arithmetic application supplies reciprocal bounds for the three marked
events `A`, `B`, and `A * B`.
-/

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

/-- The explicit relative expectation-loss factor for a pointwise-small
second tilt. -/
def smallTiltLoss (epsilon : ℝ) : ℝ :=
  4 * epsilon / (1 - 2 * epsilon)















end FiniteProbability

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperBridgeNuisanceTiltFallback -/
section


/-!
# Marked fallback through the physical/head bridge tilt

On a fixed tagged bridge cell all centered-head coordinates are constant.
Consequently the residual nuisance tilt is exactly a small physical-log tilt;
the constant head factor cancels from normalization.  We combine that exact
identity with reciprocal divisibility bounds for the medium-prime tilt.

The resulting estimates retain the marked `1 / D` and `1 / (p q)` scales.
No total-variation estimate is used.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open ValuationScoreDomination OmittedTiltFallback
open DivisibilityMomentBounds

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Extend the actual effective prime fugacity by zero outside the literal
medium-prime band. -/
def effectiveNatCoefficient (xi : B.ParamSpace) (p : ℕ) : ℝ :=
  if hp : p ∈ primeBand B.sampleData.n B.sampleData.W then
    B.effectivePrimeCoefficient xi ⟨p, hp⟩
  else 0

@[simp] theorem effectiveNatCoefficient_of_mem
    (xi : B.ParamSpace) {p : ℕ}
    (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    B.effectiveNatCoefficient xi p =
      B.effectivePrimeCoefficient xi ⟨p, hp⟩ := by
  simp only [effectiveNatCoefficient, dif_pos hp]



/-- The component law after only the medium-prime valuation tilt. -/
def cellMediumLaw [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head) :
    FiniteProbability (B.sampleData.SampleAt c) :=
  (B.guardedCellProbability c).exponentialTilt
    (sigmaCellScore (B.scaledMediumScore xi) c)

/-- The only nonconstant part of the nuisance score on a fixed cell. -/
def cellPhysicalTiltScore [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    (m : B.sampleData.SampleAt c) : ℝ :=
  (xi MomentCoord.physical / B.L) * B.physicalScore ⟨c, m⟩

/-- The head contribution to the nuisance score on a tagged cell. -/
def cellHeadTiltConstant [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head) : ℝ :=
  (∑ h : B.HeadIndex,
      xi (MomentCoord.head h) *
        ((if c.1 = h.1 then 1 else 0) - B.headBaselineMass h.1)) / B.L

 def nuisanceCoordEquiv_PaperBridgeNuisanceTiltFallback (I : Type*) :
    NuisanceCoord I ≃ Unit ⊕ I where
  toFun
    | .physical => Sum.inl ()
    | .head h => Sum.inr h
  invFun
    | Sum.inl _ => .physical
    | Sum.inr h => .head h
  left_inv c := by cases c <;> rfl
  right_inv
    | Sum.inl () => rfl
    | Sum.inr h => rfl























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

/-- The signed off-diagonal entry of the arithmetic Dickman matrix. -/
def squarefreeKernelEntry (n p q : ℕ) : ℝ :=
  covarianceKernel (tPrime n p) (tPrime n q) /
    ((p : ℝ) * (q : ℝ))

/-- The diagonal multiplier together with the diagonal term inserted by the
double-prime kernel sum.  This is exactly the diagonal entry represented by
`arithmeticDiagonal + arithmeticKernel`. -/
def squarefreeReferenceEntry (n p q : ℕ) : ℝ :=
  if p = q then
    DickmanBasic.F (tPrime n p) / (p : ℝ) +
      squarefreeKernelEntry n p p
  else squarefreeKernelEntry n p q













end

end Erdos390.Full.SquarefreeCovarianceReference

end

/- Source module: Erdos390.Full.SquarefreeSharpBandTransfer -/
section


/-!
# Sharp band aggregation of the signed squarefree comparison

This is the exact finite aggregation needed between the marked-divisor
profiles and the canonical endpoint operator.  The moving low row is kept
visible: a profile error `epsilon` costs `epsilon / alpha_i`, whereas the
diagonal Bernoulli correction costs only `Cdiag / W`.
-/

open scoped BigOperators

namespace Erdos390.Full.SquarefreeSharpBandTransfer

open ArithmeticModel ArithmeticBandGeometry
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open SquarefreeCovarianceReference
open PaperWeightedInverseExport PrimeSums

noncomputable section

variable {Omega Band : Type*} [Fintype Omega]
  [Fintype Band] [DecidableEq Band]
  {M n W : ℕ}

/-- Actual squarefree normalized band row, before sharp conjugation. -/
def squarefreeBandRow
    (law : BoundedValuationLaw Omega M) (P : Partition n W Band)
    (b : Band → ℝ) (i : Band) : ℝ :=
  (1 / P.mass i) *
    ∑ p ∈ P.data.fiber i,
      ∑ q : BandPrime n W, b (P.band q) * law.covII p.1 q.1

/-- The corresponding signed Dickman reference row. -/
def referenceBandRow
    (P : Partition n W Band) (b : Band → ℝ) (i : Band) : ℝ :=
  (1 / P.mass i) *
    ∑ p ∈ P.data.fiber i,
      ∑ q : BandPrime n W,
        b (P.band q) * squarefreeReferenceEntry n p.1 q.1

/-- Sharp conjugation by the actual arithmetic centers. -/
def squarefreeSharpRow
    (law : BoundedValuationLaw Omega M) (P : Partition n W Band)
    (q : Band → ℝ) (i : Band) : ℝ :=
  squarefreeBandRow law P (fun j ↦ P.center j * q j) i / P.center i

def referenceSharpRow
    (P : Partition n W Band) (q : Band → ℝ) (i : Band) : ℝ :=
  referenceBandRow P (fun j ↦ P.center j * q j) i / P.center i



end

end Erdos390.Full.SquarefreeSharpBandTransfer

end

/- Source module: Erdos390.Full.GuardDeletionReindexing -/
section


/-!
# Exact reindexing after guard deletion

The guard perturbation lemmas use a probability law on the original cell,
with deleted points assigned mass zero.  The bridge uses the subtype of the
literal guard-deleted finset.  This file proves that these are exactly the
same conditional law after reindexing, including after an exponential tilt.
-/

open scoped BigOperators

namespace Erdos390.Full.GuardedUniformCell

open FiniteProbability

noncomputable section

variable {Alpha : Type*} [DecidableEq Alpha]

/-- Inclusion of a member of `S \ G` into the original cell subtype `S`. -/
def remainingEmbedding (S G : Finset Alpha) : ↑(S \ G) → ↑S :=
  fun x ↦ ⟨x.1, (Finset.mem_sdiff.mp x.2).1⟩

@[simp] theorem remainingEmbedding_value (S G : Finset Alpha)
    (x : ↑(S \ G)) :
    ((remainingEmbedding S G x : ↑S) : Alpha) = x.1 := rfl

@[simp] theorem remainingEmbedding_not_guard (S G : Finset Alpha)
    (x : ↑(S \ G)) :
    remainingEmbedding S G x ∉ guardSubtype S G := by
  rw [mem_guardSubtype]
  exact (Finset.mem_sdiff.mp x.2).2

/-- The guard-deleted cell is equivalent to the non-guard members of the
original subtype. -/
def remainingEquiv (S G : Finset Alpha) :
    ↑(S \ G) ≃ {x : ↑S // x ∉ guardSubtype S G} where
  toFun x := ⟨remainingEmbedding S G x,
    remainingEmbedding_not_guard S G x⟩
  invFun x := ⟨x.1.1, Finset.mem_sdiff.mpr ⟨x.1.2, by
    simpa only [mem_guardSubtype] using x.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl



/-- Exponential weight remaining after guard deletion. -/
def remainingExpSum (S G : Finset Alpha) (score : ↑S → ℝ) : ℝ :=
  ∑ y : ↑(S \ G), Real.exp (score (remainingEmbedding S G y))













end

end Erdos390.Full.GuardedUniformCell

end

/- Source module: Erdos390.Full.GuardDeletionSquarefreeProfiles -/
section


/-!
# Reciprocal signed profiles after guard deletion

For the signed squarefree comparison only divisors `p` and `pq` occur.
Although deleting guards first gives an additive probability error, the
paper census is much smaller than `1/y²`; multiplying by the explicit
`y²` factor therefore restores the required reciprocal scale.  This file
records the exact finite step, including renormalization.
-/

namespace Erdos390.Full.GuardDeletionSquarefreeProfiles

open ArithmeticModel Scale FiniteProbability GuardedUniformCell
open OmittedTiltPairChamber PaperPrimePowerChamberError
open PaperScaleMarkedCell

noncomputable section

/-- The explicit reciprocal-profile cost of deleting guards from one cell. -/
def guardSquarefreeError
    (S G : Finset ℕ) (scoreBound : ℝ) (n : ℕ) : ℝ :=
  2 * (Real.exp (2 * scoreBound) * (G.card : ℝ) / (S.card : ℝ)) *
    (yNat n : ℝ) ^ 2







end

end Erdos390.Full.GuardDeletionSquarefreeProfiles

end

/- Source module: Erdos390.Full.PaperGuardDeletionRows -/
section


/-!
# Prime-row perturbations from the concrete guard deletion

The central estimate is family-summed.  Thus the row cost is controlled by
the total valuation of one integer, `O(log n / log W)`, rather than by the
number of primes in the moving band.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperGuardCensus

open ArithmeticModel Scale StructuredCells HeadPattern
open FiniteProbability GuardedUniformCell
open ValuationTiltCell ArithmeticBandGeometry
open PaperScaleMarkedCell

noncomputable section

variable {Alpha I : Type*} [DecidableEq Alpha] [Fintype I]











/-- The logarithmic envelope used in all concrete guard rows. -/
def valuationEnvelope
    {Head : Type*} [Fintype Head]
    (Iphys : PhysicalIntervals) (n W : ℕ)
    (c : PaperBridgeFit.Cell Head) : ℝ :=
  Real.log (physicalBound (Iphys.upper c.2) n : ℝ) / Real.log (W : ℝ)







end

end Erdos390.Full.PaperGuardCensus

end

/- Source module: Erdos390.Full.GuardSquarefreeErrorRate -/
section


/-!
# Vanishing rate of the squarefree guard error

The reciprocal guard conversion costs `y²`.  Since the concrete ledger has
`O(y log n)` guards and each raw cell has positive linear density, the final
cost is `O((log n)/n^(1/3))`; it still vanishes after multiplication by
`log log n`.  This file proves that rate with the literal scales.
-/

open Filter Topology

namespace Erdos390.Full.GuardSquarefreeErrorRate

open ArithmeticModel Scale PaperGuardCensus
open GuardDeletionSquarefreeProfiles

noncomputable section





























/-- One common guard-profile error for the fixed finite family of all
head/physical cells. -/
def canonicalGuardSquarefreeError
    {Head : Type*} [Fintype Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    {Cprom Cbank : ℕ} (G : ∀ n, Ledger n Cprom Cbank)
    (K : ℝ) (n : ℕ) : ℝ :=
  ∑ c : PaperBridgeFit.Cell Head,
    guardSquarefreeError (rawCell P I n c) (G n).guards K n







end

end Erdos390.Full.GuardSquarefreeErrorRate

end

/- Source module: Erdos390.Full.PrimePowerSharpBandTransfer -/
section


/-!
# Prime-power transfer in the moving-low sharp band norm

The already-proved row field of `PrimePowerTransferBounds` is sufficient for
fixed positive bands, but dividing that collapsed row bound by the moving low
centre would incorrectly charge the box-independent `C_pow / W` term by
`1 / alpha_0`.  This file retains the first four fields of the certificate
until after band averaging.  The factors `t_p t_q` then cancel the output
centre exactly; only the genuine analytic remainder is divided by that
centre.
-/

open scoped BigOperators

namespace Erdos390.Full.PrimePowerSharpBandTransfer

set_option maxHeartbeats 2400000

open ArithmeticModel ArithmeticBandGeometry PrimeSums
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerLemma75 PaperPrimePowerRow
open PrimePowerCutoffCovariance
open SquarefreeSharpBandTransfer

noncomputable section

variable {Omega Band : Type*} [Fintype Omega]
  [Fintype Band] [DecidableEq Band]
  {M n W : ℕ}

/-- Full-valuation analogue of the normalized squarefree band row. -/
def fullBandRow
    (law : BoundedValuationLaw Omega M) (P : Partition n W Band)
    (b : Band → ℝ) (i : Band) : ℝ :=
  (1 / P.mass i) *
    ∑ p ∈ P.data.fiber i,
      ∑ q : BandPrime n W, b (P.band q) * law.covVV p.1 q.1

def fullSharpRow
    (law : BoundedValuationLaw Omega M) (P : Partition n W Band)
    (q : Band → ℝ) (i : Band) : ℝ :=
  fullBandRow law P (fun j ↦ P.center j * q j) i / P.center i







end

end Erdos390.Full.PrimePowerSharpBandTransfer

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

/-- The full-tilted law on one literal guard-deleted component, widened to
the same endpoint as the global bridge law. -/
def actualComponentValuationLaw [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head) :
    BoundedValuationLaw (B.sampleData.SampleAt c) B.sampleEndpoint where
  probability :=
    (B.guardedCellProbability c).exponentialTilt
      (sigmaCellScore (B.scaledBridgeScore xi) c)
  value := fun m => (m : ℕ)
  value_pos := by
    intro m
    let sample : B.sampleData.Sample := ⟨c, m⟩
    simpa only [sample, StructuredSampleData.value] using
      B.sampleData.value_pos sample
  value_le := by
    intro m
    let sample : B.sampleData.Sample := ⟨c, m⟩
    simpa only [sample, StructuredSampleData.value] using
      B.sample_value_le_endpoint sample

@[simp] theorem actualComponentValuationLaw_probability [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head) :
    (B.actualComponentValuationLaw xi c).probability =
      (B.guardedCellProbability c).exponentialTilt
        (sigmaCellScore (B.scaledBridgeScore xi) c) := rfl

@[simp] theorem actualComponentValuationLaw_value [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    (m : B.sampleData.SampleAt c) :
    (B.actualComponentValuationLaw xi c).value m = (m : ℕ) := rfl





















/-- The complete sharp-row error after inserting the moving-low reciprocal
center envelope `1/alpha_i ≤ Calpha log L`. -/
def squarefreeSharpProfileRemainder
    (E : ℕ → ℝ) (Calpha K CKernel : ℝ) (W n : ℕ) : ℝ :=
  (4 * PaperPrimePowerChamberError.pairCovarianceScale (E n)) * K *
      (Calpha * Real.log (Scale.L n)) +
    2 * E n +
    ((1 / DickmanBasic.rho DickmanBasic.U + 2 * E n) ^ 2 + CKernel) *
      (1 / (W : ℝ))









/-! ### Exact finite-dimensional attachment to the arithmetic inverse -/

 theorem squarefreeSharpRow_add
    [Nonempty Head]
    (xi : B.ParamSpace) (q r : Band → ℝ) (i : Band) :
    SquarefreeSharpBandTransfer.squarefreeSharpRow
        (B.actualValuationLaw xi) B.partition (q + r) i =
      SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i +
        SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition r i := by
  unfold SquarefreeSharpBandTransfer.squarefreeSharpRow
    SquarefreeSharpBandTransfer.squarefreeBandRow
  simp only [Pi.add_apply, mul_add, add_mul]
  have hinner (p : ArithmeticBandGeometry.BandPrime
      B.sampleData.n B.sampleData.W) :
      (∑ s : ArithmeticBandGeometry.BandPrime
          B.sampleData.n B.sampleData.W,
        (B.partition.center (B.partition.band s) * q (B.partition.band s) *
            (B.actualValuationLaw xi).covII p.1 s.1 +
          B.partition.center (B.partition.band s) * r (B.partition.band s) *
            (B.actualValuationLaw xi).covII p.1 s.1)) =
        (∑ s : ArithmeticBandGeometry.BandPrime
            B.sampleData.n B.sampleData.W,
          B.partition.center (B.partition.band s) * q (B.partition.band s) *
            (B.actualValuationLaw xi).covII p.1 s.1) +
        ∑ s : ArithmeticBandGeometry.BandPrime
            B.sampleData.n B.sampleData.W,
          B.partition.center (B.partition.band s) * r (B.partition.band s) *
            (B.actualValuationLaw xi).covII p.1 s.1 := by
    exact Finset.sum_add_distrib
  have hsum :
      (∑ p ∈ B.partition.data.fiber i,
        ∑ s : ArithmeticBandGeometry.BandPrime
            B.sampleData.n B.sampleData.W,
          (B.partition.center (B.partition.band s) * q (B.partition.band s) *
              (B.actualValuationLaw xi).covII p.1 s.1 +
            B.partition.center (B.partition.band s) * r (B.partition.band s) *
              (B.actualValuationLaw xi).covII p.1 s.1)) =
        (∑ p ∈ B.partition.data.fiber i,
          ∑ s : ArithmeticBandGeometry.BandPrime
              B.sampleData.n B.sampleData.W,
            B.partition.center (B.partition.band s) * q (B.partition.band s) *
              (B.actualValuationLaw xi).covII p.1 s.1) +
        ∑ p ∈ B.partition.data.fiber i,
          ∑ s : ArithmeticBandGeometry.BandPrime
              B.sampleData.n B.sampleData.W,
            B.partition.center (B.partition.band s) * r (B.partition.band s) *
              (B.actualValuationLaw xi).covII p.1 s.1 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    exact hinner p
  rw [hsum]
  ring

 theorem squarefreeSharpRow_smul
    [Nonempty Head]
    (xi : B.ParamSpace) (c : ℝ) (q : Band → ℝ) (i : Band) :
    SquarefreeSharpBandTransfer.squarefreeSharpRow
        (B.actualValuationLaw xi) B.partition (c • q) i =
      c * SquarefreeSharpBandTransfer.squarefreeSharpRow
        (B.actualValuationLaw xi) B.partition q i := by
  unfold SquarefreeSharpBandTransfer.squarefreeSharpRow
    SquarefreeSharpBandTransfer.squarefreeBandRow
  simp only [Pi.smul_apply, smul_eq_mul]
  have hinner (p : ArithmeticBandGeometry.BandPrime
      B.sampleData.n B.sampleData.W) :
      (∑ r : ArithmeticBandGeometry.BandPrime
          B.sampleData.n B.sampleData.W,
        B.partition.center (B.partition.band r) *
            (c * q (B.partition.band r)) *
              (B.actualValuationLaw xi).covII p.1 r.1) =
        c * (∑ r : ArithmeticBandGeometry.BandPrime
          B.sampleData.n B.sampleData.W,
          B.partition.center (B.partition.band r) *
            q (B.partition.band r) *
              (B.actualValuationLaw xi).covII p.1 r.1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    ring
  simp_rw [hinner]
  rw [← Finset.mul_sum]
  ring

/-- The exact sharp gauge weight has positive total mass.  This is a finite
arithmetic fact: every harmonic mass and every arithmetic center is positive,
and `lowBand` supplies a witness to the nonempty sum. -/
theorem actualSharpWeightTotal_pos :
    0 < MovingLowGaugeTransfer.sharpWeightTotal
      B.partition.mass B.partition.center := by
  unfold MovingLowGaugeTransfer.sharpWeightTotal
    MovingLowGaugeTransfer.sharpWeight
  apply Finset.sum_pos
  · intro j _hj
    exact mul_pos (B.partition.data.mass_pos j)
      (sq_pos_of_pos (B.partition.center_pos B.n_gt_one j))
  · exact ⟨B.lowBand, Finset.mem_univ _⟩

/-- The literal actual squarefree covariance operator, projected to the exact
finite arithmetic sharp gauge.  No reference kernel or asymptotic estimate
occurs in this definition. -/
def actualSquarefreeProjectedLinearMap
    [Nonempty Head] (xi : B.ParamSpace) :
    PaperWeightedInverseExport.SharpGaugeSpace
        B.partition.mass B.partition.center →ₗ[ℝ]
      PaperWeightedInverseExport.SharpGaugeSpace
        B.partition.mass B.partition.center where
  toFun q :=
    ⟨FiniteGraphQuotientInverse.meanProjection
        (MovingLowGaugeTransfer.sharpWeight
          B.partition.mass B.partition.center)
        (fun i ↦ SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q.1 i),
      FiniteGraphStableInverse.weighted_sum_meanProjection
        (MovingLowGaugeTransfer.sharpWeight
          B.partition.mass B.partition.center)
        (fun i ↦ SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q.1 i)
        (ne_of_gt (actualSharpWeightTotal_pos B))⟩
  map_add' q r := by
    apply Subtype.ext
    funext i
    change FiniteGraphQuotientInverse.meanProjection
        (MovingLowGaugeTransfer.sharpWeight
          B.partition.mass B.partition.center)
        (fun j ↦ SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition (q.1 + r.1) j) i = _
    rw [show (fun j ↦ SquarefreeSharpBandTransfer.squarefreeSharpRow
        (B.actualValuationLaw xi) B.partition (q.1 + r.1) j) =
        (fun j ↦ SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q.1 j) +
        (fun j ↦ SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition r.1 j) by
      funext j
      exact B.squarefreeSharpRow_add xi q.1 r.1 j]
    exact FiniteGraphStableInverse.meanProjection_add
      (MovingLowGaugeTransfer.sharpWeight
        B.partition.mass B.partition.center) _ _ i
  map_smul' c q := by
    apply Subtype.ext
    funext i
    change FiniteGraphQuotientInverse.meanProjection
        (MovingLowGaugeTransfer.sharpWeight
          B.partition.mass B.partition.center)
        (fun j ↦ SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition (c • q.1) j) i = _
    rw [show (fun j ↦ SquarefreeSharpBandTransfer.squarefreeSharpRow
        (B.actualValuationLaw xi) B.partition (c • q.1) j) =
        c • (fun j ↦ SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q.1 j) by
      funext j
      exact B.squarefreeSharpRow_smul xi c q.1 j]
    exact FiniteGraphStableInverse.meanProjection_smul
      (MovingLowGaugeTransfer.sharpWeight
        B.partition.mass B.partition.center) c _ i

def actualSquarefreeProjectedCLM
    [Nonempty Head] (xi : B.ParamSpace) :
    PaperWeightedInverseExport.SharpGaugeSpace
        B.partition.mass B.partition.center →L[ℝ]
      PaperWeightedInverseExport.SharpGaugeSpace
        B.partition.mass B.partition.center :=
  (B.actualSquarefreeProjectedLinearMap xi).toContinuousLinearMap





 theorem fullSharpRow_add
    [Nonempty Head]
    (xi : B.ParamSpace) (q r : Band → ℝ) (i : Band) :
    PrimePowerSharpBandTransfer.fullSharpRow
        (B.actualValuationLaw xi) B.partition (q + r) i =
      PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q i +
        PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition r i := by
  unfold PrimePowerSharpBandTransfer.fullSharpRow
    PrimePowerSharpBandTransfer.fullBandRow
  simp only [Pi.add_apply]
  have hinner (p : ArithmeticBandGeometry.BandPrime
      B.sampleData.n B.sampleData.W) :
      (∑ s : ArithmeticBandGeometry.BandPrime
          B.sampleData.n B.sampleData.W,
        B.partition.center (B.partition.band s) *
            (q (B.partition.band s) + r (B.partition.band s)) *
              (B.actualValuationLaw xi).covVV p.1 s.1) =
        (∑ s : ArithmeticBandGeometry.BandPrime
            B.sampleData.n B.sampleData.W,
          B.partition.center (B.partition.band s) * q (B.partition.band s) *
            (B.actualValuationLaw xi).covVV p.1 s.1) +
        ∑ s : ArithmeticBandGeometry.BandPrime
            B.sampleData.n B.sampleData.W,
          B.partition.center (B.partition.band s) * r (B.partition.band s) *
            (B.actualValuationLaw xi).covVV p.1 s.1 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _hs
    ring
  simp_rw [hinner]
  rw [Finset.sum_add_distrib]
  ring

 theorem fullSharpRow_smul
    [Nonempty Head]
    (xi : B.ParamSpace) (c : ℝ) (q : Band → ℝ) (i : Band) :
    PrimePowerSharpBandTransfer.fullSharpRow
        (B.actualValuationLaw xi) B.partition (c • q) i =
      c * PrimePowerSharpBandTransfer.fullSharpRow
        (B.actualValuationLaw xi) B.partition q i := by
  unfold PrimePowerSharpBandTransfer.fullSharpRow
    PrimePowerSharpBandTransfer.fullBandRow
  simp only [Pi.smul_apply, smul_eq_mul]
  have hinner (p : ArithmeticBandGeometry.BandPrime
      B.sampleData.n B.sampleData.W) :
      (∑ s : ArithmeticBandGeometry.BandPrime
          B.sampleData.n B.sampleData.W,
        B.partition.center (B.partition.band s) *
            (c * q (B.partition.band s)) *
              (B.actualValuationLaw xi).covVV p.1 s.1) =
        c * (∑ s : ArithmeticBandGeometry.BandPrime
          B.sampleData.n B.sampleData.W,
          B.partition.center (B.partition.band s) *
            q (B.partition.band s) *
              (B.actualValuationLaw xi).covVV p.1 s.1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _hs
    ring
  simp_rw [hinner]
  rw [← Finset.mul_sum]
  ring

/-- The literal full-valuation covariance operator, projected to the same
finite arithmetic sharp gauge as the squarefree operator. -/
def actualFullProjectedLinearMap
    [Nonempty Head] (xi : B.ParamSpace) :
    PaperWeightedInverseExport.SharpGaugeSpace
        B.partition.mass B.partition.center →ₗ[ℝ]
      PaperWeightedInverseExport.SharpGaugeSpace
        B.partition.mass B.partition.center where
  toFun q :=
    ⟨FiniteGraphQuotientInverse.meanProjection
        (MovingLowGaugeTransfer.sharpWeight
          B.partition.mass B.partition.center)
        (fun i ↦ PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q.1 i),
      FiniteGraphStableInverse.weighted_sum_meanProjection
        (MovingLowGaugeTransfer.sharpWeight
          B.partition.mass B.partition.center)
        (fun i ↦ PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q.1 i)
        (ne_of_gt (actualSharpWeightTotal_pos B))⟩
  map_add' q r := by
    apply Subtype.ext
    funext i
    change FiniteGraphQuotientInverse.meanProjection
        (MovingLowGaugeTransfer.sharpWeight
          B.partition.mass B.partition.center)
        (fun j ↦ PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition (q.1 + r.1) j) i = _
    rw [show (fun j ↦ PrimePowerSharpBandTransfer.fullSharpRow
        (B.actualValuationLaw xi) B.partition (q.1 + r.1) j) =
        (fun j ↦ PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q.1 j) +
        (fun j ↦ PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition r.1 j) by
      funext j
      exact B.fullSharpRow_add xi q.1 r.1 j]
    exact FiniteGraphStableInverse.meanProjection_add
      (MovingLowGaugeTransfer.sharpWeight
        B.partition.mass B.partition.center) _ _ i
  map_smul' c q := by
    apply Subtype.ext
    funext i
    change FiniteGraphQuotientInverse.meanProjection
        (MovingLowGaugeTransfer.sharpWeight
          B.partition.mass B.partition.center)
        (fun j ↦ PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition (c • q.1) j) i = _
    rw [show (fun j ↦ PrimePowerSharpBandTransfer.fullSharpRow
        (B.actualValuationLaw xi) B.partition (c • q.1) j) =
        c • (fun j ↦ PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q.1 j) by
      funext j
      exact B.fullSharpRow_smul xi c q.1 j]
    exact FiniteGraphStableInverse.meanProjection_smul
      (MovingLowGaugeTransfer.sharpWeight
        B.partition.mass B.partition.center) c _ i

def actualFullProjectedCLM
    [Nonempty Head] (xi : B.ParamSpace) :
    PaperWeightedInverseExport.SharpGaugeSpace
        B.partition.mass B.partition.center →L[ℝ]
      PaperWeightedInverseExport.SharpGaugeSpace
        B.partition.mass B.partition.center :=
  (B.actualFullProjectedLinearMap xi).toContinuousLinearMap





/-! ### Reference-law row attachment

The literal global-tilt form of Lemma 7.5 is naturally obtained first for an
unguarded component mixture.  The actual bridge law is a guard-deleted
mixture with a residual physical tilt.  The next elementary estimate keeps
that identification issue outside the prime-power algebra: a weighted
prime-row comparison for the full and squarefree covariance matrices moves
the Lemma 7.5 estimate from an arbitrary reference law to the actual law.
The only moving-low loss is displayed explicitly as `rho / center i`.
-/

 def sharpCovarianceRow
    (cov : ℕ → ℕ → ℝ)
    (P : Partition B.sampleData.n B.sampleData.W Band)
    (q : Band → ℝ) (i : Band) : ℝ :=
  ((1 / P.mass i) *
      ∑ p ∈ P.data.fiber i,
        ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          (P.center (P.band r) * q (P.band r)) * cov p.1 r.1) /
    P.center i



















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



/-- The actual full-valuation operator on the paper's raw arithmetic gauge,
before the finite nuisance regression. -/
def actualBandFullLinearMap [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) : B.RawBandGauge →ₗ[ℝ] B.RawBandGauge where
  toFun q := B.projectRawBandVector
    (B.normalizedBandCovarianceRow xi (B.bandRegressionScore q))
  map_add' q r := by
    rw [B.bandRegressionScore_add,
      B.normalizedBandCovarianceRow_add,
      B.projectRawBandVector_add]
  map_smul' c q := by
    rw [B.bandRegressionScore_smul,
      B.normalizedBandCovarianceRow_smul,
      B.projectRawBandVector_smul]
    rfl





/-- The literal nuisance-Schur operator transported to the sharp gauge in
which Lemma 8.4 supplies its inverse. -/
def actualSchurProjectedLinearMap [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) :
    SharpGaugeSpace B.partition.mass B.partition.center →ₗ[ℝ]
      SharpGaugeSpace B.partition.mass B.partition.center :=
  let S := scaleGaugeLinearEquiv B.partition.mass B.partition.center
    (B.partition.center_ne_zero B.n_gt_one)
  S.symm.toLinearMap.comp
    ((B.actualBandSchurLinearMap xi hgamma hgap).comp S.toLinearMap)

def actualSchurProjectedCLM [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) :
    SharpGaugeSpace B.partition.mass B.partition.center →L[ℝ]
      SharpGaugeSpace B.partition.mass B.partition.center :=
  (B.actualSchurProjectedLinearMap xi hgamma hgap).toContinuousLinearMap

@[simp] theorem actualSchurProjectedCLM_apply
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : SharpGaugeSpace B.partition.mass B.partition.center) :
    B.actualSchurProjectedCLM xi hgamma hgap q =
      (scaleGaugeLinearEquiv B.partition.mass B.partition.center
        (B.partition.center_ne_zero B.n_gt_one)).symm
        (B.actualBandSchurLinearMap xi hgamma hgap
          (scaleGaugeLinearEquiv B.partition.mass B.partition.center
            (B.partition.center_ne_zero B.n_gt_one) q)) := rfl

/-- Transport a sharp-gauge equivalence back to the paper's raw arithmetic
gauge by the exact centre scaling. -/
def rawBandEquivOfSharpEquiv [Nonempty Band]
    (e : SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
      SharpGaugeSpace B.partition.mass B.partition.center) :
    RawGaugeSpace B.partition.mass B.partition.center ≃ₗ[ℝ]
      RawGaugeSpace B.partition.mass B.partition.center :=
  let S := scaleGaugeLinearEquiv B.partition.mass B.partition.center
    (B.partition.center_ne_zero B.n_gt_one)
  S.symm.trans (e.toLinearEquiv.trans S)











end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperNuisancePrimeLogRows -/
section


/-!
# Exact logarithmic decomposition of the nuisance rows

The physical nuisance coordinate is not an unrelated marked statistic.  The
finite factorization identity in `BridgeData.HasPrimeLogCompatibility`
expresses the medium-prime logarithmic score as a nonzero multiple of the
physical logarithm plus a function of the fixed head tag.  This file solves
that identity for the physical score and does so inside an arbitrary nuisance
linear functional.

The resulting covariance-row identity is exact at finite `n`.  It is the
algebraic attachment used in Lemma 8.6 before applying the analytic estimates
for the prime-log null row and for cell-constant head rows.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

 def nuisanceCoordEquiv_PaperNuisancePrimeLogRows (I : Type*) :
    NuisanceCoord I ≃ Unit ⊕ I where
  toFun
    | .physical => Sum.inl ()
    | .head h => Sum.inr h
  invFun
    | Sum.inl _ => .physical
    | Sum.inr h => .head h
  left_inv c := by cases c <;> rfl
  right_inv
    | Sum.inl () => rfl
    | Sum.inr h => rfl



/-- The cell-constant head function carried by a nuisance vector after its
physical coordinate has been removed. -/
def nuisanceHeadFunction [Nonempty Head]
    (z : B.NuisanceSpace) (h₀ : Head) : ℝ :=
  ∑ h : B.HeadIndex,
    z (NuisanceCoord.head h) *
      ((if h₀ = h.1 then 1 else 0) - B.headBaselineMass h.1)









/-- The explicit tagged-head term in the paper's finite logarithmic
factorization. -/
def exactPrimeLogHeadFunction (h : Head) : ℝ :=
  (Real.log (B.sampleData.n : ℝ) - B.headLogScore h) /
    Real.log (ArithmeticModel.y B.sampleData.n)













/-- The centered indicator of one retained head pattern, regarded as a
function of the full head tag.  Writing this function explicitly lets the
component-mixture cancellation be applied to the literal nuisance
coordinate, rather than to an unnamed bounded tag function. -/
def centeredHeadTagFunction [Nonempty Head]
    (h : B.HeadIndex) (h₀ : Head) : ℝ :=
  (if h₀ = h.1 then 1 else 0) - B.headBaselineMass h.1

















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









/-- The exact Schur perturbation rate supplied by a reciprocal marked family.
The explicit `1 / amin` records the moving-low-cell loss. -/
def nuisanceMarkedSchurRate (Cmarked gamma amin : ℝ) : ℝ :=
  let droot := Real.sqrt
    (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  let moment := ∑ j : Band, B.harmonicMass j * B.bandCenter j
  (((droot * (Cmarked * moment)) / gamma) *
      (droot * Cmarked)) / amin









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



























/-- The target numerator with the norm split used in the paper. -/
def twoStageCompensatedTargetBoundOrdinaryFast
    (Creg Tband TslowCoord : ℝ) : ℝ :=
  (∑ j : Band, B.harmonicMass j * B.bandCenter j) *
      (Creg * B.w) * Tband +
    B.w * TslowCoord







end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87Assembly -/
section


/-!
# Finite assembly layer for Proposition 8.7

This file assembles the already proved finite exponential-family, ODE,
endpoint, marked-row, and feasibility statements in the literal effective
norm used in the paper.  It deliberately does not assert the analytic
estimates of Lemmas 8.4 and 8.6: the three hypotheses `hgap`, `hvelocity`,
and `hmarkedRow` are exactly the uniform analytic outputs which those lemmas
must supply on the effective box chosen before the path.

The conclusion is not packaged as an abstract contract.  It exhibits the
actual bridge path and states the individual band, physical, head,
logarithmic, marked-prime, natural-coordinate feasibility, frozen-coordinate,
mass, and integer-quota conclusions directly.
-/

open scoped BigOperators
open Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The literal frozen weight at a natural-number coordinate.  Several
tagged frozen summands are allowed to occupy the same coordinate, as happens
for a protected contribution superposed on a clean active coordinate. -/
def frozenAmbientWeight {Fixed : Type*} [Fintype Fixed]
    (fixedValue : Fixed → ℕ) (fixedWeight : Fixed → ℝ) (x : ℕ) : ℝ :=
  ∑ f : Fixed, if fixedValue f = x then fixedWeight f else 0

/-- The unnormalized ordinary logarithm whose moment the construction keeps
exact.  `physicalScore` differs from it only by the constant `log n`. -/
def ordinaryLogScore (m : B.sampleData.Sample) : ℝ :=
  Real.log (B.sampleData.value m : ℝ)







end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87CanonicalConclusion -/
section


/-!
# Literal endpoint package for paper Proposition 8.7

This is only a name for the conjunction proved by the exact finite ODE
assembly.  Every field is stated with the actual `BridgeData` moments,
weights, and valuation statistics.  In particular this is not a stylized
surrogate for Proposition 8.7; it is the reusable paper-level endpoint which
the canonical eventual theorem will produce.
-/

open scoped BigOperators
open Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The complete literal conclusion of the physically centered
fixed-partition fit.  The path clauses retain the stronger information used
to prove feasibility, while the endpoint clauses are exactly the paper's
moment, residual, frozen-layer, mass, and quota conclusions. -/
def HasPhysicallyCenteredFixedPartitionFit
    [Nonempty Head]
    {Fixed : Type*} [Fintype Fixed]
    (Delta : Band → ℝ) (a : NNReal)
    (monitoredPrimes : Finset ℕ)
    (markedTarget : ℕ → ℝ) (N Cpost : ℝ)
    (fixedValue : Fixed → ℕ) (fixedWeight : Fixed → ℝ)
    (quota : ℤ) : Prop :=
  ∃ path : ℝ → B.ParamSpace,
    path 0 = 0 ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
      B.effectiveParamEquiv.symm (path t) ∈
        closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
      B.paperEffectiveSize (path t) ≤ 3 * (a : ℝ)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt path
        (B.vectorFamily.vectorField (B.targetVector Delta) (path t))
        (Icc (0 : ℝ) 1) t) ∧
    (∀ j : Band,
      B.paperMoment (B.bandScore j) (path 1) =
        B.paperMoment (B.bandScore j) 0 + Delta j) ∧
    B.paperMoment B.physicalScore (path 1) =
      B.paperMoment B.physicalScore 0 ∧
    B.paperMoment B.ordinaryLogScore (path 1) =
      B.paperMoment B.ordinaryLogScore 0 ∧
    (∀ h : B.HeadIndex,
      B.paperMoment (B.headIndicator h.1) (path 1) =
        B.paperMoment (B.headIndicator h.1) 0) ∧
    (∀ p : ℕ, p.Prime → p ≤ B.sampleData.W →
      B.paperMoment (B.markedValuation p) (path 1) =
        B.paperMoment (B.markedValuation p) 0) ∧
    B.paperMoment B.primeLogScore (path 1) =
      B.paperMoment B.primeLogScore 0 ∧
    (∀ p ∈ monitoredPrimes,
      |markedTarget p - B.paperMoment (B.markedValuation p) (path 1)| ≤
        Cpost * N / ((p : ℝ) * B.L)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℕ,
      B.ambientCombinedWeight
          (frozenAmbientWeight fixedValue fixedWeight)
          (path t) x ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ f : Fixed,
      B.combinedWeight fixedWeight (path t) (Sum.inl f) =
        B.combinedWeight fixedWeight 0 (Sum.inl f)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
      (∑ m : B.sampleData.Sample,
        B.activeCoordinateWeight (path t) m) = B.q) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
      (∑ x : Fixed ⊕ B.sampleData.Sample,
        B.combinedWeight fixedWeight (path t) x) = (quota : ℝ)

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperPermittedRegularMesh -/
section


/-!
# The paper's two-sided relative-mesh condition

`RegularRelativeMesh.Mesh delta eta` records an exact common relative width
`M.ratio` and the upper estimate `M.ratio ≤ eta`.  The permitted meshes in
Section 8.4 of the paper also satisfy the lower estimate

`cMesh * eta ≤ M.ratio`.

Keeping that second estimate as a named proposition prevents an arbitrary
upper-width parameter from being confused with the actual mesh scale.  The
elementary lemmas below convert estimates at the actual scale
`delta + M.ratio` to the paper scale `delta + eta`, with constants depending
only on the fixed structural regularity constant `cMesh`.
-/

namespace Erdos390.Full.PaperPermittedRegularMesh

open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-- The lower half of the paper's two-sided relative regularity condition.
The upper half is already the field `M.ratio_le_eta`. -/
def IsPermitted {delta eta cMesh : ℝ} (M : Mesh delta eta) : Prop :=
  cMesh * eta ≤ M.ratio

namespace IsPermitted

variable {delta eta cMesh : ℝ} {M : Mesh delta eta}

























end IsPermitted

end

end Erdos390.Full.PaperPermittedRegularMesh

end

/- Source module: Erdos390.Full.PaperProposition87CanonicalStatement -/
section


/-!
# Paper-order canonical statement of Proposition 8.7

This file fixes the public statement before the analytic orchestration is
attached.  Its order is the one needed in the paper: choose `W`, then the
effective box and the mesh-independent residual constant, then an arbitrary
sufficiently fine permitted partition, and only last the ambient integer
`n`.  All rough-stage and feasibility data occur as their literal finite
envelopes or ledgers.  No covariance gap, inverse, target estimate, nuisance
row, marked row, speed inequality, or exponential-slack inequality occurs in
the statement.
-/

open scoped BigOperators
open Filter

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel PaperGuardCensus PaperPermittedRegularMesh
open RegularMeshPrimeCutoffs

/-- The exact canonical, eventual form of the physically centered
fixed-partition proposition. -/
def CanonicalProposition87Statement
    (cMesh : ℝ)
    (I : PhysicalIntervals) (U : ℝ)
    (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank) : Prop :=
  0 < cMesh →
  1 ≤ U →
  (∀ sigma, 1 ≤ I.lower sigma) →
  (∀ sigma, I.upper sigma ≤ U) →
  ∃ meshTol : ℝ, 0 < meshTol ∧
  ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
    ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
      (Phead : Head → HeadPattern.Pattern),
    (∀ h : Head, ∀ p : ℕ,
      p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
    ∀ (Ctarget Cinitial Cmass Cfixed Cactive marginFloor : ℝ),
      0 ≤ Ctarget → 0 ≤ Cinitial → 0 ≤ Cmass →
      0 ≤ Cfixed → 0 ≤ Cactive → 0 < marginFloor →
    ∃ a : NNReal, 0 < (a : ℝ) ∧
    ∃ Cpost : ℝ, 0 ≤ Cpost ∧
    ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
      (hdelta : 0 < delta)
      (_hPermitted : IsPermitted (cMesh := cMesh) M),
      delta + eta ≤ meshTol →
      ∀ᶠ n : ℕ in atTop,
        ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
          B.sampleData.n = n → B.sampleData.W = W →
          ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : ∀ c : Cell Head,
              (rawCell Phead I B.sampleData.n c \
                (ledger B.sampleData.n).guards).Nonempty),
            (hcanonical : B.sampleData = canonicalSampleData
              (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
                hsep hremaining) →
            (hpartition : ∃ (hWne : B.sampleData.W ≠ 0)
                (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
            (hscale : B.w = delta + eta) →
            ∀ (T : BarycentricTarget B.sampleData),
              marginFloor ≤ T.cellMassMargin →
              B.baseline = T.baseline →
            ∀ (Delta : Fin (M.cellCount + 1) → ℝ),
              B.HasTargetEnvelopes Ctarget Delta →
            ∀ (monitoredPrimes : Finset ℕ),
              (∀ p ∈ monitoredPrimes, p.Prime) →
              (∀ p ∈ monitoredPrimes, p ≤ yNat B.sampleData.n) →
            ∀ (markedTarget : ℕ → ℝ) (N : ℝ),
              0 ≤ N →
              B.q ≤ Cmass * N →
              (∀ p ∈ monitoredPrimes,
                |markedTarget p - B.paperMoment (B.markedValuation p) 0| ≤
                  Cinitial * N / ((p : ℝ) * B.L)) →
            ∀ {Fixed : Type*} [Fintype Fixed]
              (fixedValue : Fixed → ℕ) (fixedWeight : Fixed → ℝ)
              (quota : ℤ),
              (quota : ℝ) = (∑ f, fixedWeight f) + B.q →
              B.sampleData.HeadPatternsSeparated →
              (∀ x,
                BridgeData.frozenAmbientWeight fixedValue fixedWeight x ∈
                  Set.Icc (0 : ℝ) 1) →
              (∀ m : B.sampleData.Sample,
                BridgeData.frozenAmbientWeight fixedValue fixedWeight
                  (B.sampleData.value m) ≤ Cfixed / B.L) →
              (∀ m : B.sampleData.Sample,
                B.baseline.baseWeight m ≤ Cactive / B.L) →
              B.HasPhysicallyCenteredFixedPartitionFit Delta a
                monitoredPrimes markedTarget N Cpost
                fixedValue fixedWeight quota

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.FiniteAnchoredDirichletQuadratic -/
section


/-!
# Finite anchored Dirichlet quadratic forms

This file records the exact finite algebra needed in the slow-direction
part of paper Lemma 8.6.  A symmetric reference covariance is a graph
Dirichlet energy plus its (possibly nonzero) discrete row-sum residual.
A positive block of anchor vertices then controls the quotient distance to
the constant direction.  The statements are entirely finite; in
particular, no continuum limit or spectral-gap hypothesis is hidden in the
algebra.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.FiniteAnchoredDirichletQuadratic

variable {ι : Type*} [Fintype ι]

/-- The finite reference quadratic with vertex weight `weight`, diagonal
multiplier `diagonal`, and symmetric signed kernel `kernel`. -/
def referenceQuadratic
    (weight diagonal : ι → ℝ) (kernel : ι → ι → ℝ) (x : ι → ℝ) : ℝ :=
  (∑ i, weight i * diagonal i * x i ^ 2) +
    ∑ i, ∑ j, weight i * weight j * kernel i j * x i * x j

/-- The positive-sign convention for the graph energy associated with the
signed kernel. -/
def dirichletEnergy
    (weight : ι → ℝ) (kernel : ι → ι → ℝ) (x : ι → ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ i, ∑ j,
      weight i * weight j * (-kernel i j) * (x i - x j) ^ 2

/-- The error in the discrete analogue of the continuum row-sum identity. -/
def rowResidual
    (weight diagonal : ι → ℝ) (kernel : ι → ι → ℝ) (i : ι) : ℝ :=
  diagonal i + ∑ j, weight j * kernel i j



/-- Harmonic mass of a finite anchor set. -/
def anchorMass (weight : ι → ℝ) (anchor : Finset ι) : ℝ :=
  ∑ j ∈ anchor, weight j

/-- Weighted square distance to a scalar representative of the constant
direction. -/
def weightedDistance (metricWeight : ι → ℝ) (x : ι → ℝ) (mu : ℝ) : ℝ :=
  ∑ i, metricWeight i * (x i - mu) ^ 2

/-- Pair variation between every vertex and the anchor block. -/
def anchorPairVariation
    (metricWeight anchorWeight : ι → ℝ) (anchor : Finset ι)
    (x : ι → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ anchor,
    metricWeight i * anchorWeight j * (x i - x j) ^ 2





end Erdos390.Full.FiniteAnchoredDirichletQuadratic

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

abbrev PrimeIndex (n W : ℕ) := {p : ℕ // p ∈ primeBand n W}

variable {n W : ℕ}

instance : Fintype (PrimeIndex n W) :=
  Fintype.ofFinset (primeBand n W) (fun _ ↦ Iff.rfl)

/-- The conjugated vertex measure `t_p / p`. -/
def primeWeight (n : ℕ) (p : PrimeIndex n W) : ℝ :=
  tPrime n p.1 / (p.1 : ℝ)

/-- The physical quotient metric `t_p^2 / p`. -/
def primeMetricWeight (n : ℕ) (p : PrimeIndex n W) : ℝ :=
  tPrime n p.1 ^ 2 / (p.1 : ℝ)

def primeDiagonal (n : ℕ) (p : PrimeIndex n W) : ℝ :=
  DickmanBasic.F (tPrime n p.1) * tPrime n p.1

def primeKernel (n : ℕ) (p q : PrimeIndex n W) : ℝ :=
  covarianceKernel (tPrime n p.1) (tPrime n q.1)

def dirichletCoordinate (n : ℕ)
    (c : PrimeIndex n W → ℝ) (p : PrimeIndex n W) : ℝ :=
  c p / tPrime n p.1

/-- The separated diagonal-plus-kernel form of the prime reference
quadratic. -/
def primeReferenceQuadratic (n : ℕ)
    (c : PrimeIndex n W → ℝ) : ℝ :=
  (∑ p, DickmanBasic.F (tPrime n p.1) / (p.1 : ℝ) * c p ^ 2) +
    ∑ p, ∑ q,
      covarianceKernel (tPrime n p.1) (tPrime n q.1) /
          ((p.1 : ℝ) * (q.1 : ℝ)) * c p * c q

/-- The same reference quadratic written with the literal primewise matrix
entry used by the signed squarefree comparison. -/
def primeReferenceEntryQuadratic (n : ℕ)
    (c : PrimeIndex n W → ℝ) : ℝ :=
  ∑ p, ∑ q, c p * c q * squarefreeReferenceEntry n p.1 q.1

/-- Literal prime quotient distance. -/
def primePhysicalDistance (n : ℕ)
    (c : PrimeIndex n W → ℝ) (mu : ℝ) : ℝ :=
  ∑ p, (1 / (p.1 : ℝ)) * (c p - mu * tPrime n p.1) ^ 2

/-- Literal reciprocal-weighted coefficient square norm. -/
def primeCoefficientL2Sq (c : PrimeIndex n W → ℝ) : ℝ :=
  ∑ p, (1 / (p.1 : ℝ)) * c p ^ 2























/-- Weighted mean on a nonempty positive-mass anchor block. -/
def anchorMean (n : ℕ) (anchor : Finset (PrimeIndex n W))
    (c : PrimeIndex n W → ℝ) : ℝ :=
  (∑ p ∈ anchor, primeWeight n p * dirichletCoordinate n c p) /
    anchorMass (primeWeight n) anchor







end Erdos390.Full.PrimeSquarefreeDirichletGeometry

end

/- Source module: Erdos390.Full.FiniteSignedQuadraticEntryTransfer -/
section


/-!
# Entrywise transfer for finite signed quadratic forms

This is the exact finite summation used to pass from the signed Dickman
reference matrix to the genuine squarefree covariance matrix.  In
particular, the proof keeps the off-diagonal product-reciprocal error and
the two diagonal errors separate; it never replaces a sum of absolute
values by the absolute value of a sum.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.FiniteSignedQuadraticEntryTransfer

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixQuadratic (A : ι → ι → ℝ) (c : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * A i j

def weightedL1 (weight : ι → ℝ) (c : ι → ℝ) : ℝ :=
  ∑ i, weight i * |c i|

def weightedL2Sq (weight : ι → ℝ) (c : ι → ℝ) : ℝ :=
  ∑ i, weight i * c i ^ 2

def weightedL2SqSecond (weight : ι → ℝ) (c : ι → ℝ) : ℝ :=
  ∑ i, weight i ^ 2 * c i ^ 2



end Erdos390.Full.FiniteSignedQuadraticEntryTransfer

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

abbrev Prime (n W : ℕ) := PrimeIndex n W

def reciprocalWeight (p : Prime n W) : ℝ := 1 / (p.1 : ℝ)

def compensatedPrimeCoefficient
    (q : PaperWeightedInverseExport.RawGaugeSpace P.mass P.center)
    (p : Prime n W) : ℝ :=
  P.compensatedCoefficient q p

/-- The genuine squarefree covariance quadratic, indexed by the actual
prime subtype. -/
def subtypeSquarefreeQuadratic {Omega : Type*} [Fintype Omega] {M : ℕ}
    (law : BoundedValuationLaw Omega M) (c : Prime n W → ℝ) : ℝ :=
  matrixQuadratic (fun p r ↦ law.covII p.1 r.1) c





















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

def slowL1Constant (C K : ℝ) : ℝ := 7 + C * K

def slowL2Constant (C K : ℝ) : ℝ := 2 * (4 + C ^ 2 * K)

def signedSecondConstant (Eprofile CKernel : ℝ) : ℝ :=
  (1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 + CKernel















end BridgeData

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalSlowKappa -/
section


/-!
# A fixed slow-direction Dickman gap

The compact interior anchor is always taken in `[1/8,7/8]`.  Hence its
Dickman quotient gap must be selected once, before `n`, the arithmetic mesh,
and every tilt parameter.  This file exposes that fixed choice and threads
it through the exact prime Dirichlet and squarefree lower bounds.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PaperCanonicalSlowKappa

open ArithmeticModel ArithmeticBandGeometry
open ConditionedPoissonLimit PoissonDickmanWeightedInverse
open PoissonDickmanDirichlet OmittedTiltPairChamber
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open PaperSquarefreeSlowQuadraticLower
open PaperBridgeFit PaperBridgeFit.BridgeData
open PaperPrimePowerChamberError
open PaperWeightedInverseExport
open FiniteSignedQuadraticEntryTransfer
open SquarefreeCovarianceReference
open PrimePowerCovariance

/-- The one compact Dickman quotient gap used by every canonical slow
estimate. -/
def canonicalSlowKappa : ℝ :=
  Classical.choose
    (exists_transposeQuotient_uniform_gap
      (epsilon := (1 / 8 : ℝ)) (by norm_num) (by norm_num))









end Erdos390.Full.PaperCanonicalSlowKappa

namespace Erdos390.Full.PaperBridgeFit.BridgeData

open ArithmeticModel ArithmeticBandGeometry
open ConditionedPoissonLimit OmittedTiltPairChamber
open PrimeSquarefreeDirichletGeometry FiniteAnchoredDirichletQuadratic
open PaperSquarefreeSlowQuadraticLower PaperPrimePowerChamberError
open PaperWeightedInverseExport FiniteSignedQuadraticEntryTransfer
open SquarefreeCovarianceReference PrimePowerCovariance
open PaperCanonicalSlowKappa

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)





end Erdos390.Full.PaperBridgeFit.BridgeData

end

end

/- Source module: Erdos390.Full.PaperCanonicalActualBandQuadraticTransfer -/
section


/-!
# Fixed-kappa actual band and nuisance-Schur gaps

This file is the fixed-constant counterpart of the existential quadratic
transfer in `PaperActualBandQuadraticTransfer`.  The structural constant is
the single continuum constant `PaperCanonicalSlowKappa.canonicalSlowKappa`;
it is therefore selected before the arithmetic mesh, the cutoff, and every
finite-`n` law.  All finite row, signed-profile, prime-power, and nuisance
losses remain displayed as coefficients of the literal arithmetic `D`-norm.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PaperCanonicalActualBandQuadraticTransfer

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open PaperBandQuadraticGeometry
open PaperCanonicalSlowKappa
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open FiniteSignedQuadraticEntryTransfer
open PaperSquarefreeSlowQuadraticLower
open SquarefreeCovarianceReference

variable {Omega : Type*} [Fintype Omega] {M n W : ℕ}
variable {Band : Type*} [Fintype Band] [DecidableEq Band]

/-- Full-valuation covariance quadratic on the literal prime subtype. -/
def subtypeFullQuadratic (law : BoundedValuationLaw Omega M)
    (c : PrimeIndex n W → ℝ) : ℝ :=
  matrixQuadratic (fun p r ↦ law.covVV p.1 r.1) c























end Erdos390.Full.PaperCanonicalActualBandQuadraticTransfer

namespace Erdos390.Full.PaperBridgeFit.BridgeData

open ArithmeticModel ArithmeticBandGeometry
open PaperCanonicalSlowKappa
open PaperCanonicalActualBandQuadraticTransfer
open PaperPrimePowerChamberError
open PaperWeightedInverseExport
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open PaperSquarefreeSlowQuadraticLower
open FiniteSignedQuadraticEntryTransfer
open SquarefreeCovarianceReference
open OmittedTiltPairChamber

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : PaperBridgeFit.BridgeData Head Band)



/-- Literal full-valuation score for an arbitrary coefficient on the actual
prime subtype. -/
def primeValuationScore
    (c : BandPrime B.sampleData.n B.sampleData.W → ℝ)
    (m : B.sampleData.Sample) : ℝ :=
  ∑ p : BandPrime B.sampleData.n B.sampleData.W,
    c p * valuation p.1 (B.sampleData.value m)



















end Erdos390.Full.PaperBridgeFit.BridgeData

end

end

/- Source module: Erdos390.Full.PaperCanonicalActualFullQuotientNullIdentification -/
section


/-!
# Exact prime-log null identification for the fixed-kappa quotient gap

The arithmetic quotient lower bound is naturally proved after minimizing the
coefficient `b_{j(p)} - mu t_p` over the physical logarithmic direction.  The
actual main score, however, carries a prescribed value of `mu` coming from
the stored slow coordinate.  This file proves at finite `n` that the two
scores have exactly the same nuisance-Schur quadratic form: their difference
is a multiple of `primeLogScore`, and the latter is an affine nuisance score.

No continuum limit or covariance approximation occurs here.  In particular,
the arbitrary band vector is retained throughout; the slow/`alpha` direction
is not discarded by restricting to the raw gauge.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperCanonicalSlowKappa
open PaperCanonicalActualBandQuadraticTransfer
open PaperPrimePowerChamberError
open PaperWeightedInverseExport
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open PaperSquarefreeSlowQuadraticLower
open FiniteSignedQuadraticEntryTransfer
open SquarefreeCovarianceReference
open OmittedTiltPairChamber

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The nuisance vector whose physical coordinate is `a` and whose centered
head coordinates represent `phi` modulo the reference head. -/
def physicalHeadNuisanceVector [Nonempty Head]
    (a : ℝ) (phi : Head → ℝ) : B.NuisanceSpace :=
  (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).symm
    (fun c => match c with
      | .physical => a
      | .head h => phi h.1 - phi B.referenceHead)

@[simp] theorem physicalHeadNuisanceVector_physical [Nonempty Head]
    (a : ℝ) (phi : Head → ℝ) :
    B.physicalHeadNuisanceVector a phi NuisanceCoord.physical = a := rfl

@[simp] theorem physicalHeadNuisanceVector_head [Nonempty Head]
    (a : ℝ) (phi : Head → ℝ) (h : B.HeadIndex) :
    B.physicalHeadNuisanceVector a phi (NuisanceCoord.head h) =
      phi h.1 - phi B.referenceHead := rfl

/-- The deterministic term created when ordinary head indicators are
rewritten as the centered nuisance head indicators. -/
def physicalHeadAffineConstant [Nonempty Head]
    (phi : Head → ℝ) : ℝ :=
  phi B.referenceHead +
    ∑ h : B.HeadIndex,
      (phi h.1 - phi B.referenceHead) * B.headBaselineMass h.1











































end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.ContinuumRowResidualBound -/
section


/-!
# An explicit moving-low bound for the continuum row residual

Harmonic cell centers need not be close pointwise to the coordinate in the
moving low cell.  The correct cancellation is instead
`center * ∫ dt/t = ∫ dt`.  This file exploits that exact identity before
taking absolute values.  Consequently the residual is controlled by the
ordinary modulus of continuity of `F` and of the removable kernel on the
closed physical square, together with the omitted initial tail.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full
namespace ContinuumCellGraph
namespace IntervalMesh

open MeasureTheory
open ConditionedPoissonLimit
open DickmanBasic
open PoissonDickmanWeightedInverse

variable {Band : Type*} [Fintype Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)



/-- Exact coverage information for a finite mesh of the truncated physical
interval `[base,1]`.  It is purely interval combinatorics; no covariance
gap, inverse, or residual estimate is stored here. -/
structure TailPartitionCertificate where
  base : ℝ
  base_nonneg : 0 ≤ base
  base_le_one : base ≤ 1
  totalLength : ∑ j, M.length j = 1 - base
  kernelIntegral_split : ∀ s,
    (∑ j, ∫ t in M.lower j..M.upper j,
      covarianceKernelQuotient t s) =
      ∫ t in base..1, covarianceKernelQuotient t s
  kernelDoubleIntegral_split : ∀ i,
    (∑ j, ∫ s in M.lower i..M.upper i,
      ∫ t in M.lower j..M.upper j,
        covarianceKernelQuotient t s) =
      ∫ s in M.lower i..M.upper i,
        ∫ t in base..1, covarianceKernelQuotient t s







/-- Input-cell contribution to the physical-null residual after the exact
harmonic-center cancellation is exposed. -/
def inputCellResidual (i j : Band) : ℝ :=
  ∫ s in M.lower i..M.upper i,
    (M.center j *
      (∫ t in M.lower j..M.upper j,
        covarianceKernelQuotient t s / t) -
      ∫ t in M.lower j..M.upper j,
        covarianceKernelQuotient t s)



/-- Omitted initial kernel tail in one output cell. -/
def kernelTailResidual (base : ℝ) (i : Band) : ℝ :=
  ∫ s in M.lower i..M.upper i,
    ∫ t in (0 : ℝ)..base, covarianceKernelQuotient t s



















end IntervalMesh
end ContinuumCellGraph
end Erdos390.Full

end

/- Source module: Erdos390.Full.ContinuumTwoTailResidualBound -/
section


/-!
# Continuum row residual with both endpoint tails

For the literal arithmetic endpoint mesh the last endpoint is
`log(floor y)/log y`, not exactly `1`.  This file keeps both omitted tails
explicit.  It closes the top-endpoint gap without changing the continuum
operator or pretending that `floor y = y`.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full
namespace ContinuumCellGraph
namespace IntervalMesh

open MeasureTheory
open ConditionedPoissonLimit
open DickmanBasic
open PoissonDickmanWeightedInverse

variable {Band : Type*} [Fintype Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

/-- Exact coverage of a middle interval `[base, top]`. -/
structure TwoTailPartitionCertificate where
  base : ℝ
  upperEnd : ℝ
  base_nonneg : 0 ≤ base
  base_le_upperEnd : base ≤ upperEnd
  upperEnd_le_one : upperEnd ≤ 1
  totalLength : ∑ j, M.length j = upperEnd - base
  kernelDoubleIntegral_split : ∀ i,
    (∑ j, ∫ s in M.lower i..M.upper i,
      ∫ t in M.lower j..M.upper j,
        covarianceKernelQuotient t s) =
      ∫ s in M.lower i..M.upper i,
        ∫ t in base..upperEnd, covarianceKernelQuotient t s

/-- Omitted upper kernel tail in one output cell. -/
def kernelUpperTailResidual (top : ℝ) (i : Band) : ℝ :=
  ∫ s in M.lower i..M.upper i,
    ∫ t in top..1, covarianceKernelQuotient t s













end IntervalMesh
end ContinuumCellGraph
end Erdos390.Full

end

/- Source module: Erdos390.Full.CanonicalEndpointTwoTailCertificate -/
section


/-!
# Exact two-tail coverage of the canonical endpoint mesh

Consecutive natural cutoffs telescope exactly.  The first endpoint is the
fixed cutoff coordinate and the last is the `floor y` coordinate, so this
produces the two-tail certificate required by the honest residual theorem.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel RegularRelativeMesh
open KernelPrimeQuadrature
open ConditionedPoissonLimit
open ContinuumCellGraph
open ContinuumCellGraph.IntervalMesh
open MeasureTheory

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

 theorem continuous_inner_endpointKernel
    (a b : ℝ) :
    Continuous (fun s : ℝ =>
      ∫ t in a..b, covarianceKernelQuotient t s) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (a₀ := a) (b₀ := b)
  exact continuous_uncurry_covarianceKernelQuotient.comp
    (continuous_snd.prodMk continuous_fst)

/-- The canonical interval mesh covers exactly from the coordinate of `W`
to the coordinate of `floor y`. -/
def canonicalTwoTailCertificate
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (hWTwo : 2 ≤ W)
    (S : ScaleSeparation M n W)
    (epsilon : ℝ) (anchorCell : Fin M.cellCount)
    (hInteriorLower hInteriorUpper) :
    let IM := canonicalIntervalMesh M hdelta hn hW hWTwo S
      epsilon anchorCell hInteriorLower hInteriorUpper
    IM.TwoTailPartitionCertificate := by
  let E := canonicalCertificate M hdelta hn hW S
  let IM := canonicalIntervalMesh M hdelta hn hW hWTwo S
    epsilon anchorCell hInteriorLower hInteriorUpper
  let a : ℕ → ℝ := fun k =>
    realLogCoordinate (y n) (fullCutoff M n W k : ℝ)
  have hylog : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
  have hbasePos : 0 < a 0 := by
    dsimp only [a, fullCutoff]
    unfold realLogCoordinate
    exact div_pos (Real.log_pos (by exact_mod_cast (show 1 < W by omega))) hylog
  have hmono : Monotone (fullCutoff M n W) :=
    fullCutoff_monotone M hdelta hn (W_le_first_fullCutoff M S)
  have haMono : Monotone a := by
    intro r s hrs
    dsimp only [a]
    have hrTwo : 2 ≤ fullCutoff M n W r :=
      hWTwo.trans (hmono (Nat.zero_le r))
    exact DoubleKernelPrimeQuadrature.realLogCoordinate_mono_nat
      (by
        exact (Real.log_pos_iff (Scale.y_pos
          (Nat.zero_lt_of_lt hn)).le).mp hylog)
      hrTwo (hmono hrs)
  have htopOne : a (M.cellCount + 1) ≤ 1 := by
    dsimp only [a]
    rw [fullCutoff_last M (Nat.zero_lt_of_lt hn)]
    have hypos := Scale.y_pos (Nat.zero_lt_of_lt hn)
    have hfloorPos : (0 : ℝ) < (yNat n : ℝ) := by
      have : 2 ≤ yNat n := by
        rw [← fullCutoff_last M (Nat.zero_lt_of_lt hn)]
        exact hWTwo.trans (hmono (Nat.zero_le _))
      positivity
    unfold realLogCoordinate
    apply (div_le_iff₀ hylog).2
    simpa only [one_mul] using Real.log_le_log hfloorPos
      (Nat.floor_le hypos.le)
  refine {
    base := a 0
    upperEnd := a (M.cellCount + 1)
    base_nonneg := hbasePos.le
    base_le_upperEnd := haMono (Nat.zero_le _)
    upperEnd_le_one := htopOne
    totalLength := ?_
    kernelDoubleIntegral_split := ?_
  }
  · change (∑ j : Fin (M.cellCount + 1),
        (a (j.1 + 1) - a j.1)) =
      a (M.cellCount + 1) - a 0
    calc
      (∑ j : Fin (M.cellCount + 1), (a (j.1 + 1) - a j.1)) =
          ∑ k ∈ Finset.range (M.cellCount + 1),
            (a (k + 1) - a k) := by
        simpa only using Fin.sum_univ_eq_sum_range
          (fun k : ℕ => a (k + 1) - a k) (M.cellCount + 1)
      _ = a (M.cellCount + 1) - a 0 := by
        rw [Finset.sum_range_sub]
  · intro i
    change (∑ j : Fin (M.cellCount + 1),
      ∫ s in a i.1..a (i.1 + 1),
        ∫ t in a j.1..a (j.1 + 1),
          covarianceKernelQuotient t s) =
      ∫ s in a i.1..a (i.1 + 1),
        ∫ t in a 0..a (M.cellCount + 1),
          covarianceKernelQuotient t s
    rw [← intervalIntegral.integral_finset_sum]
    · apply intervalIntegral.integral_congr
      intro s hs
      change (∑ j : Fin (M.cellCount + 1),
          ∫ t in a j.1..a (j.1 + 1),
            covarianceKernelQuotient t s) =
        ∫ t in a 0..a (M.cellCount + 1),
          covarianceKernelQuotient t s
      calc
        (∑ j : Fin (M.cellCount + 1),
            ∫ t in a j.1..a (j.1 + 1),
              covarianceKernelQuotient t s) =
            ∑ k ∈ Finset.range (M.cellCount + 1),
              ∫ t in a k..a (k + 1),
                covarianceKernelQuotient t s := by
          simpa only using Fin.sum_univ_eq_sum_range
            (fun k : ℕ =>
              ∫ t in a k..a (k + 1), covarianceKernelQuotient t s)
            (M.cellCount + 1)
        _ = _ := intervalIntegral.sum_integral_adjacent_intervals
          (fun k hk =>
            (continuous_uncurry_covarianceKernelQuotient.comp
              (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)
    · intro j hj
      exact (continuous_inner_endpointKernel (a j.1) (a (j.1 + 1))).intervalIntegrable _ _

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.CanonicalEndpointMultiAnchorIntervalMesh -/
section


/-!
# Canonical endpoint meshes with a positive-mass interior anchor block

The earlier singleton-anchor constructor is convenient for a fixed mesh,
but its inverse constant degenerates when that one cell is refined.  This
file keeps the same literal endpoint cells and allows a finite collection of
positive cells to supply the interior anchor.  The operator entries are
unchanged; only the graph anchor measure is enlarged.
-/

open Set
open scoped BigOperators

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel RegularRelativeMesh
open KernelPrimeQuadrature DoubleKernelPrimeQuadrature
open ContinuumCellGraph

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- The positive-band inclusion as a finite-set embedding. -/
def positiveBandEmbedding : Fin M.cellCount ↪ Fin (M.cellCount + 1) where
  toFun := positiveBand M
  inj' := by
    intro i j hij
    apply Fin.ext
    have hij' := congrArg Fin.val hij
    change i.1 + 1 = j.1 + 1 at hij'
    omega

/-- Exact logarithmic-coordinate interval mesh whose interior anchor is the
union of the selected positive cells. -/
def canonicalIntervalMeshOfAnchors
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (hWTwo : 2 ≤ W)
    (S : ScaleSeparation M n W)
    (epsilon : ℝ) (anchors : Finset (Fin M.cellCount))
    (hAnchors : anchors.Nonempty)
    (hInteriorLower : ∀ k ∈ anchors, epsilon ≤
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).lower
          (positiveBand M k) : ℝ))
    (hInteriorUpper : ∀ k ∈ anchors,
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).upper
          (positiveBand M k) : ℝ) ≤ 1 - epsilon) :
    IntervalMesh epsilon (Fin (M.cellCount + 1)) where
  lower j := realLogCoordinate (y n)
    ((canonicalCertificate M hdelta hn hW S).lower j : ℝ)
  upper j := realLogCoordinate (y n)
    ((canonicalCertificate M hdelta hn hW S).upper j : ℝ)
  lower_pos j := by
    apply realLogCoordinate_pos_nat
    · have hlog : 0 < Real.log (y n) := by
        rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
        exact mul_pos (by norm_num)
          (Real.log_pos (by exact_mod_cast hn))
      exact (Real.log_pos_iff (Scale.y_pos
        (Nat.zero_lt_of_lt hn)).le).mp hlog
    · exact hWTwo.trans
        (canonicalCertificate_lower_ge_cutoff M hdelta hn hW S j)
  lower_lt_upper j := by
    let E := canonicalCertificate M hdelta hn hW S
    obtain ⟨p, hpPrime, hpLower, hpUpper⟩ :=
      every_fullCutoff_cell_has_prime M hW S j
    have hCut : E.lower j < E.upper j := by
      change fullCutoff M n W j.1 < fullCutoff M n W (j.1 + 1)
      exact hpLower.trans_le hpUpper
    have hLowerPos : (0 : ℝ) < (E.lower j : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < W)
        (canonicalCertificate_lower_ge_cutoff M hdelta hn hW S j))
    have hUpperPos : (0 : ℝ) < (E.upper j : ℝ) :=
      hLowerPos.trans (by exact_mod_cast hCut)
    unfold realLogCoordinate
    exact div_lt_div_of_pos_right
      (Real.strictMonoOn_log hLowerPos hUpperPos (by exact_mod_cast hCut))
      (by
        rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
        exact mul_pos (by norm_num)
          (Real.log_pos (by exact_mod_cast hn)))
  upper_le_one j := by
    let E := canonicalCertificate M hdelta hn hW S
    have hypos : 0 < y n := Scale.y_pos (Nat.zero_lt_of_lt hn)
    have hUpperPos : (0 : ℝ) < (E.upper j : ℝ) := by
      have hLower := canonicalCertificate_lower_ge_cutoff
        M hdelta hn hW S j
      have hle := E.lower_le_upper j
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < W) (hLower.trans hle))
    have hUpperY : (E.upper j : ℝ) ≤ y n := by
      exact (by exact_mod_cast E.upper_le_yNat j :
        (E.upper j : ℝ) ≤ (yNat n : ℝ)) |>.trans
          (Nat.floor_le hypos.le)
    unfold realLogCoordinate
    apply (div_le_iff₀ (Real.log_pos (by
      have hlog : 0 < Real.log (y n) := by
        rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
        exact mul_pos (by norm_num)
          (Real.log_pos (by exact_mod_cast hn))
      exact (Real.log_pos_iff hypos.le).mp hlog))).2
    simpa only [one_mul] using Real.log_le_log hUpperPos hUpperY
  interiorCells := anchors.map (positiveBandEmbedding M)
  interior_lower j hj := by
    rw [Finset.mem_map] at hj
    obtain ⟨k, hk, rfl⟩ := hj
    exact hInteriorLower k hk
  interior_upper j hj := by
    rw [Finset.mem_map] at hj
    obtain ⟨k, hk, rfl⟩ := hj
    exact hInteriorUpper k hk
  interiorTotal_pos := by
    obtain ⟨k, hk⟩ := hAnchors
    let IM₁ := canonicalIntervalMesh M hdelta hn hW hWTwo S epsilon k
      (hInteriorLower k hk) (hInteriorUpper k hk)
    apply Finset.sum_pos
    · intro j hj
      exact sub_pos.mpr (by
        simpa only [IM₁, canonicalIntervalMesh] using IM₁.lower_lt_upper j)
    · exact ⟨positiveBand M k,
        (Finset.mem_map' (positiveBandEmbedding M)).2 hk⟩

@[simp] theorem canonicalIntervalMeshOfAnchors_lower
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (hWTwo : 2 ≤ W)
    (S : ScaleSeparation M n W)
    (epsilon : ℝ) (anchors : Finset (Fin M.cellCount))
    (hAnchors hInteriorLower hInteriorUpper)
    (j : Fin (M.cellCount + 1)) :
    (canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon anchors
      hAnchors hInteriorLower hInteriorUpper).lower j =
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).lower j : ℝ) := rfl

@[simp] theorem canonicalIntervalMeshOfAnchors_upper
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (hWTwo : 2 ≤ W)
    (S : ScaleSeparation M n W)
    (epsilon : ℝ) (anchors : Finset (Fin M.cellCount))
    (hAnchors hInteriorLower hInteriorUpper)
    (j : Fin (M.cellCount + 1)) :
    (canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon anchors
      hAnchors hInteriorLower hInteriorUpper).upper j =
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).upper j : ℝ) := rfl

/-- The multi-anchor mesh has the same exact endpoint coverage as the
singleton constructor. -/
def canonicalTwoTailCertificateOfAnchors
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (hWTwo : 2 ≤ W)
    (S : ScaleSeparation M n W)
    (epsilon : ℝ) (anchors : Finset (Fin M.cellCount))
    (hAnchors : anchors.Nonempty)
    (anchor : Fin M.cellCount) (hAnchor : anchor ∈ anchors)
    (hInteriorLower : ∀ k ∈ anchors, epsilon ≤
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).lower
          (positiveBand M k) : ℝ))
    (hInteriorUpper : ∀ k ∈ anchors,
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).upper
          (positiveBand M k) : ℝ) ≤ 1 - epsilon) :
    let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S
      epsilon anchors hAnchors hInteriorLower hInteriorUpper
    IM.TwoTailPartitionCertificate := by
  let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S
    epsilon anchors hAnchors hInteriorLower hInteriorUpper
  let IM₁ := canonicalIntervalMesh M hdelta hn hW hWTwo S epsilon anchor
    (hInteriorLower anchor hAnchor) (hInteriorUpper anchor hAnchor)
  let T₁ := canonicalTwoTailCertificate M hdelta hn hW hWTwo S epsilon anchor
    (hInteriorLower anchor hAnchor) (hInteriorUpper anchor hAnchor)
  exact {
    base := T₁.base
    upperEnd := T₁.upperEnd
    base_nonneg := T₁.base_nonneg
    base_le_upperEnd := T₁.base_le_upperEnd
    upperEnd_le_one := T₁.upperEnd_le_one
    totalLength := by
      simpa only [IM, IM₁, canonicalIntervalMeshOfAnchors,
        canonicalIntervalMesh] using T₁.totalLength
    kernelDoubleIntegral_split := by
      intro i
      simpa only [IM, IM₁, canonicalIntervalMeshOfAnchors,
        canonicalIntervalMesh] using T₁.kernelDoubleIntegral_split i
  }

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.CanonicalEndpointMeshGeometryEventually -/
section


/-!
# Eventual geometry of the literal canonical endpoint mesh

The first endpoint is the fixed cutoff `W` and the last is `floor y`.
This file proves, rather than assumes, that the two omitted tails vanish and
that every actual floored cell inherits any strict upper bound satisfied by
its ideal regular-mesh length.
-/

open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel RegularRelativeMesh KernelPrimeQuadrature

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- Logarithmic coordinate of one literal natural cutoff, for a general
regular mesh whose two parameters need not coincide. -/
def actualCutoffCoordinate (n W r : ℕ) : ℝ :=
  realLogCoordinate (y n) (fullCutoff M n W r : ℝ)











end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.CanonicalEndpointRelativeCenterEventually -/
section


/-!
# Relative centre convergence for the canonical endpoint family

This is the endpoint-level convergence needed by the moving-low sharp
projection.  In particular the conclusion is relative even on the low band,
whose centre tends to zero.  Constants in the two PNT estimates are selected
before the cutoff and before `n`.
-/

open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer PrimeBandQuadrature MovingLowMomentQuadrature
open MovingLowGaugeTransfer KernelPrimeQuadrature

/- The cutoff is chosen solely from the two global prime-sum estimates.  In
particular it is definitionally independent of every later regular mesh. -/
noncomputable def canonicalRelativeCenterCutoff : ℕ :=
  max 2 (max PrimeBandQuadrature.fullReciprocalSumUniformCutoff
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff)

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- Endpoint continuum mass, before mentioning a partition proof. -/
def endpointContinuumMass (n W : ℕ) (j : Fin (M.cellCount + 1)) : ℝ :=
  Real.log (Real.log (fullCutoff M n W (j.1 + 1) : ℝ)) -
    Real.log (Real.log (fullCutoff M n W j.1 : ℝ))

/-- Endpoint continuum first moment on the `log y` scale. -/
def endpointContinuumMoment (n W : ℕ)
    (j : Fin (M.cellCount + 1)) : ℝ :=
  (Real.log (fullCutoff M n W (j.1 + 1) : ℝ) -
    Real.log (fullCutoff M n W j.1 : ℝ)) / Real.log (y n)

def endpointMassError (C : ℝ) (n W : ℕ)
    (j : Fin (M.cellCount + 1)) : ℝ :=
  5 * C / Real.log (fullCutoff M n W j.1 : ℝ) ^ 3

def endpointMomentError (C : ℝ) (n W : ℕ)
    (j : Fin (M.cellCount + 1)) : ℝ :=
  (2 * C / Real.log (fullCutoff M n W j.1 : ℝ) ^ 3 +
    C / (2 * Real.log (fullCutoff M n W j.1 : ℝ) ^ 2)) /
      Real.log (y n)

def endpointRelativeCenterBound (Cmass Cmoment : ℝ) (n W : ℕ)
    (j : Fin (M.cellCount + 1)) : ℝ :=
  2 * endpointMomentError M Cmoment n W j /
      endpointContinuumMoment M n W j +
    2 * endpointMassError M Cmass n W j /
      endpointContinuumMass M n W j

























end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PaperCanonicalPrimeAnchorEventually -/
section


/-!
# Literal prime anchors for a fixed regular-mesh block

The continuum anchor used by the transferred inverse is not, by itself, the
prime anchor required by the finite Dirichlet argument.  This file constructs
the latter as the union of the literal prime fibers belonging to the selected
positive cells.  It proves both facts needed later:

* every selected prime stays in the prescribed compact subinterval of
  logarithmic coordinates; and
* its `t_p / p` mass is bounded below uniformly in the mesh, provided the
  selected ideal cells have a fixed total-width floor.

The mass comparison is an unconditional two-endpoint PNT estimate.  In
particular, no arithmetic centre is identified with a continuum centre.
-/

open Filter Set
open scoped BigOperators

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer MovingLowMomentQuadrature
open KernelPrimeQuadrature DoubleKernelPrimeQuadrature
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- The literal primes whose canonical band belongs to the selected positive
anchor block. -/
def canonicalPrimeAnchorSet {n W : ℕ}
    (P : Partition n W (Fin (M.cellCount + 1)))
    (anchors : Finset (Fin M.cellCount)) :
    Finset (BandPrime n W) :=
  Finset.univ.filter (fun p ↦
    P.band p ∈ anchors.map (positiveBandEmbedding M))













/-- The structural anchor cutoff.  It is defined before, and is independent
of, every later mesh and selected anchor block. -/
noncomputable def canonicalPrimeAnchorCutoff : ℕ :=
  max 2 MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff





end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PaperCanonicalPrimeRowResidualEventually -/
section


/-!
# Relative prime-row residual for the squarefree Dickman reference

The prime-level anchored Dirichlet proof needs a *relative* row estimate.
An additive estimate for the Dickman kernel is not enough when the marked
prime coordinate tends to zero.  We therefore apply weighted Abel summation
to

`phi_s(t) = t * K(s,t)`.

Both `phi_s` and its derivative in `t` are `O(s)` uniformly on the unit
square.  Consequently the PNT remainder is `O(s / log(W)^3)`.  Kernel
symmetry and the removable quotient row-sum identity then turn this into the
literal bound

`|R_p| <= (D / log(W)^3 + two endpoint tails) * t_p`.

All constants below are chosen before `W`, the ambient integer, and the
marked prime.
-/

open scoped BigOperators
open Set Filter Topology

noncomputable section

namespace Erdos390.Full.PaperCanonicalPrimeRowResidualEventually

open ArithmeticModel PrimeSums PrimeBandQuadrature
open KernelPrimeQuadrature ConditionedPoissonLimit DickmanBasic
open PrimeSquarefreeDirichletGeometry FiniteAnchoredDirichletQuadratic
open MeasureTheory
open DoubleKernelPrimeQuadrature

/-- The test function whose prime sum occurs after conjugating the reference
row by `t_p / p`. -/
def firstMomentKernel (s t : ℝ) : ℝ :=
  t * covarianceKernel s t

/-- Continuous extension of the derivative of `firstMomentKernel s` in its
second coordinate. -/
def firstMomentKernelDerivative (s t : ℝ) : ℝ :=
  covarianceKernel s t +
    t * covarianceKernelDerivativeSecondExtension s t







/-- Explicit Abel coefficient for `firstMomentKernel`. -/
def firstMomentAbelCoefficient (s z x : ℝ) : ℝ :=
  weightedAbelCoefficient (firstMomentKernel s) z x

/-- Explicit derivative of the preceding Abel coefficient. -/
def firstMomentAbelDerivative (s z x : ℝ) : ℝ :=
  weightedAbelCoefficientDerivative (firstMomentKernel s)
    (firstMomentKernelDerivative s) z x





































/-- Explicit relative row-error budget: the PNT term plus the two literal
endpoint tails. -/
def primeRowRelativeError (D C : ℝ) (n W : ℕ) : ℝ :=
  D / Real.log (W : ℝ) ^ 3 +
    C * (realLogCoordinate (y n) (W : ℝ) +
      (1 - realLogCoordinate (y n) (yNat n : ℝ)))









end Erdos390.Full.PaperCanonicalPrimeRowResidualEventually

end

/- Source module: Erdos390.Full.PaperLemma84StructuralCutoff -/
section


/-!
# Structural cutoff for the arithmetic quotient gap

The constants and cutoff in this file precede the mesh, the finite head
type, the exact head patterns, and every later tilt box.  Only vanishing
remainders will be selected after those data in the eventual theorem.
-/

open Filter Topology

namespace Erdos390.Full.PaperLemma84StructuralCutoff

noncomputable section

open ArithmeticModel
open PaperCanonicalSlowKappa
open PaperSquarefreeSlowQuadraticLower
open PaperBridgeFit.BridgeData
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic

/-- The anchor mass is at least `1/8`, so the fixed-kappa Dirichlet main
coefficient is at least `canonicalSlowKappa / 16`. -/
def quotientMain : ℝ := canonicalSlowKappa / 16

/-- A small structural part of the row budget, fixed before the cutoff. -/
def quotientRowTarget : ℝ := quotientMain / 16

/-- The final uniform quotient constant after all perturbations are
absorbed. -/
def quotientKappa : ℝ := quotientMain / 2









end
end Erdos390.Full.PaperLemma84StructuralCutoff

end

/- Source module: Erdos390.Full.PaperGuardPowerCorrectionMixture -/
section


/-!
# Guard deletion for the global prime-power correction row

The useful object in Lemma 7.5 is not the full valuation covariance by
itself, but its difference from the squarefree covariance.  This file applies
the family-summed tagged-mixture perturbation theorem separately to the `VV`
and `II` rows and then subtracts them.  The estimate is global: arbitrary
common component weights and every between-cell covariance term are included.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperGuardCensus

open ArithmeticModel ArithmeticBandGeometry FiniteProbability PaperBridgeFit

noncomputable section

/-- The prime-power correction covariance of a finite integer-valued law. -/
def powerCorrectionCovariance
    {Omega : Type*} [Fintype Omega]
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (p q : ℕ) : ℝ :=
  mu.covariance (fun x ↦ valuation p (value x))
      (fun x ↦ valuation q (value x)) -
    mu.covariance (fun x ↦ divInd p (value x))
      (fun x ↦ divInd q (value x))

/-- Explicit global error produced by deleting the concrete guards from both
the full-valuation and squarefree rows. -/
def guardPowerCorrectionRowError (K d : ℝ) : ℝ :=
  (3 * K * K * d +
      2 * ((K + K * d) * (K * d) + K * (K * d))) +
    (3 * K * d +
      2 * (((1 : ℝ) + d) * (K * d) + K * d))



variable {Head : Type*} [Fintype Head]



end

end Erdos390.Full.PaperGuardCensus

end

/- Source module: Erdos390.Full.PaperBridgeMediumValuationMixture -/
section


/-!
# The bounded medium-only bridge mixture

The reference law used after guard deletion has the same literal integer
values as the bridge sample and differs from the actual component law only by
the residual physical tilt.  This file records that law with the paper's
common endpoint and proves the exact `VV-II = JI+IJ+JJ` identities used by
the physical-transfer ledger.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The medium-only component law, widened to the common bridge endpoint. -/
def mediumComponentValuationLaw [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head) :
    BoundedValuationLaw (B.sampleData.SampleAt c) B.sampleEndpoint where
  probability := B.cellMediumLaw xi c
  value := fun m ↦ (m : ℕ)
  value_pos := by
    intro m
    let sample : B.sampleData.Sample := ⟨c, m⟩
    simpa only [sample, StructuredSampleData.value] using
      B.sampleData.value_pos sample
  value_le := by
    intro m
    let sample : B.sampleData.Sample := ⟨c, m⟩
    simpa only [sample, StructuredSampleData.value] using
      B.sample_value_le_endpoint sample

@[simp] theorem mediumComponentValuationLaw_probability [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head) :
    (B.mediumComponentValuationLaw xi c).probability =
      B.cellMediumLaw xi c := rfl

@[simp] theorem mediumComponentValuationLaw_value [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    (m : B.sampleData.SampleAt c) :
    (B.mediumComponentValuationLaw xi c).value m = (m : ℕ) := rfl







/-- The global value map of the tagged medium mixture is the underlying
integer in each component. -/
@[simp] theorem sigmaMixture_mediumComponent_value [Nonempty Head]
    (xi : B.ParamSpace) (weight : FiniteProbability (Cell Head))
    (x : Sigma fun c : Cell Head ↦ B.sampleData.SampleAt c) :
    (BoundedValuationLaw.sigmaMixture weight
        (B.mediumComponentValuationLaw xi)).value x = (x.2 : ℕ) := rfl

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperBridgePhysicalPowerCorrectionRow -/
section


/-!
# The prime-power correction row through the residual physical tilt

This file keeps the actual partition-function-reweighted component weights
fixed and compares the residual physical tilt component by component.  The
high prime-power columns are summed geometrically before the tagged-mixture
covariance algebra is applied.  Consequently the final comparison is for the
literal `VV-II` row, including all between-component covariance terms.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PrimePowerCutoffCovariance ValuationCutoff LocalFugacityBounds
open PrimeSums
open PrimePowerLcmGeometry

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The medium-only comparison law uses exactly the component weights of the
actual full bridge law.  Thus this comparison never changes the tagged-cell
mixture weights. -/
def physicalMediumReferenceLaw [Nonempty Head]
    (xi : B.ParamSpace) :
    BoundedValuationLaw B.sampleData.Sample B.sampleEndpoint :=
  sigmaMixture
    (tiltedSigmaWeight B.baselineCellProbability
      B.guardedCellProbability (B.scaledBridgeScore xi))
    (B.mediumComponentValuationLaw xi)

/-- Explicit weighted-row loss for deleting the residual physical tilt.
The only moving arithmetic quantity is the harmonic prime-band mass. -/
def physicalPowerCorrectionRowError
    (epsilon G : ℝ) (n W : ℕ) : ℝ :=
  200 * (8 * epsilon) * (1 + quadraticHalfMass) * (1 + G) ^ 2 *
    (bandReciprocalSum n W + 1) * (1 / (W : ℝ))

/-- The exact budget supplied to the tagged-mixture perturbation identity for
one marked prime.  It is kept as a definition so every source term remains
auditable. -/
def physicalPowerCorrectionMixtureBudget
    (epsilon G : ℝ) (n W p : ℕ) : ℝ :=
  let e := 8 * epsilon
  let H := bandReciprocalSum n W
  let S₂ := bandReciprocalSquareSum n W
  let w₁ := 1 / (W : ℝ)
  let p₁ := 1 / (p : ℝ)
  let AIp := G * p₁
  let AJp := 2 * G * p₁ ^ 2
  let AIrow := G * H
  let AJrow := 2 * G * w₁
  let dIp := e * G * p₁
  let dJp := 2 * e * G * p₁ ^ 2
  let dIrow := e * G * H
  let dJrow := 2 * e * G * w₁
  let dJI := e * (2 * G + 6 * G ^ 2) * p₁ ^ 2 * H +
    e * (2 * G * p₁ ^ 2 + 6 * G ^ 2 * p₁ ^ 3)
  let dIJ := e * (2 * G + 6 * G ^ 2) * p₁ * S₂ +
    e * (2 * G * p₁ ^ 2 + 6 * G ^ 2 * p₁ ^ 3)
  let dJJ := e * (4 * G + 12 * G ^ 2) * p₁ ^ 2 * S₂ +
    e * (G * quadraticHalfMass * p₁ ^ 2 + 12 * G ^ 2 * p₁ ^ 4)
  (dJI + 2 * ((AJp + dJp) * dIrow + AIrow * dJp)) +
    (dIJ + 2 * ((AIp + dIp) * dJrow + AJrow * dIp)) +
    (dJJ + 2 * ((AJp + dJp) * dJrow + AJrow * dJp))

















































end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperBridgeCanonicalGuardPowerCorrection -/
section


/-!
# The canonical guard contribution to the prime-power correction row

The prime-power reference law in Lemma 8.4 lives on the unguarded raw
structured cells, whereas the medium-only bridge law lives on the literal
guard-deleted cells.  This file compares the two tagged mixtures without
changing their (post-tilt) component weights.  The comparison includes all
between-component covariance terms.

No arbitrary `BridgeData` is declared canonical.  The finite comparison is
stated under the exact equality between its `sampleData` field and the
canonical constructor from `PaperGuardedStructuredSample`; all dependent
sample-space identifications are then obtained from
`canonicalSampleData_cellFinset`.
-/

open scoped BigOperators
open Filter Topology

set_option maxRecDepth 5000

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open StructuredCellValuationLaw StructuredCells
open PaperGuardCensus GuardedUniformCell
open ValuationScoreDomination

namespace BridgeData



variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The unguarded, medium-prime tilted component, widened to one fixed
physical endpoint. -/
def canonicalRawMediumComponentLaw
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ) (xi : B.ParamSpace)
    (hC_le : ∀ sigma, I.upper sigma ≤ Cmax)
    (hS : ∀ c : Cell Head, (rawCell P I B.sampleData.n c).Nonempty)
    (c : Cell Head) :
    BoundedValuationLaw (rawCell P I B.sampleData.n c)
      (physicalBound Cmax B.sampleData.n) :=
  widen
    (valuationTilt (P c.1)
      (physicalBound (I.lower c.2) B.sampleData.n)
      (physicalBound (I.upper c.2) B.sampleData.n)
      (yNat B.sampleData.n) (hS c)
      (primeBand B.sampleData.n B.sampleData.W)
      (B.effectiveNatCoefficient xi) B.L)
    (FixedFiniteMixtureFullUniform.physicalBound_mono
      (hC_le c.2) B.sampleData.n)

/-- The raw unguarded tagged reference law, with exactly the component
weights carried by the actual post-tilt bridge law. -/
def canonicalRawMediumReferenceLaw [Nonempty Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ) (xi : B.ParamSpace)
    (hC_le : ∀ sigma, I.upper sigma ≤ Cmax)
    (hS : ∀ c : Cell Head, (rawCell P I B.sampleData.n c).Nonempty) :
    BoundedValuationLaw
      (Sigma fun c : Cell Head ↦ rawCell P I B.sampleData.n c)
      (physicalBound Cmax B.sampleData.n) :=
  sigmaMixture
    (tiltedSigmaWeight B.baselineCellProbability
      B.guardedCellProbability (B.scaledBridgeScore xi))
    (B.canonicalRawMediumComponentLaw P I Cmax xi hC_le hS)

/-- The medium-only guard-deleted mixture with the actual post-tilt cell
weights.  This definition is deliberately local to the guard comparison;
the residual-physical comparison uses the definitionally identical law. -/
def canonicalGuardedMediumReferenceLaw [Nonempty Head]
    (xi : B.ParamSpace) :
    BoundedValuationLaw B.sampleData.Sample B.sampleEndpoint :=
  sigmaMixture
    (tiltedSigmaWeight B.baselineCellProbability
      B.guardedCellProbability (B.scaledBridgeScore xi))
    (B.mediumComponentValuationLaw xi)

@[simp] theorem canonicalRawMediumReferenceLaw_probability [Nonempty Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ) (xi : B.ParamSpace)
    (hC_le : ∀ sigma, I.upper sigma ≤ Cmax)
    (hS : ∀ c : Cell Head, (rawCell P I B.sampleData.n c).Nonempty) :
    (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).probability =
      sigmaMixture
        (tiltedSigmaWeight B.baselineCellProbability
          B.guardedCellProbability (B.scaledBridgeScore xi))
        (fun c ↦
          (uniformOnFinset (rawCell P I B.sampleData.n c) (hS c)).exponentialTilt
            (fun m ↦ valuationScore
              (primeBand B.sampleData.n B.sampleData.W)
              (B.effectiveNatCoefficient xi) B.L (m : ℕ))) := rfl

@[simp] theorem canonicalRawMediumReferenceLaw_value [Nonempty Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ) (xi : B.ParamSpace)
    (hC_le : ∀ sigma, I.upper sigma ≤ Cmax)
    (hS : ∀ c : Cell Head, (rawCell P I B.sampleData.n c).Nonempty)
    (m : Sigma fun c : Cell Head ↦ rawCell P I B.sampleData.n c) :
    (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).value m =
      (m.2 : ℕ) := rfl



/-- The guard perturbation needed by the canonical raw cells is a fixed
multiple of the ledger census ratio. -/
def canonicalGuardPerturbationConstant
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Kscore : ℝ) : ℝ :=
  ∑ c : Cell Head,
    8 * Real.exp (2 * Kscore) /
      PaperScaleMarkedCell.paperCellDensity
        (P c.1) (I.lower c.2) (I.upper c.2)



/-- The literal weighted guard-row majorant.  `Cenv * L` is the total
valuation envelope and `D * censusRatioMajorant` is the conditional guard
normalization loss. -/
def guardPowerCorrectionWeightedMajorant
    (Cprom Cbank : ℕ) (Cenv D : ℝ) (n : ℕ) : ℝ :=
  (yNat n : ℝ) *
    PaperGuardCensus.guardPowerCorrectionRowError
      (Cenv * Scale.L n)
      (D * PaperGuardCensus.censusRatioMajorant Cprom Cbank n)



















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperBridgeCanonicalPhysicalPowerCorrectionEventually -/
section


/-!
# Eventual canonical specialization of the residual physical power row

This file discharges the density, score-envelope, small-tilt, and divisor
fallback inputs of the residual-physical comparison.  All constants are
chosen from the fixed physical cells, cutoff, and preselected coefficient
box.  The resulting row error is also proved to survive division by the
moving-low centre, via its explicit `error * log L -> 0` rate.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PrimeSums

namespace BridgeData

variable {Head : Type*} [Fintype Head] [DecidableEq Head]

/-- The fixed cellwise density used in the guarded raw-cell census. -/
def canonicalPhysicalCellDensity
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (c : Cell Head) : ℝ :=
  PaperScaleMarkedCell.paperCellDensity (P c.1)
      (I.lower c.2) (I.upper c.2) /
    (4 * I.upper c.2)

/-- One fixed fallback constant dominating every physical component in the
preselected effective-prime box.  A finite sum is used in place of a maximum
so no choice of a maximizing cell is required. -/
def canonicalPhysicalPowerCorrectionConstant
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ) (W : ℕ) (Acoef : ℝ) : ℝ :=
  let K := Acoef * PaperStatisticNorm.valuationLogCoefficient Cmax W
  ∑ c : Cell Head,
    Real.exp (2 * K) / canonicalPhysicalCellDensity P I c

/-- The residual physical tilt size at ambient integer `n`. -/
def canonicalPhysicalPowerCorrectionEpsilon
    (Aphys Cmax : ℝ) (n : ℕ) : ℝ :=
  Aphys * Real.log Cmax / Scale.L n









end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.FiniteLogStieltjes -/
section


/-!
# Finite logarithmic Stieltjes transfer

The physical column in the marked smooth-number argument is obtained from
uniform prefix-count estimates by Abel summation.  This file isolates the
exact deterministic step.  In particular, the error is charged only once
against the total variation of `log`; it is not multiplied by the number of
integer endpoints or by an auxiliary partition size.
-/

open scoped BigOperators Interval

namespace Erdos390.Full.FiniteLogStieltjes

open Finset MeasureTheory Set

noncomputable section

variable {Omega : Type*} [Fintype Omega]

/-- Centered mass carried by one integer value of a finite random
variable. -/
def centeredFiberMass (mu : FiniteProbability Omega)
    (value : Omega → ℕ) (A : Omega → ℝ) (k : ℕ) : ℝ :=
  ∑ omega, if value omega = k then
    mu.mass omega * (A omega - mu.expect A) else 0











end

end Erdos390.Full.FiniteLogStieltjes

end

/- Source module: Erdos390.Full.PaperMediumNuisanceInputReduction -/
section


/-!
# Exact reductions for the two medium-law nuisance inputs

The nuisance Schur row in paper Lemma 8.6 uses two arithmetic facts about
the literal medium-prime component laws:

* a Stieltjes bound for `Cov(v_p, log (m / n))` inside one cell; and
* agreement, to reciprocal-logarithmic precision, of `E v_p` in two cells.

This file proves all finite probability, Abel summation, prime-power
summation, and physical-log identifications surrounding those two facts.
It intentionally does **not** replace the remaining arithmetic estimates by
a bundled certificate.  The hypotheses in the two terminal reductions are
the literal moving-prefix estimate and the literal prime-power/tail
estimates which still have to be obtained from the marked-cell theorem.
-/

open scoped BigOperators Interval

namespace Erdos390.Full

noncomputable section

open ArithmeticModel FiniteProbability ValuationScoreDomination
open DivisibilityMomentBounds

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

























































end FiniteProbability

namespace PrimePowerTaylorLedger

open LocalFugacityBounds PrimePowerLcmGeometry

/-- A fixed constant controlling the complete same-prime reciprocal-lcm
ledger, including the exponent-one row and column. -/
def positivePrimePowerLcmConstant : ℝ :=
  1 + (4 + quadraticHalfMass) / 2













end PrimePowerTaylorLedger

namespace FiniteProbability

open PrimePowerTaylorLedger

variable {Omega : Type*} [Fintype Omega]



















end FiniteProbability

namespace FiniteLogStieltjes

open Finset Set

variable {Omega : Type*} [Fintype Omega]





end FiniteLogStieltjes

namespace GuardedUniformCell

open FiniteLogStieltjes

variable {Alpha : Type*} [DecidableEq Alpha]





end GuardedUniformCell

namespace PrimePowerTail

open Finset

variable {Omega : Type*} [Fintype Omega]



end PrimePowerTail

namespace PaperBridgeFit

open ArithmeticBandGeometry FiniteLogStieltjes

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)













end BridgeData

end PaperBridgeFit

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperMovingPrefixMarkedCell -/
section


/-!
# Uniform moving-prefix endpoint bookkeeping

For a prefix endpoint `k` inside a fixed physical interval, put
`D = k / n`.  Then `physicalBound D n = k` exactly.  Moreover `D` stays
in the original fixed compact physical interval.  These elementary facts
allow the marked-cell endpoint theorem to be applied without pretending
that the moving endpoint is fixed as `n` varies.
-/

namespace Erdos390.Full.PaperMovingPrefixMarkedCell

open ArithmeticModel PaperScaleMarkedCell
open HeadPattern StructuredCells MarkedFriableAsymptotic
open StructuredCellAsymptotic
open scoped BigOperators

noncomputable section

/-- The physical scale represented by an integer moving endpoint. -/
def prefixScale (n k : ℕ) : ℝ := (k : ℝ) / (n : ℝ)



/-- Re-encoding an integer prefix as a physical scale loses no endpoint:
the floor operation returns the original integer exactly. -/
@[simp] theorem physicalBound_prefixScale_eq {n k : ℕ} (hn : 0 < n) :
    physicalBound (prefixScale n k) n = k := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold physicalBound prefixScale
  rw [div_mul_cancel₀ _ hnR]
  simp







/-- A coarse but fixed endpoint coefficient valid uniformly for every
moving physical scale in `[A,C]`. -/
def compactEndpointCoefficient (A C : ℝ) (g : ℕ) : ℝ :=
  2 + 5 * (Real.log 2 + |Real.log A| + |Real.log C| +
      |Real.log (g : ℝ)|) +
    (45 / 2 : ℝ) * Real.log 2





/-- Uniform version of the complete finite head endpoint ledger. -/
def compactEndpointFamilyCoefficient
    (P : HeadPattern.Pattern) (A C : ℝ) : ℝ :=
  ∑ a ∈ P.modulus.divisors,
    |(ArithmeticFunction.moebius a : ℝ)| *
      (compactEndpointCoefficient A C (P.factor * a) *
        C / ((P.factor * a : ℕ) : ℝ))







/-! ## Exact prefix normalization identities -/









/-- Relative physical length of a moving prefix. -/
def prefixFraction (A C : ℝ) (n k : ℕ) : ℝ :=
  (prefixScale n k - A) / (C - A)











end

end Erdos390.Full.PaperMovingPrefixMarkedCell

end

/- Source module: Erdos390.Full.PaperRawPrefixValuationRow -/
section


/-!
# The raw full-valuation moving-prefix row

This file sums the divisor-prefix estimates over the exact local prime-power
cutoff.  Prime powers in the four-mark chamber use the sharp moving-prefix
estimate.  The remaining powers use the reciprocal fallback and the literal
weighted diagonal tail ledger.  The result is an explicit `p⁻¹` row whose
coefficient tends to zero at the rate required in paper Lemma 8.6.
-/

open Filter
open scoped BigOperators

namespace Erdos390.Full

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance PrimePowerCutoffCovariance
open PaperPrimePowerTailLedger LocalFugacityBounds ValuationCutoff
open PaperPrimePowerTailRow

noncomputable section

namespace PaperRawPrefixValuationRow

/-- A row coefficient dominating both the chamber contribution and the
literal beyond-four tail. -/
def rawValuationPrefixRateMajorant (K G : ℝ) (W n : ℕ) : ℝ :=
  2 * K / L n + tailRowMajorant G W n







end PaperRawPrefixValuationRow

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperRawTiltTaylorRate -/
section


/-!
# A closed rate bound for the raw moving-prefix Taylor polynomial

The finite Taylor theorem records its normalization and remainder terms in
`rawTiltPrefixTaylorBound`.  For the asymptotic application we only need a
simple domination by the marked first moment `RFone` and by `MF * a`.
This file proves that domination with a fixed numerical constant, so the
subsequent rate argument does not have to re-expand the polynomial.
-/

open Filter Topology

namespace Erdos390.Full

open ArithmeticModel Scale PrimeSums

noncomputable section

namespace FiniteProbability







/-- A prime-uniform scalar majorant for the nonlinear part of the Taylor
row after inserting the elementary band bound
`sum_{W<p≤y} 1/p ≤ 12 log L`. -/
def rawTiltNonlinearRateMajorant (B c : ℝ) (n : ℕ) : ℝ :=
  let H := 12 * Real.log (L n)
  128 *
    ((B / L n) * (1 / c) *
        (4 * H + PrimePowerTaylorLedger.positivePrimePowerLcmConstant) +
      (2 / c) * ((B / L n) * ((2 / c) * H)))





end FiniteProbability

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperRawTiltedPrefixRow -/
section


/-!
# The raw tilted full-valuation moving-prefix row

This file closes the finite Taylor argument for the nuisance marked rows.
All inputs to the Taylor lemma are discharged from the structured-cell
census, the un-tilted prefix theorem, and the third-cumulant theorem.  The
only scale separation retained in the terminal statement is the transparent
fixed-box condition `2 B ≤ log W`, which makes the valuation score pointwise
at most one.  The resulting row coefficient remains `o(1 / log L)`.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimeSums ValuationScoreDomination ValuationTiltCell
open PaperScaleMarkedCell FullTiltPairChamber
open PaperRawPrefixValuationRow PaperRawPrefixThirdCumulantRow

noncomputable section

namespace PaperRawTiltedPrefixRow

/-- The first absolute score-moment parameter appearing in the finite
Taylor ledger. -/
def rawTiltSmallParameter (B c : ℝ) (W n : ℕ) : ℝ :=
  (B / L n) * ((2 / c) * bandReciprocalSum n W)









end PaperRawTiltedPrefixRow

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperCanonicalTiltedPrefixRows -/
section


/-!
# Canonical guard-deleted tilted moving-prefix rows

The raw Taylor row is transported through the literal guard deletion and
the exact canonical sample-space reindexing.  After row normalization, the
guard error contains the factor `p * valuationEnvelope`.  Uniformly in the
moving band this is eventually at most `yNat^2`, so it is absorbed by the
already audited squarefree guard error.  The final coefficient therefore
still satisfies the sharp `epsilon(n) * log L(n) -> 0` rate.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.PaperCanonicalTiltedPrefixRows

open ArithmeticModel Scale HeadPattern StructuredCells
open ArithmeticBandGeometry PaperBridgeFit
open FiniteProbability ValuationScoreDomination ValuationTiltCell
open PaperGuardCensus GuardDeletionSquarefreeProfiles
open GuardSquarefreeErrorRate PaperPrimePowerTailRate
open PaperFixedFiniteRawTiltedPrefixRows

noncomputable section

set_option maxHeartbeats 1600000







/-- A fixed finite physical-interval constant dominating every relative
cell span. -/
def physicalSpanMajorant (I : PhysicalIntervals) : ℝ :=
  ∑ sigma : PhysicalSign, 2 * I.upper sigma / I.lower sigma





namespace PaperBridgeFit.BridgeData

open PaperBridgeFit

variable {Head : Type*} [Fintype Head] [DecidableEq Head]





end PaperBridgeFit.BridgeData

end

end Erdos390.Full.PaperCanonicalTiltedPrefixRows

end

/- Source module: Erdos390.Full.CanonicalEndpointDiagonalEventually -/
section


/-!
# Canonical endpoint convergence of the diagonal multiplier

The normalized diagonal PNT estimate contains the actual output-cell mass
in its denominator.  This file proves that the denominator has the required
limit on every literal canonical cell: it diverges on the moving low cell
and tends to a positive constant on every positive cell.  Thus no
``mass is large'' hypothesis remains in the final diagonal statement.
-/

open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel RegularRelativeMesh PrimeBandQuadrature
open DiagonalPrimeQuadrature DoubleKernelPrimeQuadrature
open KernelPrimeQuadrature

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

def endpointActualMass (n W : ℕ) (j : Fin (M.cellCount + 1)) : ℝ :=
  actualCellMass (fullCutoff M n W j.1)
    (fullCutoff M n W (j.1 + 1))

def endpointDiagonalError (n W : ℕ)
    (j : Fin (M.cellCount + 1)) : ℝ :=
  |normalizedDiagonalPrimeCell (y n)
      (fullCutoff M n W j.1) (fullCutoff M n W (j.1 + 1)) -
    normalizedDiagonalContinuumCell (y n)
      (fullCutoff M n W j.1) (fullCutoff M n W (j.1 + 1))|













end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.CanonicalEndpointDoubleKernelRowEventually -/
section


/-!
# Canonical sharp-row aggregation of the double-kernel quadrature

This file closes the two-index application-layer item in the audit of paper
Lemma 8.4.  The normalized double-prime estimate is applied to the literal
canonical endpoints and then summed in the sharp arithmetic norm.  The low
output and low input are treated separately; in particular no factor
`1 / alpha_0` is hidden in a finite-dimensional constant.
-/

open scoped BigOperators
open Filter Topology Set

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open KernelPrimeQuadrature DoubleKernelPrimeQuadrature
open ContinuumCellGraph ContinuumCellGraph.IntervalMesh
open CompressedArithmeticOperator PositiveCellTransfer PrimeBandQuadrature

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- Literal absolute normalized double-kernel error at two canonical cells. -/
def endpointDoubleKernelError (n W : ℕ)
    (i j : Fin (M.cellCount + 1)) : ℝ :=
  |normalizedDoublePrimeKernelCell (y n)
      (fullCutoff M n W i.1) (fullCutoff M n W (i.1 + 1))
      (fullCutoff M n W j.1) (fullCutoff M n W (j.1 + 1)) -
    normalizedDoubleContinuumKernelCell (y n)
      (fullCutoff M n W i.1) (fullCutoff M n W (i.1 + 1))
      (fullCutoff M n W j.1) (fullCutoff M n W (j.1 + 1))|



/-- The explicit right side of the uniform normalized cell theorem. -/
def normalizedDoubleKernelCellBound
    (CKernel DKernel CMass : ℝ) (z : ℝ)
    (A₁ Y₁ A₂ Y₂ : ℕ) : ℝ :=
  (((DKernel / Real.log (A₂ : ℝ) ^ 3) * actualCellMass A₁ Y₁ +
      (DKernel / Real.log (A₁ : ℝ) ^ 3) *
        continuumCellMass z A₂ Y₂) /
      actualCellMass A₁ Y₁) +
    ((CKernel *
        (realLogCoordinate z (Y₁ : ℝ) - realLogCoordinate z (A₁ : ℝ)) *
        (realLogCoordinate z (Y₂ : ℝ) - realLogCoordinate z (A₂ : ℝ))) *
      (5 * CMass / Real.log (A₁ : ℝ) ^ 3) /
      (actualCellMass A₁ Y₁ * |continuumCellMass z A₁ Y₁|))

/-- Algebraic form of the cell bound after naming the output mass, the two
continuum masses and the two coordinate lengths. -/
def abstractNormalizedCellBound
    (CKernel DKernel CMass rOut rIn actualOutMass
      continuumOutMass continuumInMass outLength inLength : ℝ) : ℝ :=
  (DKernel * rIn * actualOutMass +
      DKernel * rOut * continuumInMass) / actualOutMass +
    CKernel * outLength * inLength * (5 * CMass * rOut) /
      (actualOutMass * continuumOutMass)





/-- Continuum centre of a literal canonical endpoint cell. -/
def endpointContinuumCenter (n W : ℕ)
    (j : Fin (M.cellCount + 1)) : ℝ :=
  endpointContinuumMoment M n W j / endpointContinuumMass M n W j

/-- Cubic PNT cutoff factor attached to the lower endpoint of a cell. -/
def endpointInvLogCube (n W : ℕ)
    (j : Fin (M.cellCount + 1)) : ℝ :=
  1 / Real.log (fullCutoff M n W j.1 : ℝ) ^ 3

@[simp] theorem endpointInvLogCube_low (n W : ℕ) :
    endpointInvLogCube M n W (lowBand M) =
      1 / Real.log (W : ℝ) ^ 3 := by
  rfl

























end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.CanonicalEndpointCenterEnvelopeEventually -/
section


/-!
# The canonical moving-low centre has the sharp reciprocal envelope

This file records the quantitative fact needed when an `o(1)` prime-profile
error is divided by the centre of the moving low cell.  The loss is exactly
`O(log log n)`: uniformly in every proof of scale separation and in every
canonical band,

`1 / center i <= C * log (log n)`.

The proof does not identify the low centre with a fixed continuum centre.
It uses the already proved *relative* endpoint-centre convergence, the
literal endpoint continuum first moment, and an elementary upper bound for
the literal endpoint continuum harmonic mass.  Thus it remains valid for the
moving low endpoint and has the quantifier order required in Sections 8.4--8.6.
-/

open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer PrimeBandQuadrature MovingLowMomentQuadrature
open MovingLowGaugeTransfer KernelPrimeQuadrature

/- A mesh-independent cutoff for the sharp moving-low centre envelope. -/
noncomputable def canonicalCenterEnvelopeCutoff : ℕ :=
  max 3 canonicalRelativeCenterCutoff

/-- The explicit reciprocal-centre constant used throughout the later sharp
row and Schur estimates. -/
def canonicalCenterEnvelopeConstant (delta : ℝ) : ℝ := 4 / delta



namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)













end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PaperActualFullProjectedInverseEventually -/
section


/-!
# Eventual inverse for the literal actual full projected operator

This file performs the two stable perturbations in the order used in
Section 8.4.  First the canonical arithmetic reference is perturbed to the
actual squarefree operator; then the proved full-versus-squarefree sharp row
is inserted.  The two perturbation radii and every inverse constant are
chosen before the ambient integer.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimeSums PaperWeightedInverseExport
open OmittedTiltPairChamber PaperPrimePowerChamberError

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



/-- Common row radius reserved for each of the two Neumann perturbations. -/
def canonicalProjectedPerturbationRadius (C : ℝ) : ℝ :=
  1 / (8 * C)













/-- The two already-audited residual rows (physical second tilt and guard
deletion) in the exact combination exported by the canonical prime-power
terminal. -/
def canonicalCombinedPowerCorrection
    (P : Head → HeadPattern.Pattern)
    (I : PaperGuardCensus.PhysicalIntervals)
    (Cmax : ℝ) (Cprom Cbank W : ℕ) (Acoef Aphys : ℝ)
    (n : ℕ) : ℝ :=
  physicalPowerCorrectionRowError
      (canonicalPhysicalPowerCorrectionEpsilon Aphys Cmax n)
      (canonicalPhysicalPowerCorrectionConstant P I Cmax W Acoef) n W +
    guardPowerCorrectionWeightedMajorant Cprom Cbank
      (PaperStatisticNorm.valuationLogCoefficient Cmax W)
      (canonicalGuardPerturbationConstant P I
        (Acoef * PaperStatisticNorm.valuationLogCoefficient Cmax W)) n



/-- Uniform full-versus-squarefree row budget after inserting the canonical
reciprocal-centre envelope.  Its first term is the fixed-cutoff loss; the
other two terms vanish with `n`. -/
def canonicalFullSharpRemainder
    (epsilon combined : ℕ → ℝ)
    (Cpow Calpha K : ℝ) (W n : ℕ) : ℝ :=
  3 * Cpow * (K + 1) * (1 / (W : ℝ)) +
    3 * epsilon n *
      (K * (Calpha * Real.log (Scale.L n)) + 1) *
        (1 / (W : ℝ)) +
    combined n * (Calpha * Real.log (Scale.L n))













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

/-- A reference-head-independent ceiling for the nuisance dimension. -/
def nuisanceDimensionCeiling (Head : Type*) [Fintype Head] : ℝ :=
  Real.sqrt (Fintype.card Head + 1 : ℝ)

/-- A reference-head-independent ceiling for the finite nuisance geometry. -/
def nuisanceGeometryCeiling (Head : Type*) [Fintype Head]
    (sep R : ℝ) : ℝ :=
  2 * sep ^ 2 + 1 + 8 * R ^ 2 * (Fintype.card Head : ℝ)

/-- The uniform nuisance-statistic envelope with the varying deleted
reference coordinate replaced by the full head-cardinality ceiling. -/
def nuisanceStatisticCoefficientCeiling (Head : Type*) [Fintype Head]
    (U : ℝ) : ℝ :=
  nuisanceDimensionCeiling Head *
    max (PaperStatisticNorm.physicalLogCoefficient U) (3 / Real.log 2)

/-- Explicit root lower floor for every canonical effective nuisance gap
whose barycentric cell-mass margin is at least `marginFloor`. -/
def canonicalEffectiveNuisanceGammaFloor
    (Head : Type*) [Fintype Head]
    (I : PhysicalIntervals) (U a : ℝ) (W : ℕ)
    (marginFloor : ℝ) : ℝ :=
  Real.exp (-2 *
      ((PaperStatisticNorm.valuationLogCoefficient U W +
        nuisanceStatisticCoefficientCeiling Head U) * a)) *
    (marginFloor ^ 2 *
      (Real.log (I.lower .plus) - Real.log (I.upper .minus)) ^ 2 /
        (2 * nuisanceGeometryCeiling Head
          (Real.log (I.lower .plus) - Real.log (I.upper .minus))
          (Real.log U)))

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)













end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.RegularRelativeMeshInteriorAnchors -/
section


/-!
# A fixed-mass interior anchor block in every fine relative mesh

For the uniform moving-low inverse one cannot anchor on a single cell: its
width may tend to zero as the mesh is refined.  This file selects all cells
between the first crossings of `1/4` and `3/4`.  If every cell is shorter
than `1/16` and the low endpoint is below `1/16`, that block lies strictly
inside `[1/8,7/8]` and has total width at least `1/4` (in fact at least
`7/16`).
-/

open scoped BigOperators

namespace Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)



/-- First mesh endpoint at or above `x`.  The hypothesis `x ≤ 1` makes
the terminal endpoint a witness. -/
theorem exists_endpoint_ge (x : ℝ) (hx : x ≤ 1) :
    ∃ k : ℕ, x ≤ M.endpoint k := by
  exact ⟨M.cellCount, by simpa only [M.endpoint_cellCount] using hx⟩

def firstEndpointAtLeast (x : ℝ) (hx : x ≤ 1) : ℕ :=
  Nat.find (M.exists_endpoint_ge x hx)



theorem firstEndpointAtLeast_le_cellCount (x : ℝ) (hx : x ≤ 1) :
    M.firstEndpointAtLeast x hx ≤ M.cellCount := by
  apply Nat.find_min' (M.exists_endpoint_ge x hx)
  simpa only [M.endpoint_cellCount] using hx







/-- Cells between the quarter and three-quarter endpoint crossings. -/
def interiorAnchors : Finset (Fin M.cellCount) :=
  Finset.univ.filter fun k ↦
    M.firstEndpointAtLeast (1 / 4 : ℝ) (by norm_num) ≤ k.1 ∧
      k.1 < M.firstEndpointAtLeast (3 / 4 : ℝ) (by norm_num)















end Mesh

end

end Erdos390.Full.RegularRelativeMesh

end

/- Source module: Erdos390.Full.PaperBandBestDistance -/
section


/-!
# Exact weighted distance to the logarithmic null direction

The paper states the quotient gap using an infimum over the scalar multiple
of the band-centre vector.  The finite Lean development uses the explicit
weighted orthogonal projection `gaugePart`.  This file proves that the two
forms are literally equal, so a paper-facing terminal can use the displayed
infimum without changing the result.
-/

namespace Erdos390.Lemma84

noncomputable section

open Set

variable {Prime Band : Type*}
variable [Fintype Prime] [Fintype Band]
variable [DecidableEq Prime] [DecidableEq Band]

namespace WeightedBandData

variable (d : WeightedBandData Prime Band)

/-- The literal weighted distance appearing in the paper. -/
def bestBandDistance (b : Band → ℝ) : ℝ :=
  ⨅ mu : ℝ, d.bandNormSq (fun j ↦ b j - mu * d.center j)





end WeightedBandData

end


end Erdos390.Lemma84

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

/-- Squarefree companion of a literal raw-band regression score. -/
def bandSquarefreeRegressionScore
    (q : B.RawBandGauge) (m : B.sampleData.Sample) : ℝ :=
  ∑ r : BandPrime B.sampleData.n B.sampleData.W,
    q.1 (B.partition.band r) * divInd r.1 (B.sampleData.value m)











end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualSchurOrdinaryRow -/
section


/-!
# Ordinary raw-norm nuisance--Schur transfer

The sharp Schur estimate divides by the least band centre.  That loss is
appropriate for a sharp input, but it is spurious for the ordinary raw
supremum norm required by the fast solve.  Here both prime-band summations
are performed before projection.  The result depends on the total harmonic
mass, which is later paired with the genuinely vanishing marked rate; it has
no factor `1 / min alpha`.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry
open OrdinaryRawInverseTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



/-- Ordinary raw Schur rate supplied by a reciprocal marked family.  In
contrast with `nuisanceMarkedSchurRate`, this has no least-centre divisor. -/
def nuisanceMarkedOrdinarySchurRate (Cmarked gamma R : ℝ) : ℝ :=
  let droot := Real.sqrt
    (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  let totalMass := ∑ j : Band, B.harmonicMass j
  (1 + R) *
    (((droot * (Cmarked * totalMass)) / gamma) * (droot * Cmarked))





end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperPrimeDeviationGeometry -/
section


/-!
# Deterministic geometry of the actual prime deviations

These are the finite inequalities used in the `L¹` and variance census of
Lemma 8.6.  They apply to the actual arithmetic centers and actual primes.
No continuum center and no prime-number estimate occurs here; analytic
quadrature can therefore be inserted afterwards without a centering error.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PositiveCellTransfer KernelPrimeQuadrature

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Weighted `L¹` deviation on one actual arithmetic band. -/
def bandDeviationL1 (j : Band) : ℝ :=
  ∑ p ∈ B.partition.data.fiber j,
    (1 / (p.1 : ℝ)) * |B.primeDeviation p|

/-- The paper's full `sum |g_p|/p`. -/
def primeDeviationL1 : ℝ :=
  ∑ p : BandPrime B.sampleData.n B.sampleData.W,
    (1 / (p.1 : ℝ)) * |B.primeDeviation p|

















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

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

/-- Compression of the literal prime Dirichlet graph to band-constant
quotient coordinates.  The normalization is exactly
`H_i alpha_i = sum_{p in i} t_p/p`. -/
def compressedPrimeGraphEdge (i j : Band) : ℝ :=
  (1 / (B.harmonicMass i * B.bandCenter i)) *
    ∑ p ∈ B.partition.data.fiber i,
      ∑ q ∈ B.partition.data.fiber j,
        (1 / (p.1 : ℝ)) * primeWeight B.sampleData.n q *
          (-primeKernel B.sampleData.n p q)



/-- The residual-row contribution with the band coefficient kept inside
the finite sum.  This syntactic form makes the exact decomposition literal;
it is subsequently bounded by the scalar residual estimate. -/
def referenceResidualError (x : Band → ℝ) (i : Band) : ℝ :=
  (1 / (B.harmonicMass i * B.bandCenter i)) *
    ∑ p ∈ B.partition.data.fiber i,
      (1 / (p.1 : ℝ)) *
        rowResidual
          (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n)
          (primeKernel B.sampleData.n) p * x i

/-- The part left after replacing each arithmetic band centre by the
literal prime coordinate in the diagonal term. -/
def referenceCenteringDiagonal (x : Band → ℝ) (i : Band) : ℝ :=
  (1 / (B.harmonicMass i * B.bandCenter i)) *
    ∑ p ∈ B.partition.data.fiber i,
      (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)) *
        B.primeDeviation p * x i

/-- The corresponding centred kernel term. -/
def referenceCenteringKernel (x : Band → ℝ) (i : Band) : ℝ :=
  (1 / (B.harmonicMass i * B.bandCenter i)) *
    ∑ p ∈ B.partition.data.fiber i,
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        B.primeDeviation q * x (B.partition.band q) *
          covarianceKernel
            (tPrime B.sampleData.n p.1)
            (tPrime B.sampleData.n q.1) /
              ((p.1 : ℝ) * (q.1 : ℝ))





/-- Literal prime-anchor mass compressed to the arithmetic bands. -/
def compressedPrimeAnchor
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (j : Band) : ℝ :=
  ∑ q ∈ B.partition.data.fiber j,
    if q ∈ anchor then primeWeight B.sampleData.n q else 0























end BridgeData
end
end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalActualMomentBoundsEventually -/
section


/-!
# Canonical actual-prime moment bounds, uniformly in the separation proof

`RegularMeshActualMomentBoundsEventually` constructs a partition
existentially.  For the paper-facing bridge we need the same estimates on
the literal canonical partition appearing in the bridge hypothesis, and we
need them for every proof of the scale-separation inequalities.  Proof
irrelevance is not used as an analytic input here: the endpoint inequalities
are established first and the canonical partition is then constructed from
any supplied separation proof.
-/

open scoped BigOperators
open Filter

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer KernelPrimeQuadrature PrimeBandQuadrature
open PrimeCoordinateSecondMoment MovingLowMomentQuadrature

/-- Named global witnesses for reciprocal-mass quadrature. -/
noncomputable def canonicalMassQuadratureConstant : ℝ :=
  Classical.choose
    PrimeBandQuadrature.exists_fullReciprocalSum_interval_error_bound

noncomputable def canonicalMassQuadratureCutoff : ℕ :=
  Classical.choose
    (Classical.choose_spec
      PrimeBandQuadrature.exists_fullReciprocalSum_interval_error_bound).2



/-- Named global witnesses for the square-coordinate quadrature. -/
noncomputable def canonicalSecondMomentConstant : ℝ :=
  Classical.choose
    PrimeCoordinateSecondMoment.exists_uniform_squarePrimeCell_error_bound

noncomputable def canonicalSecondMomentCutoff : ℕ :=
  Classical.choose
    (Classical.choose_spec
      PrimeCoordinateSecondMoment.exists_uniform_squarePrimeCell_error_bound).2



/-- One mesh-independent cutoff for all three moment quadratures. -/
noncomputable def canonicalActualMomentCutoff : ℕ :=
  max 8 (max canonicalMassQuadratureCutoff
    (max MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff
      canonicalSecondMomentCutoff))

namespace Mesh

section DiagonalMomentMesh

variable {delta : ℝ} (M : Mesh delta delta)





end DiagonalMomentMesh

section GenericFirstMomentMesh

variable {delta eta : ℝ} (M : Mesh delta eta)











end GenericFirstMomentMesh

section DiagonalMesh

variable {delta : ℝ} (M : Mesh delta delta)





end DiagonalMesh

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

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



/-- Explicit scalar majorant for the nuisance-Schur perturbation. -/
def selectedMeshSchurRateMajorant
    (epsilon : ℕ → ℝ) (droot momentBound gammaFloor centerScale : ℝ)
    (n : ℕ) : ℝ :=
  (((droot * (epsilon n * momentBound)) / gammaFloor) *
      (droot * epsilon n)) /
    (centerScale / Real.log (Scale.L n))











end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.ContinuumManyLowHighGeometry -/
section


/-!
# Low--high geometry for the ordinary continuum inverse

The ordinary inverse cannot be obtained from the sharp inverse by dividing
by the least cell centre: the centre of the moving low cell tends to zero.
This file instead records the exact estimates used after splitting a finite
continuum mesh into an arbitrary low block and a high block.  The product
kernel bound makes every edge entering a low cell proportional to both the
ordinary length and the centre of that cell.  Consequently all constants
below depend on the total low length, not on the number of low cells or on
their least endpoint.

No inverse, coercivity, or convergence statement is assumed here.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.ContinuumCellGraph
namespace IntervalMesh

open ConditionedPoissonLimit
open FiniteGraphQuotientInverse

variable {Band Low High : Type*}
  [Fintype Band] [Fintype Low]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

/-- Relabel the continuum sharp edge along a low--high decomposition. -/
def splitSharpEdge (e : Sum Low High ≃ Band)
    (x y : Sum Low High) : ℝ :=
  M.sharpKernelEdge (e x) (e y)





section Anchor

variable [DecidableEq Band]

/-- Interior anchor measure after restricting the relabelled graph to the
high block. -/
def splitHighAnchor (e : Sum Low High ≃ Band) (j : High) : ℝ :=
  M.anchor (e (.inr j))









end Anchor









end IntervalMesh
end Erdos390.Full.ContinuumCellGraph

end

/- Source module: Erdos390.Full.FiniteManyLowRawGraphInverse -/
section


/-!
# Ordinary raw inverse with a finite low block

This is the finite maximum-principle mechanism needed when a relative mesh
contains arbitrarily many cells below a fixed structural cutoff.  The low
rows are controlled by a separate diagonal-dominance estimate.  On the high
block the common interior anchor controls oscillation.  Low-to-high forcing
and the low contribution to the gauge are retained explicitly and then
absorbed in the literal raw supremum norm.

No inverse, surjectivity statement, or spectral gap occurs among the
hypotheses.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.FiniteManyLowRawGraphInverse

open FiniteGraphQuotientInverse

variable {Low High : Type*} [Fintype Low] [Fintype High]

def highEdge (edge : Sum Low High → Sum Low High → ℝ)
    (i j : High) : ℝ := edge (.inr i) (.inr j)

def highPart (q : Sum Low High → ℝ) (i : High) : ℝ := q (.inr i)





end Erdos390.Full.FiniteManyLowRawGraphInverse

end

/- Source module: Erdos390.Full.RegularRelativeMeshPrefixSplit -/
section


/-!
# Prefix split at a fixed logarithmic threshold

The moving low cell and all positive cells before the first ideal endpoint
crossing `tau` form the low block.  The remaining positive cells form the
high block.  The construction is purely ideal-mesh geometry and therefore
does not depend on the later arithmetic cutoff or ambient integer.
-/

namespace Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

def prefixIndex (tau : ℝ) (htau : tau ≤ 1) : ℕ :=
  M.firstEndpointAtLeast tau htau

abbrev prefixLow (tau : ℝ) (htau : tau ≤ 1) : Type :=
  Fin (M.prefixIndex tau htau + 1)

abbrev prefixHigh (tau : ℝ) (htau : tau ≤ 1) : Type :=
  Fin (M.cellCount - M.prefixIndex tau htau)

/-- The exact low-prefix/high-suffix reindexing of the full band set. -/
def prefixSplitEquiv (tau : ℝ) (htau : tau ≤ 1) :
    Sum (M.prefixLow tau htau) (M.prefixHigh tau htau) ≃
      Fin (M.cellCount + 1) :=
  finSumFinEquiv.trans (finCongr (by
    have hj := M.firstEndpointAtLeast_le_cellCount tau htau
    dsimp only [prefixLow, prefixHigh, prefixIndex]
    omega))

@[simp] theorem prefixSplitEquiv_inl_val
    (tau : ℝ) (htau : tau ≤ 1) (l : M.prefixLow tau htau) :
    (M.prefixSplitEquiv tau htau (.inl l)).1 = l.1 := by
  rfl

@[simp] theorem prefixSplitEquiv_inr_val
    (tau : ℝ) (htau : tau ≤ 1) (k : M.prefixHigh tau htau) :
    (M.prefixSplitEquiv tau htau (.inr k)).1 =
      M.prefixIndex tau htau + 1 + k.1 := by
  rfl

















end Mesh
end
end Erdos390.Full.RegularRelativeMesh

end

/- Source module: Erdos390.Full.CanonicalEndpointPrefixGeometry -/
section


/-!
# Canonical endpoint geometry for the moving prefix split

One literal boundary separates the low prefix from the high suffix.  Its
coordinate converges to the corresponding ideal endpoint.  Consequently,
ordinary centre and length estimates do not divide by the moving low-cell
centre and are uniform in the number of cells.
-/

open scoped BigOperators
open Filter

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel RegularRelativeMesh KernelPrimeQuadrature
  DoubleKernelPrimeQuadrature
  ContinuumCellGraph

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

def canonicalPrefixBoundary (n W : ℕ) (tau : ℝ) (htau : tau ≤ 1) : ℝ :=
  actualCutoffCoordinate M n W (M.prefixIndex tau htau + 1)





section LiteralGeometry

variable {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
  (hW : W ≠ 0) (hWTwo : 2 ≤ W) (S : ScaleSeparation M n W)
  {tau epsilon : ℝ} (htau : tau ≤ 1)
  (anchors : Finset (Fin M.cellCount)) (hAnchors : anchors.Nonempty)
  (hIdealAnchorLower : ∀ k ∈ anchors, tau < M.lower k)
  (hInteriorLower : ∀ k ∈ anchors, epsilon ≤
    realLogCoordinate (y n)
      ((canonicalCertificate M hdelta hn hW S).lower
        (positiveBand M k) : ℝ))
  (hInteriorUpper : ∀ k ∈ anchors,
    realLogCoordinate (y n)
      ((canonicalCertificate M hdelta hn hW S).upper
        (positiveBand M k) : ℝ) ≤ 1 - epsilon)















end LiteralGeometry

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.CanonicalEndpointRawWeightDefectEventually -/
section


/-!
# Ordinary raw-weight convergence for canonical endpoint bands

The arithmetic raw gauge uses the exact finite weights `H_j alpha_j`.
The continuum gauge uses `harmonicMass_j * center_j`, which is exactly the
ordinary coordinate length of the endpoint cell.  This file compares those
two quantities without identifying either arithmetic factor separately with
its continuum analogue.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open KernelPrimeQuadrature MovingLowMomentQuadrature

/-- A mesh-independent cutoff for the first-moment quadrature used in the
raw-gauge comparison. -/
def canonicalRawWeightDefectCutoff : ℕ :=
  max 2 MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff

namespace Mesh





end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.CanonicalEndpointDoubleKernelOrdinaryRowEventually -/
section


/-!
# Canonical endpoint double-kernel quadrature in ordinary raw norm

The sharp row estimate weights an input cell by a ratio of arithmetic
centres.  That is the correct estimate after sharp conjugation, but its
fixed-cutoff constant contains the reciprocal of the moving low centre.
For the ordinary raw norm no centre ratio occurs.  This file repeats only
the final finite summation in that norm and obtains a fixed-cutoff constant
which is independent of the later regular mesh.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel RegularRelativeMesh
open PrimeBandQuadrature KernelPrimeQuadrature DoubleKernelPrimeQuadrature

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- A centre-free majorant for one normalized double-kernel cell. -/
def endpointDoubleKernelOrdinaryCoarseEntry
    (CKernel DKernel CMass : ℝ) (n W : ℕ)
    (i j : Fin (M.cellCount + 1)) : ℝ :=
  DKernel * endpointInvLogCube M n W j +
    2 * DKernel * endpointInvLogCube M n W i *
      (endpointContinuumMass M n W j /
        endpointContinuumMass M n W i) +
    10 * CKernel * CMass * endpointInvLogCube M n W i *
      (endpointContinuumMoment M n W i *
        endpointContinuumMoment M n W j /
          endpointContinuumMass M n W i ^ 2)

def endpointDoubleKernelOrdinaryCoarseRow
    (CKernel DKernel CMass : ℝ) (n W : ℕ)
    (i : Fin (M.cellCount + 1)) : ℝ :=
  ∑ j, endpointDoubleKernelOrdinaryCoarseEntry
    M CKernel DKernel CMass n W i j
























end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.CanonicalEndpointOrdinaryProjectedRawInverseEventually -/
section


/-!
# Mesh-uniform ordinary inverse for the canonical endpoint operator

This is the arithmetic conclusion of the moving-low-cell transfer.  All
structural constants, the mesh tolerance, and the prime cutoff are selected
before the two independent mesh parameters.  For each permitted mesh only
the eventual ambient threshold is allowed to vary.
-/

open scoped BigOperators NNReal
open Filter Topology Set

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open KernelPrimeQuadrature DoubleKernelPrimeQuadrature
open ContinuumCellGraph ContinuumCellGraph.IntervalMesh
open ContinuumCellGraph.ArithmeticGaugeOrdinary
open CompressedArithmeticOperator MovingLowGaugeTransfer
open PaperWeightedInverseExport PoissonDickmanWeightedInverse
open PoissonDickmanKernelBounds PrimeSums
open PaperBridgeFit.PaperActualSlowRightRowFinite

namespace Mesh

 theorem sharpWeightTotal_partition_eq_centerEnergy
    {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
    (P : ArithmeticBandGeometry.Partition n W Band) :
    sharpWeightTotal P.mass P.center = P.centerEnergy := by
  unfold sharpWeightTotal sharpWeight
  unfold ArithmeticBandGeometry.Partition.centerEnergy
    Erdos390.Lemma84.WeightedBandData.centerEnergy
    Erdos390.Lemma84.WeightedBandData.bandNormSq
    Erdos390.Lemma84.WeightedBandData.bandInner
  simp only [pow_two, mul_assoc]





end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PaperCanonicalActualSchurOrdinaryRowsEventually -/
section


/-!
# Fully discharged ordinary perturbation rows for Lemma 8.4

This file packages the three analytic perturbations used by the endpoint
ordinary inverse: squarefree-to-reference, full-to-squarefree, and the
nuisance Schur correction.  The fixed `1/W` tails are made small before the
head data and the effective tilt ball are selected.  Every dependence on the
later ball is confined to an eventual error in the ambient parameter `n`.

The only local premise retained by the last row is the exact first-moment to
centre-energy ratio.  That geometric premise is supplied, without analytic
assumptions, by the separate canonical moment-ratio terminal when the final
Lemma 8.4 wrapper is assembled.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PrimeSums PaperWeightedInverseExport
open RegularMeshPrimeCutoffs
open SquarefreeCovarianceReference
open PaperPrimePowerChamberError
open PrimeSquarefreeDirichletGeometry

namespace BridgeData

/-- A fixed ordinary row budget small enough for the two-stage endpoint
perturbation. -/
def canonicalOrdinaryRowTolerance (Cref Rproj : ℝ) : ℝ :=
  1 / (8 * Cref * (1 + Rproj))

/-- A fixed ordinary Schur-row budget small enough for the second Neumann
step. -/
def canonicalOrdinarySchurTolerance (Cref : ℝ) : ℝ :=
  1 / (8 * Cref)















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalPositiveCellVarianceEventually -/
section


/-!
# Positive-cell variance on an arbitrary regular relative mesh

The moving low cell alone controls the paper scale only when the positive
relative width is no larger than the low endpoint.  This file supplies the
missing complementary estimate: the sum of the literal within-cell prime
variances in the positive cells is bounded below by a fixed multiple of the
square of the actual common mesh ratio.  The proof first identifies the
finite prime moments with three unconditional PNT quadratures and then
passes to the exact continuum cell variance.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer KernelPrimeQuadrature PrimeBandQuadrature
open PrimeCoordinateSecondMoment MovingLowMomentQuadrature

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- Exact continuum variance of one positive logarithmic cell for the
harmonic measure `dt/t`. -/
def idealPositiveBandVariance (k : Fin M.cellCount) : ℝ :=
  (M.upper k ^ 2 - M.lower k ^ 2) / 2 -
    M.width k ^ 2 / M.cellHarmonicMass k









/-- The three literal prime sums attached to a positive canonical cell.
They are defined without choosing a proof of scale separation, so their
limits can be stated as ordinary sequences. -/
def canonicalPositiveMassValue (n W : ℕ) (k : Fin M.cellCount) : ℝ :=
  PrimeSums.fullReciprocalSum (fullCutoff M n W (k.1 + 2)) -
    PrimeSums.fullReciprocalSum (fullCutoff M n W (k.1 + 1))

def canonicalPositiveFirstValue (n W : ℕ) (k : Fin M.cellCount) : ℝ :=
  (PrimeSums.fullLogReciprocalSum (fullCutoff M n W (k.1 + 2)) -
      PrimeSums.fullLogReciprocalSum (fullCutoff M n W (k.1 + 1))) /
    Real.log (y n)

def canonicalPositiveSecondValue (n W : ℕ) (k : Fin M.cellCount) : ℝ :=
  fullWeightedReciprocalSum squareCoordinate (y n)
      (fullCutoff M n W (k.1 + 2)) -
    fullWeightedReciprocalSum squareCoordinate (y n)
      (fullCutoff M n W (k.1 + 1))

def canonicalPositiveVarianceValue (n W : ℕ) (k : Fin M.cellCount) : ℝ :=
  canonicalPositiveSecondValue M n W k -
    canonicalPositiveFirstValue M n W k ^ 2 /
      canonicalPositiveMassValue M n W k

/-- Endpoint second moment before applying the prime quadrature. -/
def positiveContinuumSecond (n W : ℕ) (k : Fin M.cellCount) : ℝ :=
  (cutoffCoordinate M n W (k.1 + 2) ^ 2 -
    cutoffCoordinate M n W (k.1 + 1) ^ 2) / 2



























end Mesh

end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PaperCanonicalGeometricMomentFineMeshEventually -/
section


/-!
# Paper-scale geometric moment inputs on every permitted fine mesh

This file assembles the arithmetic estimates used after the continuum-to-band
transfer.  The structural prime cutoff and the numerical mesh tolerance are
chosen before the mesh.  The two mesh parameters remain independent: the
only comparison used is the two-sided regularity condition from the paper,
namely

`cMesh * eta ≤ M.ratio ≤ eta`.

The lower variance estimate deliberately combines two different arithmetic
sources.  The moving low cell controls `delta^2`, while the positive cells
control the square of the actual relative width `M.ratio`.  Thus no hidden
hypothesis such as `M.ratio ≤ delta` or `eta ≤ delta` is present.
-/

open scoped BigOperators
open Filter

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PaperPermittedRegularMesh

namespace Mesh

/-- A single mesh-independent cutoff for the moments and the prime anchor. -/
noncomputable def canonicalPaperGeometricCutoff : ℕ :=
  max canonicalActualMomentCutoff canonicalPrimeAnchorCutoff

/-- The fixed numerical small-mesh threshold used by the anchor argument. -/
def canonicalPaperGeometricMeshTolerance : ℝ := (1 : ℝ) / 16







end Mesh

end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PaperCanonicalLemma86CoefficientPackageEventually -/
section


/-!
# Canonical eventual coefficient package for Lemma 8.6

This file joins the paper-scale canonical prime geometry to the literal
first-stage Schur regression.  All prime-deviation moments, the moving-low
cell, the positive-cell variance, and the prime anchor are discharged before
the public call site.  The only quantitative call-site inputs are precisely
those supplied by the preceding inverse lemma:

* an equivalence representing the same literal Schur map, together with its
  sharp inverse estimate; and
* the normalized slow right-row estimate.

The theorem is uniform over an arbitrary effective box.  Its quantifiers are
ordered as in the paper: the structural prime cutoff is fixed before the
mesh, the mesh before the effective box, and only then may the ambient
integer threshold be selected.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport PrimeSums
open RegularMeshPrimeCutoffs PaperPermittedRegularMesh

namespace BridgeData

/-- The coefficient package needs no cutoff beyond the final geometric one. -/
noncomputable def canonicalPaperLemma86CoefficientCutoff : ℕ :=
  RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricCutoff





end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperNonstepSlowRightLedger -/
section


/-!
# Exact non-step prime-power ledger for the slow right row

The slow coefficient is the literal arithmetic deviation
`g_p = alpha_{j(p)} - t_p`; it is not replaced by a step function.  This
file keeps the `t_p` factors in the three `JI/IJ/JJ` orientations until
after the output-band average.  The resulting finite estimate has exactly
three kinds of terms:

* a structural `Cpow / W` multiple of `w * alpha_i`;
* an analytic remainder `epsilon / W` times `w` (to be divided by the
  actual arithmetic centre only in the eventual specialization); and
* the literal local reciprocal-square deviation ledger.

No mesh, continuum centre, asymptotic profile, or ODE box occurs in the
theorem below.  It is therefore reusable in both Lemma 8.6 and Proposition
8.7.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PrimeSums
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerLemma75

namespace BridgeData





variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The squarefree analogue of the literal slow score. -/
def slowSquarefreeScore (m : B.sampleData.Sample) : ℝ :=
  ∑ p : BandPrime B.sampleData.n B.sampleData.W,
    B.primeDeviation p * divInd p.1 (B.sampleData.value m)

/-- The squarefree output statistic on one actual arithmetic band. -/
def squarefreeBandScore (i : Band) (m : B.sampleData.Sample) : ℝ :=
  ∑ p ∈ B.partition.data.fiber i,
    divInd p.1 (B.sampleData.value m)

/-- Squarefree-output analogue of `normalizedBandCovarianceRow`. -/
def normalizedSquarefreeBandCovarianceRow
    [Nonempty Head] (xi : B.ParamSpace)
    (F : B.sampleData.Sample → ℝ) (i : Band) : ℝ :=
  (B.tiltedLaw xi).covariance (B.squarefreeBandScore i) F /
    B.harmonicMass i

/-- The local `p^{-2}` deviation term which is deliberately retained in the
non-step prime-power calculation. -/
def bandDeviationReciprocalSquare (i : Band) : ℝ :=
  (1 / B.harmonicMass i) *
    ∑ p ∈ B.partition.data.fiber i,
      |B.primeDeviation p| * (1 / (p.1 : ℝ)) ^ 2

/-- Named exact budget for the non-step prime-power row.  The first summand
is structural, the second is the analytic four-mark remainder, and the
third is the diagonal prime-power term. -/
def nonstepPrimePowerRowBudget
    (Cpow epsilon w W alpha localDiagonal : ℝ) : ℝ :=
  (21 * Cpow * (1 / W)) * (w * alpha) +
    (21 * epsilon * (1 / W)) * w +
  3 * (Cpow + epsilon) * localDiagonal

/-- Literal full-valuation row with the primewise non-step coefficient.
This formulation is law-generic, so the canonical raw reference law and
the final actual law can be compared without changing coefficients. -/
def nonstepFullCoefficientRow
    {Omega : Type*} [Fintype Omega] {Mlaw : ℕ}
    (law : BoundedValuationLaw Omega Mlaw) (i : Band) : ℝ :=
  (1 / B.harmonicMass i) *
    ∑ p ∈ B.partition.data.fiber i,
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        B.primeDeviation q * law.covVV p.1 q.1

/-- Literal squarefree row with the same primewise non-step coefficient. -/
def nonstepSquarefreeCoefficientRow
    {Omega : Type*} [Fintype Omega] {Mlaw : ℕ}
    (law : BoundedValuationLaw Omega Mlaw) (i : Band) : ℝ :=
  (1 / B.harmonicMass i) *
    ∑ p ∈ B.partition.data.fiber i,
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        B.primeDeviation q * law.covII p.1 q.1







end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperNonstepSquarefreeSlowLedger -/
section


/-!
# Exact non-step squarefree slow-row ledger

This file keeps the primewise coefficient
`g_p = alpha_{j(p)} - t_p` throughout the signed squarefree comparison.
Consequently the off-diagonal profile error is charged to the global
weighted `L¹` deviation, and the `p^{-2}` diagonal is exactly the local
quantity handled by `PaperCanonicalNonstepLocalDiagonalEventually`.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open SquarefreeCovarianceReference SquarefreeSharpBandTransfer
open PrimeSquarefreeDirichletGeometry FiniteAnchoredDirichletQuadratic
open PaperActualSlowRightRowFinite
open SquarefreeReferenceOperatorIdentification

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Signed Dickman reference row with the literal non-step slow
coefficient. -/
def referenceSlowRow (i : Band) : ℝ :=
  (1 / B.harmonicMass i) *
    ∑ p ∈ B.partition.data.fiber i,
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        B.primeDeviation q *
          squarefreeReferenceEntry B.sampleData.n p.1 q.1











end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperNonstepPrimeMomentRate -/
section


/-!
# Vanishing reciprocal-square logarithmic moment

The moving-low non-step ledger needs the literal quantity
`sum t_p / p^2`, not a step-function surrogate.  This file proves directly
that it tends to zero for every fixed cutoff.  The proof uses only the
already-audited harmonic prime bound and `log p ≤ p`; no PNT asymptotic is
introduced.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PrimeSums

open ArithmeticModel Scale

noncomputable section

/-- The global `G₂` output moment in the non-step slow-row ledger. -/
def bandTReciprocalSquareSum (n W : ℕ) : ℝ :=
  ∑ p ∈ primeBand n W, tPrime n p * (1 / (p : ℝ)) ^ 2







end

end Erdos390.Full.PrimeSums

end

/- Source module: Erdos390.Full.PaperNonstepLocalDiagonal -/
section


/-!
# Exact local diagonal estimates for the non-step slow row

The prime-power slow-row ledger leaves the literal cell quantity

`H_i^{-1} sum_{p in cell i} |alpha_i-t_p|/p^2`.

This file bounds that quantity without replacing `t_p` by a step value.
The low-cell estimate retains the two global reciprocal-square moments;
the positive-cell estimate exploits the moving lower endpoint.  Both are
finite identities/inequalities, independent of any tilt box.
-/

open scoped BigOperators

namespace Erdos390.Full.ArithmeticBandGeometry.Partition

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PrimeSums
open PositiveCellTransfer

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
  (P : Partition n W Band)

/-- Literal normalized reciprocal-square deviation in a partition cell. -/
def normalizedDeviationReciprocalSquare (i : Band) : ℝ :=
  (1 / P.mass i) *
    ∑ p ∈ P.data.fiber i,
      |P.deviation p| * (1 / (p.1 : ℝ)) ^ 2











end

end Erdos390.Full.ArithmeticBandGeometry.Partition

end

/- Source module: Erdos390.Full.PaperCanonicalNonstepLocalDiagonalEventually -/
section


/-!
# Canonical relative decay of the literal non-step local diagonal

For the moving low cell one must not replace the local `p^{-2}` term by an
additive `O(1/W)`: its centre tends to zero.  We instead retain the exact
decomposition into `alpha_0 * sum p^{-2}` and `sum t_p p^{-2}`.  The first
term is divided by the diverging low-cell mass, while the second vanishes
and is divided only by `H_0 alpha_0 -> delta`.

For every positive cell the lower endpoint tends to infinity, giving the
direct estimate `D_i <= w/A_i`.  The result is uniform over the finite band
set and uses the actual scale `w = delta + M.ratio`; `eta` is independent.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer PrimeSums MovingLowMomentQuadrature
open KernelPrimeQuadrature

/-- The cutoff contains only the two global prime-sum thresholds used in
the low-cell mass and first-moment arguments.  It is independent of every
later mesh, tolerance, tilt box, and head pattern. -/
def canonicalNonstepLocalDiagonalCutoff : ℕ :=
  max 2 (max canonicalMassQuadratureCutoff
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff)

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)







end Mesh

end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PaperCanonicalNonstepPowerInputsEventually -/
section


/-!
# Canonical inputs for the non-step full slow row

This file exports the two objects that the literal non-step ledger needs,
rather than only their earlier step-function contraction:

* Lemma 7.5 for the unguarded canonical raw reference law; and
* the reciprocal weighted `VV-II` row comparing the final actual law with
  that same reference law.

The prime-power constant is chosen before `W` and the later coefficient
box.  Both analytic remainders retain the sharp moving-low rate after
multiplication by `log L`.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PaperGuardCensus

namespace BridgeData

variable {Head : Type*} [Fintype Head] [DecidableEq Head]

/-- Exact sum of the residual-physical and guard-deletion row errors used
to compare the actual valuation law with the raw canonical law. -/
def canonicalNonstepPowerCorrection
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ) (Cprom Cbank W : ℕ) (Acoef Aphys : ℝ)
    (n : ℕ) : ℝ :=
  physicalPowerCorrectionRowError
      (canonicalPhysicalPowerCorrectionEpsilon Aphys Cmax n)
      (canonicalPhysicalPowerCorrectionConstant P I Cmax W Acoef) n W +
    guardPowerCorrectionWeightedMajorant Cprom Cbank
      (PaperStatisticNorm.valuationLogCoefficient Cmax W)
      (canonicalGuardPerturbationConstant P I
        (Acoef * PaperStatisticNorm.valuationLogCoefficient Cmax W)) n





end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperNonstepSlowNuisanceCorrection -/
section


/-!
# Nuisance correction for the literal non-step slow score

The source covariance vector is estimated from the exact primewise
coefficients `g_p = alpha_{j(p)} - t_p`.  Its natural size is therefore
`Cmarked * sum |g_p|/p`, with no band-centre surrogate and no least-centre
division.  This is the finite statement needed before the sharp
`alpha_0 -> 0` eventual conversion.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Relative moving-low rate for the literal slow-score nuisance
correction after `primeDeviationL1 <= CL1 * w` and `amin <= alpha_i`. -/
def nonstepSlowNuisanceRate
    (Cmarked gamma CL1 amin : ℝ) : ℝ :=
  ((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
      (Cmarked * CL1)) / gamma) *
    (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
      Cmarked) / amin











end BridgeData

end

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

/-- Squarefree lower constant with a literal relative variance factor. -/
def paperScaleSquarefreeSlowConstant
    (varianceFactor anchorFloor rowError Eprofile CKernel C K invW : ℝ) : ℝ :=
  (canonicalSlowKappa / 4) * anchorFloor * varianceFactor -
    rowError * slowL2Constant C K -
    (4 * pairCovarianceScale Eprofile) * slowL1Constant C K ^ 2 -
    (2 * Eprofile) * slowL2Constant C K -
    signedSecondConstant Eprofile CKernel * invW * slowL2Constant C K

/-- Final full-valuation/nuisance slow constant at the same paper scale. -/
def paperScaleLemma86SlowConstantOfRow
    (varianceFactor anchorFloor rowError Eprofile CKernel C K invW R
      Cmarked gamma : ℝ) : ℝ :=
  paperScaleSquarefreeSlowConstant varianceFactor anchorFloor rowError
      Eprofile CKernel C K invW -
    ((1 + C) * (7 + C * K)) * R -
    (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
      (Cmarked * (7 + C * K))) ^ 2 / gamma

/-- Matching squarefree upper constant at the literal paper scale. -/
def paperScaleSquarefreeSlowUpperConstant
    (Eprofile CF CKernel C K invW : ℝ) : ℝ :=
  CKernel * slowL1Constant C K ^ 2 +
    CF * slowL2Constant C K +
    (4 * pairCovarianceScale Eprofile) * slowL1Constant C K ^ 2 +
    (2 * Eprofile) * slowL2Constant C K +
    signedSecondConstant Eprofile CKernel * invW * slowL2Constant C K

/-- Matching full-valuation upper constant; nuisance regression can only
decrease the variance, so no nuisance loss appears here. -/
def paperScaleLemma86SlowUpperConstantOfRow
    (Eprofile CF CKernel C K invW R : ℝ) : ℝ :=
  paperScaleSquarefreeSlowUpperConstant Eprofile CF CKernel C K invW +
    ((1 + C) * (7 + C * K)) * R







end BridgeData

end Erdos390.Full.PaperBridgeFit

end

end

/- Source module: Erdos390.Full.PaperActualCompensatedMarkedRowProfiles -/
section


/-!
# The compensated slow marked row from literal analytic inputs

This removes two legacy contracts from the marked-row side of Lemma 8.6:
the squarefree marked row is derived from the signed divisor profiles, and
the prime-power correction is supplied by the literal weighted `VV-II` row.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance
open PaperPrimePowerRelativeQuadratic PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The explicit signed-profile constant in the squarefree marked row. -/
def actualSquarefreeMarkedConstant
    (C K Eprofile CF CKernel invW : ℝ) : ℝ :=
  (CKernel * (7 + C * K) + CF * (1 + C)) +
    (4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
        (7 + C * K) +
      (2 * Eprofile) * (1 + C) +
      ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
          CKernel) * (1 + C) * invW



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperLemma86CommonConstants -/
section


/-!
# Common paper constants for Lemma 8.6

The arithmetic terminal naturally produces three explicit constants for the
pointwise, first-moment, and second-moment compensated-coefficient bounds.
This file replaces them by one positive constant `Ccmp`, exactly as in the
paper.  The choice depends only on the already fixed regression constant and
therefore precedes `W`, the mesh, the head data, and the effective tilt box.

We also record the exact algebra which turns the geometric lower estimate
`w^2 <= (456 / cMesh^2) V` into the positive-factor form
`(cMesh^2 / 456) w^2 <= V` used by the variance assembly.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport

namespace BridgeData

/-- The fixed reciprocal-prime-mass constant used in the Lemma 8.6
coefficient ledger. -/
def paperLemma86BandTConstant : ℝ := 2 * Real.log 4







variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]





/-- Positive geometric variance factor used by the paper. -/
def paperLemma86VarianceFactor (cMesh : ℝ) : ℝ := cMesh ^ 2 / 456





end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalLemma86RemainingOutputsEventually -/
section


/-!
# Closed remaining outputs of paper Lemma 8.6

This file closes the three quantitative conclusions not contained in the
geometric/coefficient umbrella: two-sided paper-scale slow variance, the
relative prime-power quadratic error, and every compensated marked prime
row.  Its public theorem has no analytic hypotheses, anchor data, contracts,
or abstract comparison assumptions.  The two mesh parameters remain
independent and all constants used to choose the prime cutoff precede the
cutoff and the effective tilt box.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PrimeSums PaperWeightedInverseExport
open OmittedTiltPairChamber PaperPrimePowerChamberError
open PrimeSquarefreeDirichletGeometry FiniteAnchoredDirichletQuadratic
open RegularMeshPrimeCutoffs PaperPermittedRegularMesh
open PaperCanonicalSlowKappa

namespace BridgeData





/-- A fixed upper-variance constant obtained by replacing every vanishing
profile by `1`, the reciprocal cutoff by `1`, and the weighted power row by
the fixed majorant `Rmax`. -/
def paperScaleLemma86SlowUpperUniformConstant
    (CF CKernel C K Rmax : ℝ) : ℝ :=
  paperScaleLemma86SlowUpperConstantOfRow 1 CF CKernel C K 1 Rmax



/- The main assumption-free eventual theorem is assembled below from the
geometry/coefficient terminal and the literal finite variance and marked-row
estimates. -/



/-!
The final paper interface below deliberately repeats the quantitative
clauses instead of returning an opaque package.  Thus its type itself checks
that the geometry, inverse, regression, prime-power, variance, and marked-row
conclusions all use one and the same finite Schur equivalence `e z hz`.
-/


end BridgeData

end


end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87CanonicalFullGap -/
section


/-!
# Full covariance gap from the exact Lemmas 8.4 and 8.6 outputs

This connector eliminates the `HasCovarianceGap` premise used by the marked
row and ODE modules.  A sharp inverse for the literal actual band Schur map
gives the fast quadratic gap; Lemma 8.6 supplies the compensated slow gap
and regression bound.  The finite fast/slow and nuisance Schur identities
then give the full covariance gap.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport
open MovingLowGaugeTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The explicit full-gap constant generated by the two Schur stages. -/
def canonicalTwoStageFullGap
    [Nonempty Head] [Nonempty Band]
    (Cinv gammaSlow Creg gammaNuisance : ℝ) : ℝ :=
  let gammaFast :=
    rawDLowerWeight B.harmonicMass B.bandCenter ^ 2 /
      (sharpWeightTotal B.harmonicMass B.bandCenter * Cinv)
  let gammaMain := min gammaFast gammaSlow /
    (1 + 2 * B.gaugeCenterSquareSum * (1 + Creg ^ 2))
  min gammaMain gammaNuisance /
    (3 + 2 * (B.canonicalCrossBound / gammaNuisance) ^ 2)



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87MarkedProfilesAssembly -/
section


/-!
# Proposition 8.7 marked row from literal profile inputs

This file composes the two independently proved component rows with the
exact two-stage Schur solve.  In particular, neither component marked row
nor the marked row of the ODE vector field is assumed.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Constant in the ordinary-fast marked row before applying the ordinary
inverse to the projected target. -/
def fastProfilesMarkedConstant
    (dimension H K Eprofile CF Cprod R Cmarked gamma invW : ℝ) : ℝ :=
  (Cprod * K + CF) +
    ((4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) * H +
      2 * Eprofile +
      ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 + Cprod) *
        invW) + R +
    ((dimension * (Cmarked * H)) / gamma) * (dimension * Cmarked)

/-- Constant in the compensated-slow marked row after factoring out
`w / p`. -/
def slowProfilesMarkedConstant
    (dimension C K R Eprofile CF CKernel Cmarked gamma invW : ℝ) : ℝ :=
  actualSquarefreeMarkedConstant C K Eprofile CF CKernel invW +
    (1 + C) * R +
    ((dimension * (Cmarked * (7 + C * K))) / gamma) *
      (dimension * Cmarked)



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87UniformMarkedProfiles -/
section


/-!
# Uniform Proposition 8.7 marked rows on a preselected effective ball

This is the exact quantifier wrapper used by the ODE theorem.  It turns the
literal analytic inputs, uniform on a previously selected ball, into the
single marked-row estimate expected by the integration argument.
-/

open scoped BigOperators
open Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The fixed coefficient multiplying `1/p` after both stages of the exact
Schur solve have been assembled. -/
def vectorFieldProfilesMarkedConstant
    (H K Eprofile CF Cprod CKernel R Cmarked gammaNuisance
      CinvOrd Tband Tslow Vlower Creg : ℝ) : ℝ :=
  fastProfilesMarkedConstant
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ))
      H K Eprofile CF Cprod R Cmarked gammaNuisance
      (1 / (B.sampleData.W : ℝ)) * (CinvOrd * Tband) +
    (Tslow / Vlower) *
      (slowProfilesMarkedConstant
        (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ))
        Creg K R Eprofile CF CKernel Cmarked gammaNuisance
        (1 / (B.sampleData.W : ℝ)) * B.w)





end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87MarkedProfilesMajorant -/
section


/-!
# An ambient-independent majorant for the Proposition 8.7 marked row

The signed-profile and nuisance errors are `o(1 / log L)`, while the total
harmonic mass is `O(log L)`.  This file records the exact finite inequality
which converts those rates into one constant independent of the ambient
integer.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

set_option maxHeartbeats 1200000

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Explicit fixed majorant after the two products with the harmonic mass
have each been made at most one. -/
def vectorFieldProfilesMarkedMajorant
    (K CF Cprod CKernel Rmax gammaFloor CinvOrd Tband Tslow Vlower Creg : ℝ) : ℝ :=
  let d := Real.sqrt
    (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  let A := 1 / DickmanBasic.rho DickmanBasic.U
  let fast :=
    Cprod * K + CF +
      4 * (2 + 2 * A) + 2 + ((A + 2) ^ 2 + Cprod) + Rmax +
      d ^ 2 / gammaFloor
  let slow :=
    CKernel * (7 + Creg * K) + CF * (1 + Creg) +
      4 * (2 + 2 * A) * (7 + Creg * K) +
      2 * (1 + Creg) +
      ((A + 2) ^ 2 + CKernel) * (1 + Creg) +
      (1 + Creg) * Rmax + d ^ 2 * (7 + Creg * K) / gammaFloor
  fast * (CinvOrd * Tband) +
    (Tslow / Vlower) * (slow * B.w)



/-- Mesh-independent form of the same majorant.  The actual compensated
target is bounded by `targetScale * w` and the slow variance by
`gammaSlow * w^2`; the two powers of the moving mesh scale cancel exactly. -/
def vectorFieldProfilesMarkedScaledMajorant
    (K CF Cprod CKernel Rmax gammaFloor CinvOrd Tband
      targetScale gammaSlow Creg : ℝ) : ℝ :=
  let d := Real.sqrt
    (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  let A := 1 / DickmanBasic.rho DickmanBasic.U
  let fast :=
    Cprod * K + CF +
      4 * (2 + 2 * A) + 2 + ((A + 2) ^ 2 + Cprod) + Rmax +
      d ^ 2 / gammaFloor
  let slow :=
    CKernel * (7 + Creg * K) + CF * (1 + Creg) +
      4 * (2 + 2 * A) * (7 + Creg * K) +
      2 * (1 + Creg) +
      ((A + 2) ^ 2 + CKernel) * (1 + Creg) +
      (1 + Creg) * Rmax +
      d ^ 2 * (7 + Creg * K) / gammaFloor
  fast * (CinvOrd * Tband) + (targetScale / gammaSlow) * slow



/-- A version of the scaled majorant which is defined before a particular
bridge datum exists.  The nuisance dimension is replaced by the uniform
head-cardinality ceiling.  Consequently this constant can be quantified
before the ambient integer and before the canonical sample is constructed. -/
def vectorFieldProfilesMarkedScaledHeadMajorant
    (Head : Type*) [Fintype Head]
    (K CF Cprod CKernel Rmax gammaFloor CinvOrd Tband
      targetScale gammaSlow Creg : ℝ) : ℝ :=
  let D2 := (Fintype.card Head + 1 : ℝ)
  let A := 1 / DickmanBasic.rho DickmanBasic.U
  let fast :=
    Cprod * K + CF +
      4 * (2 + 2 * A) + 2 + ((A + 2) ^ 2 + Cprod) + Rmax +
      D2 / gammaFloor
  let slow :=
    CKernel * (7 + Creg * K) + CF * (1 + Creg) +
      4 * (2 + 2 * A) * (7 + Creg * K) +
      2 * (1 + Creg) +
      ((A + 2) ^ 2 + CKernel) * (1 + Creg) +
      (1 + Creg) * Rmax +
      D2 * (7 + Creg * K) / gammaFloor
  fast * (CinvOrd * Tband) + (targetScale / gammaSlow) * slow



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87CanonicalMarkedProfilesEventually -/
section


/-!
# Canonical eventual moving-prime row for Proposition 8.7

All signed-profile, prime-power, nuisance, kernel, harmonic-mass, and regular
mesh inputs are selected here.  The only remaining call-site assumptions are
the exact same-map Schur solve and its ordinary/slow quantitative outputs.
Fixed head primes are intentionally outside this theorem.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PrimeSums PaperWeightedInverseExport
open RegularMeshPrimeCutoffs

namespace BridgeData

/-! The cutoff is independent of the regular mesh.  Keeping it as a named
object makes the paper quantifier order visible in the exported statement:
`W` is fixed before the head data, the mesh, and the ODE ball. -/
noncomputable def canonicalMovingPrimeMarkedRowCutoff : ℕ :=
  max 2 RegularMeshPrimeCutoffs.canonicalActualMomentCutoff



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87LiteralBandBalance -/
section


/-!
# Literal residual-balance form of paper Proposition 8.7

The generalized Proposition 8.7 engine takes a prescribed vector of band
moment increments.  In the paper that vector is not arbitrary: its `j`th
coordinate is the initial sum of the marked residuals in the `j`th prime
band.  This file records that specialization and derives the displayed
post-fit identity `sum_{p in P_j} r_p = 0` exactly at finite `n`.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The active marked residual summed over one actual arithmetic prime band. -/
def markedBandResidual [Nonempty Head]
    (markedTarget : ℕ → ℝ) (xi : B.ParamSpace) (j : Band) : ℝ :=
  ∑ p ∈ B.partition.data.fiber j,
    (markedTarget p.1 - B.paperMoment (B.markedValuation p.1) xi)





/-- The path-level output of the generalized finite fit, with the monitored
set specialized to every actual medium prime. -/
def IsPaperProposition87Path
    [Nonempty Head]
    {Fixed : Type*} [Fintype Fixed]
    (Delta : Band → ℝ) (a : NNReal)
    (markedTarget : ℕ → ℝ) (N Cpost : ℝ)
    (fixedValue : Fixed → ℕ) (fixedWeight : Fixed → ℝ)
    (quota : ℤ) (path : ℝ → B.ParamSpace) : Prop :=
  path 0 = 0 ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
      B.effectiveParamEquiv.symm (path t) ∈
        closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
      B.paperEffectiveSize (path t) ≤ 3 * (a : ℝ)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt path
        (B.vectorFamily.vectorField (B.targetVector Delta) (path t))
        (Icc (0 : ℝ) 1) t) ∧
    (∀ j : Band,
      B.paperMoment (B.bandScore j) (path 1) =
        B.paperMoment (B.bandScore j) 0 + Delta j) ∧
    B.paperMoment B.physicalScore (path 1) =
      B.paperMoment B.physicalScore 0 ∧
    B.paperMoment B.ordinaryLogScore (path 1) =
      B.paperMoment B.ordinaryLogScore 0 ∧
    (∀ h : B.HeadIndex,
      B.paperMoment (B.headIndicator h.1) (path 1) =
        B.paperMoment (B.headIndicator h.1) 0) ∧
    (∀ p : ℕ, p.Prime → p ≤ B.sampleData.W →
      B.paperMoment (B.markedValuation p) (path 1) =
        B.paperMoment (B.markedValuation p) 0) ∧
    B.paperMoment B.primeLogScore (path 1) =
      B.paperMoment B.primeLogScore 0 ∧
    (∀ p ∈ ArithmeticModel.primeBand
        B.sampleData.n B.sampleData.W,
      |markedTarget p -
          B.paperMoment (B.markedValuation p) (path 1)| ≤
        Cpost * N / ((p : ℝ) * B.L)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℕ,
      B.ambientCombinedWeight
          (frozenAmbientWeight fixedValue fixedWeight)
          (path t) x ∈ Icc (0 : ℝ) 1) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ f : Fixed,
      B.combinedWeight fixedWeight (path t) (Sum.inl f) =
        B.combinedWeight fixedWeight 0 (Sum.inl f)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
      (∑ m : B.sampleData.Sample,
        B.activeCoordinateWeight (path t) m) = B.q) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
      (∑ x : Fixed ⊕ B.sampleData.Sample,
        B.combinedWeight fixedWeight (path t) x) = (quota : ℝ)

/-- The literal conclusion displayed in paper Proposition 8.7.  In addition
to all finite-fit outputs, it states the exact residual cancellation in every
actual prime band and the pointwise rate for every `W < p ≤ y`. -/
def HasPaperProposition87Conclusion
    [Nonempty Head]
    {Fixed : Type*} [Fintype Fixed]
    (Delta : Band → ℝ) (a : NNReal)
    (markedTarget : ℕ → ℝ) (N Cpost : ℝ)
    (fixedValue : Fixed → ℕ) (fixedWeight : Fixed → ℝ)
    (quota : ℤ) : Prop :=
  ∃ path : ℝ → B.ParamSpace,
    B.IsPaperProposition87Path Delta a markedTarget N Cpost
      fixedValue fixedWeight quota path ∧
    ∀ j : Band, B.markedBandResidual markedTarget (path 1) j = 0



end BridgeData

open ArithmeticModel PaperGuardCensus PaperPermittedRegularMesh
open RegularMeshPrimeCutoffs

/-- Paper-order, literal-residual statement of Proposition 8.7. -/
def CanonicalProposition87LiteralBalanceStatement
    (cMesh : ℝ)
    (I : PhysicalIntervals) (U : ℝ)
    (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank) : Prop :=
  0 < cMesh →
  1 ≤ U →
  (∀ sigma, 1 ≤ I.lower sigma) →
  (∀ sigma, I.upper sigma ≤ U) →
  ∃ meshTol : ℝ, 0 < meshTol ∧
  ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
    ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
      (Phead : Head → HeadPattern.Pattern),
    (∀ h : Head, ∀ p : ℕ,
      p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
    ∀ (Ctarget Cinitial Cmass Cfixed Cactive marginFloor : ℝ),
      0 ≤ Ctarget → 0 ≤ Cinitial → 0 ≤ Cmass →
      0 ≤ Cfixed → 0 ≤ Cactive → 0 < marginFloor →
    ∃ a : NNReal, 0 < (a : ℝ) ∧
    ∃ Cpost : ℝ, 0 ≤ Cpost ∧
    ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
      (hdelta : 0 < delta)
      (_hPermitted : IsPermitted (cMesh := cMesh) M),
      delta + eta ≤ meshTol →
      ∀ᶠ n : ℕ in atTop,
        ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
          B.sampleData.n = n → B.sampleData.W = W →
          ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : ∀ c : Cell Head,
              (rawCell Phead I B.sampleData.n c \
                (ledger B.sampleData.n).guards).Nonempty),
            (hcanonical : B.sampleData = canonicalSampleData
              (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
                hsep hremaining) →
            (hpartition : ∃ (hWne : B.sampleData.W ≠ 0)
                (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
            (hscale : B.w = delta + eta) →
            ∀ (T : BarycentricTarget B.sampleData),
              marginFloor ≤ T.cellMassMargin →
              B.baseline = T.baseline →
            ∀ (Delta : Fin (M.cellCount + 1) → ℝ),
              B.HasTargetEnvelopes Ctarget Delta →
            ∀ (markedTarget : ℕ → ℝ) (N : ℝ),
              0 ≤ N →
              B.q ≤ Cmass * N →
              (∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
                |markedTarget p - B.paperMoment (B.markedValuation p) 0| ≤
                  Cinitial * N / ((p : ℝ) * B.L)) →
              (∀ j, Delta j = B.markedBandResidual markedTarget 0 j) →
            ∀ {Fixed : Type*} [Fintype Fixed]
              (fixedValue : Fixed → ℕ) (fixedWeight : Fixed → ℝ)
              (quota : ℤ),
              (quota : ℝ) = (∑ f, fixedWeight f) + B.q →
              B.sampleData.HeadPatternsSeparated →
              (∀ x,
                BridgeData.frozenAmbientWeight fixedValue fixedWeight x ∈
                  Icc (0 : ℝ) 1) →
              (∀ m : B.sampleData.Sample,
                BridgeData.frozenAmbientWeight fixedValue fixedWeight
                  (B.sampleData.value m) ≤ Cfixed / B.L) →
              (∀ m : B.sampleData.Sample,
                B.baseline.baseWeight m ≤ Cactive / B.L) →
              B.HasPaperProposition87Conclusion Delta a markedTarget N Cpost
                fixedValue fixedWeight quota

namespace BridgeData



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalHeadPhysicalTarget -/
section


/-!
# The paper's explicit head simplex and physical interpolation

The head barycenter is not supplied as an arbitrary probability vector in
the paper.  Its nonzero-vertex coefficients are exactly `A_p / (E*q)` and
the zero-vertex coefficient is the remaining mass.  This file constructs
that literal vector from the finite reserve ledger and combines it with the
two fixed physical intervals around `mu`.
-/

open scoped BigOperators

namespace Erdos390.Full

open PaperGuardCensus PaperBridgeFit PaperHeadSimplex ArithmeticModel

noncomputable section

namespace PaperGuardCensus

/-- Explicit finite head-reserve data from the paper's simplex
`{0, E e_p : p in P}`.  The two margin fields are precisely the
coordinatewise reserve inequalities; no probability vector is stored. -/
structure HeadSimplexReserve (P : Finset ℕ) where
  exponent : ℕ
  exponent_pos : 0 < exponent
  activeMass : ℝ
  activeMass_pos : 0 < activeMass
  target : {p : ℕ // p ∈ P} → ℝ
  margin : ℝ
  margin_pos : 0 < margin
  vertex_margin : ∀ p,
    margin ≤ target p / ((exponent : ℝ) * activeMass)
  zero_margin :
    margin ≤ 1 - ∑ p : {p : ℕ // p ∈ P},
      target p / ((exponent : ℝ) * activeMass)

namespace HeadSimplexReserve

variable {P : Finset ℕ} (R : HeadSimplexReserve P)

/-- Coefficient of the zero head vertex. -/
def zeroCoefficient : ℝ :=
  1 - ∑ p : {p : ℕ // p ∈ P},
    R.target p / ((R.exponent : ℝ) * R.activeMass)

/-- Literal barycentric coefficients on `0` and `E e_p`. -/
def beta : PaperHeadSimplex.Tag P → ℝ
  | none => R.zeroCoefficient
  | some p => R.target p / ((R.exponent : ℝ) * R.activeMass)

theorem zeroCoefficient_margin : R.margin ≤ R.zeroCoefficient := by
  exact R.zero_margin

theorem beta_margin (h : PaperHeadSimplex.Tag P) :
    R.margin ≤ R.beta h := by
  cases h with
  | none => exact R.zeroCoefficient_margin
  | some p => exact R.vertex_margin p

theorem beta_pos (h : PaperHeadSimplex.Tag P) : 0 < R.beta h :=
  R.margin_pos.trans_le (R.beta_margin h)

theorem beta_sum : ∑ h : PaperHeadSimplex.Tag P, R.beta h = 1 := by
  rw [Fintype.sum_option]
  simp only [beta, zeroCoefficient]
  ring







end HeadSimplexReserve

/-- The fixed interval inequalities used by the paper's two-pool
interpolation.  They state that the entire minus interval lies below
`mu-eta` and the entire plus interval lies above `mu+eta`. -/
structure PhysicalInterpolationTarget (I : PhysicalIntervals) where
  mu : ℝ
  eta : ℝ
  eta_pos : 0 < eta
  minus_below : Real.log (I.upper .minus) ≤ mu - eta
  plus_above : mu + eta ≤ Real.log (I.lower .plus)

namespace PhysicalInterpolationTarget

variable {I : PhysicalIntervals}

/-- A fixed upper bound for the difference of any two physical means in
the selected pools. -/
def physicalSpan (I : PhysicalIntervals) : ℝ :=
  Real.log (I.upper .plus) - Real.log (I.lower .minus)

theorem lower_minus_lt_upper_plus : I.lower .minus < I.upper .plus :=
  (I.lower_lt_upper .minus).trans
    (I.separated.trans (I.lower_lt_upper .plus))

theorem physicalSpan_pos : 0 < physicalSpan I := by
  unfold physicalSpan
  apply sub_pos.mpr
  exact Real.strictMonoOn_log (I.lower_pos .minus)
    ((I.lower_pos .plus).trans (I.lower_lt_upper .plus))
    lower_minus_lt_upper_plus

/-- Uniform physical splitting margin obtained only from the fixed endpoint
gap around `mu`. -/
def tau (K : PhysicalInterpolationTarget I) : ℝ :=
  K.eta / physicalSpan I

theorem tau_pos (K : PhysicalInterpolationTarget I) : 0 < K.tau :=
  div_pos K.eta_pos physicalSpan_pos

end PhysicalInterpolationTarget

end PaperGuardCensus

namespace PaperBridgeFit.BridgeData

variable {P : Finset ℕ} {Band : Type*}
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData (PaperHeadSimplex.Tag P) Band)

 theorem cellLogMean_le_log_upper
    (I : PhysicalIntervals)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (c : Cell (PaperHeadSimplex.Tag P)) :
    cellLogMean B.sampleData c ≤ Real.log (I.upper c.2) := by
  rw [← B.cellPhysicalMean_eq_cellLogMean c]
  apply B.cellPhysicalMean_le_of_cellwise c _
  intro m hm
  exact (B.physicalScore_le_log_upper I hhi m).trans_eq (by
    congr 1
    exact congrArg I.upper (congrArg Prod.snd hm))

 theorem log_lower_le_cellLogMean
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (c : Cell (PaperHeadSimplex.Tag P)) :
    Real.log (I.lower c.2) ≤ cellLogMean B.sampleData c := by
  rw [← B.cellPhysicalMean_eq_cellLogMean c]
  apply B.le_cellPhysicalMean_of_cellwise c _
  intro m hm
  exact (B.log_lower_lt_physicalScore I hlo m).le.trans_eq' (by
    congr 1
    exact congrArg I.lower (congrArg Prod.snd hm))

 theorem poolLogMean_le_log_upper
    (I : PhysicalIntervals)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (R : HeadSimplexReserve P) (sigma : PhysicalSign) :
    poolLogMean B.sampleData R.beta sigma ≤ Real.log (I.upper sigma) := by
  unfold poolLogMean
  calc
    (∑ h : PaperHeadSimplex.Tag P,
        R.beta h * cellLogMean B.sampleData (h, sigma)) ≤
        ∑ h : PaperHeadSimplex.Tag P,
          R.beta h * Real.log (I.upper sigma) := by
      apply Finset.sum_le_sum
      intro h hh
      exact mul_le_mul_of_nonneg_left
        (B.cellLogMean_le_log_upper I hhi (h, sigma))
        (R.beta_pos h).le
    _ = Real.log (I.upper sigma) := by
      rw [← Finset.sum_mul, R.beta_sum, one_mul]

 theorem log_lower_le_poolLogMean
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (R : HeadSimplexReserve P) (sigma : PhysicalSign) :
    Real.log (I.lower sigma) ≤
      poolLogMean B.sampleData R.beta sigma := by
  unfold poolLogMean
  calc
    Real.log (I.lower sigma) =
        ∑ h : PaperHeadSimplex.Tag P,
          R.beta h * Real.log (I.lower sigma) := by
      rw [← Finset.sum_mul, R.beta_sum, one_mul]
    _ ≤ ∑ h : PaperHeadSimplex.Tag P,
        R.beta h * cellLogMean B.sampleData (h, sigma) := by
      apply Finset.sum_le_sum
      intro h hh
      exact mul_le_mul_of_nonneg_left
        (B.log_lower_le_cellLogMean I hlo (h, sigma))
        (R.beta_pos h).le

/-- The exact `BarycentricTarget` derived from the paper's displayed head
coefficients and fixed two-pool endpoint inequalities. -/
def barycentricTargetOfPaperData
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (R : HeadSimplexReserve P)
    (K : PhysicalInterpolationTarget I) :
    BarycentricTarget B.sampleData where
  beta := R.beta
  beta_pos := R.beta_pos
  beta_sum := R.beta_sum
  betaFloor := R.margin
  betaFloor_pos := R.margin_pos
  betaFloor_le := R.beta_margin
  mu := K.mu
  tau := K.tau
  tau_pos := K.tau_pos
  pool_separated := by
    have hm := B.poolLogMean_le_log_upper I hhi R .minus
    have hp := B.log_lower_le_poolLogMean I hlo R .plus
    linarith [K.minus_below, K.plus_above, K.eta_pos]
  left_interior := by
    have hmUpper := B.poolLogMean_le_log_upper I hhi R .minus
    have hpUpper := B.poolLogMean_le_log_upper I hhi R .plus
    have hmLower := B.log_lower_le_poolLogMean I hlo R .minus
    have hspan :
        poolLogMean B.sampleData R.beta .plus -
            poolLogMean B.sampleData R.beta .minus ≤
              PhysicalInterpolationTarget.physicalSpan I := by
      unfold PhysicalInterpolationTarget.physicalSpan
      linarith
    have hscaled : K.tau *
        (poolLogMean B.sampleData R.beta .plus -
          poolLogMean B.sampleData R.beta .minus) ≤ K.eta := by
      unfold PhysicalInterpolationTarget.tau
      rw [div_mul_eq_mul_div,
        div_le_iff₀ PhysicalInterpolationTarget.physicalSpan_pos]
      nlinarith [K.eta_pos.le]
    exact hscaled.trans (by linarith [K.minus_below])
  right_interior := by
    have hpUpper := B.poolLogMean_le_log_upper I hhi R .plus
    have hmLower := B.log_lower_le_poolLogMean I hlo R .minus
    have hpLower := B.log_lower_le_poolLogMean I hlo R .plus
    have hspan :
        poolLogMean B.sampleData R.beta .plus -
            poolLogMean B.sampleData R.beta .minus ≤
              PhysicalInterpolationTarget.physicalSpan I := by
      unfold PhysicalInterpolationTarget.physicalSpan
      linarith
    have hscaled : K.tau *
        (poolLogMean B.sampleData R.beta .plus -
          poolLogMean B.sampleData R.beta .minus) ≤ K.eta := by
      unfold PhysicalInterpolationTarget.tau
      rw [div_mul_eq_mul_div,
        div_le_iff₀ PhysicalInterpolationTarget.physicalSpan_pos]
      nlinarith [K.eta_pos.le]
    exact hscaled.trans (by linarith [K.plus_above])







end PaperBridgeFit.BridgeData

end

end Erdos390.Full

end


