-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceRegressionLoss_primeValuationScore_le_of_marked
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:19:32.152598+00:00
-- url     : https://prove2.me/submissions/b36b2c46-6a6e-4971-b06b-e4d0dcd95515

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
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















theorem covariance_zero_right (mu : FiniteProbability Omega) (F : Omega → ℝ) :
    mu.covariance F (fun _ ↦ 0) = 0 := by
  simp [covariance, expect]











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







/-- Weighted Cauchy--Schwarz for reciprocal prime coefficients. -/
theorem weightedL1_sq_le_totalWeight_mul_weightedL2Sq
    (c : PrimeIndex n W → ℝ) :
    weightedL1 (reciprocalWeight (n := n) (W := W)) c ^ 2 ≤
      (∑ p : PrimeIndex n W, reciprocalWeight p) *
        weightedL2Sq reciprocalWeight c := by
  let a : PrimeIndex n W → ℝ :=
    fun p ↦ Real.sqrt (reciprocalWeight p)
  let b : PrimeIndex n W → ℝ :=
    fun p ↦ Real.sqrt (reciprocalWeight p) * |c p|
  have hw (p : PrimeIndex n W) : 0 ≤ reciprocalWeight p := by
    unfold reciprocalWeight
    positivity
  have hsqa (p : PrimeIndex n W) : a p ^ 2 = reciprocalWeight p := by
    dsimp only [a]
    rw [Real.sq_sqrt (hw p)]
  have hsqb (p : PrimeIndex n W) : b p ^ 2 =
      reciprocalWeight p * c p ^ 2 := by
    dsimp only [b]
    rw [mul_pow, Real.sq_sqrt (hw p), sq_abs]
  have hab (p : PrimeIndex n W) : a p * b p =
      reciprocalWeight p * |c p| := by
    dsimp only [a, b]
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt (hw p)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  simp_rw [hab, hsqa, hsqb] at hcs
  simpa only [weightedL1, weightedL2Sq] using hcs

















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











/-- Marked nuisance rows control the regression loss of an arbitrary prime
coefficient in the same reciprocal-prime square norm. -/
theorem nuisanceRegressionLoss_primeValuationScore_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma Cmarked totalWeight : ℝ}
    (hgamma : 0 < gamma) (hCmarked : 0 ≤ Cmarked)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hTotal : (∑ p : BandPrime B.sampleData.n B.sampleData.W,
      reciprocalWeight p) ≤ totalWeight)
    (hmarked : ∀ (z : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m z)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (c : BandPrime B.sampleData.n B.sampleData.W → ℝ) :
    inner ℝ
        (B.nuisanceCoefficientOfScore xi hgamma hgap
          (B.primeValuationScore c))
        (B.nuisanceCovarianceVector xi (B.primeValuationScore c)) ≤
      ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          Cmarked ^ 2 * totalWeight / gamma) *
        primeCoefficientL2Sq c := by
  let L1 : ℝ := weightedL1 reciprocalWeight c
  have hL1 : 0 ≤ L1 := by
    dsimp only [L1]
    unfold weightedL1
    exact Finset.sum_nonneg fun p _ ↦
      mul_nonneg (by unfold reciprocalWeight; positivity) (abs_nonneg _)
  have hcoord (z : NuisanceCoord B.HeadIndex) :
      |(B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m z)
          (B.primeValuationScore c)| ≤ Cmarked * L1 := by
    unfold primeValuationScore
    rw [(B.tiltedLaw xi).covariance_sum_right]
    simp_rw [(B.tiltedLaw xi).covariance_smul_right]
    calc
      |∑ p : BandPrime B.sampleData.n B.sampleData.W,
          c p * (B.tiltedLaw xi).covariance
            (fun m ↦ B.nuisanceStatistic m z)
            (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          |c p * (B.tiltedLaw xi).covariance
            (fun m ↦ B.nuisanceStatistic m z)
            (fun m ↦ valuation p.1 (B.sampleData.value m))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          |c p| * (Cmarked * (1 / (p.1 : ℝ))) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hmarked z p) (abs_nonneg _)
      _ = Cmarked * L1 := by
        dsimp only [L1]
        unfold weightedL1 reciprocalWeight
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
  have hK : 0 ≤ Cmarked * L1 := mul_nonneg hCmarked hL1
  have hvec := B.nuisanceCovarianceVector_norm_le_sqrt_card_mul
    xi (B.primeValuationScore c) hK hcoord
  have hvecSq :
      ‖B.nuisanceCovarianceVector xi (B.primeValuationScore c)‖ ^ 2 ≤
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          Cmarked ^ 2 * L1 ^ 2 := by
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hvec 2
    have hcard : 0 ≤
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) := by positivity
    calc
      ‖B.nuisanceCovarianceVector xi (B.primeValuationScore c)‖ ^ 2 ≤
          (Real.sqrt (Fintype.card
              (NuisanceCoord B.HeadIndex) : ℝ) * (Cmarked * L1)) ^ 2 :=
        hsquare
      _ = (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          Cmarked ^ 2 * L1 ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hcard]
        ring
  have hL1Base := weightedL1_sq_le_totalWeight_mul_weightedL2Sq c
  have hnormNonneg : 0 ≤ weightedL2Sq reciprocalWeight c := by
    unfold weightedL2Sq
    exact Finset.sum_nonneg fun p _ ↦
      mul_nonneg (by unfold reciprocalWeight; positivity) (sq_nonneg _)
  have hL1Sq : L1 ^ 2 ≤ totalWeight * primeCoefficientL2Sq c := by
    have h := hL1Base.trans
      (mul_le_mul_of_nonneg_right hTotal hnormNonneg)
    simpa only [L1] using h
  have hcardC : 0 ≤
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * Cmarked ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  have hvecD :
      ‖B.nuisanceCovarianceVector xi (B.primeValuationScore c)‖ ^ 2 ≤
        ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          Cmarked ^ 2 * totalWeight) * primeCoefficientL2Sq c :=
    hvecSq.trans (by
      calc
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            Cmarked ^ 2 * L1 ^ 2 ≤
          ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            Cmarked ^ 2) *
              (totalWeight * primeCoefficientL2Sq c) :=
          mul_le_mul_of_nonneg_left hL1Sq hcardC
        _ = _ := by ring)
  have hloss := B.nuisanceRegressionLoss_bounds
    xi hgamma hgap (B.primeValuationScore c)
  have hdiv := div_le_div_of_nonneg_right hvecD hgamma.le
  calc
    inner ℝ
        (B.nuisanceCoefficientOfScore xi hgamma hgap
          (B.primeValuationScore c))
        (B.nuisanceCovarianceVector xi (B.primeValuationScore c)) ≤
      ‖B.nuisanceCovarianceVector xi (B.primeValuationScore c)‖ ^ 2 /
        gamma := hloss.2
    _ ≤ (((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          Cmarked ^ 2 * totalWeight) * primeCoefficientL2Sq c) / gamma :=
      hdiv
    _ = ((Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          Cmarked ^ 2 * totalWeight / gamma) *
        primeCoefficientL2Sq c := by ring











end Erdos390.Full.PaperBridgeFit.BridgeData

end

end

universe u_1 u_2
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B) {gamma Cmarked totalWeight : Real}
  (hgamma : LT.lt.{0} (0 : Real) gamma),
  LE.le.{0} (0 : Real) Cmarked →
    ∀
      (hgap :
        ∀ (z : Erdos390.Full.PaperBridgeFit.BridgeData.NuisanceSpace.{u_1, u_2} B),
          LE.le.{0} (HMul.hMul.{0, 0, 0} gamma (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} z) (2 : Nat)))
            (Inner.inner.{0, u_1} Real z
              ((Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceCovarianceOperator.{u_1, u_2} B xi :
                  Erdos390.Full.PaperBridgeFit.BridgeData.NuisanceSpace.{u_1, u_2} B →
                    Erdos390.Full.PaperBridgeFit.BridgeData.NuisanceSpace.{u_1, u_2} B)
                z))),
      LE.le.{0}
          (∑ p :
            Erdos390.Full.ArithmeticBandGeometry.BandPrime
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
            Erdos390.Full.PaperSquarefreeSlowQuadraticLower.reciprocalWeight p)
          totalWeight →
        (∀
            (z :
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
                  (Erdos390.Full.PaperBridgeFit.BridgeData.tiltedLaw.{u_1, u_2} B xi)
                  (fun
                      (m :
                        Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) =>
                    WithLp.ofLp.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceStatistic.{u_1, u_2} B m) z)
                  fun
                    (m :
                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) =>
                  Erdos390.Full.ArithmeticModel.valuation (↑p : Nat)
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) m)))
              (HMul.hMul.{0, 0, 0} Cmarked (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑(↑p : Nat) : Real)))) →
          ∀
            (c :
              Erdos390.Full.ArithmeticBandGeometry.BandPrime
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) →
                Real),
            LE.le.{0}
              (Inner.inner.{0, u_1} Real
                (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceCoefficientOfScore.{u_1, u_2} B xi hgamma hgap
                  (Erdos390.Full.PaperBridgeFit.BridgeData.primeValuationScore.{u_1, u_2} B c))
                (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceCovarianceVector.{u_1, u_2} B xi
                  (Erdos390.Full.PaperBridgeFit.BridgeData.primeValuationScore.{u_1, u_2} B c)))
              (HMul.hMul.{0, 0, 0}
                (HDiv.hDiv.{0, 0, 0}
                  (HMul.hMul.{0, 0, 0}
                    (HMul.hMul.{0, 0, 0}
                      (↑(Fintype.card.{u_1}
                            (Erdos390.Full.PaperBridgeFit.NuisanceCoord.{u_1}
                              (Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1, u_2} B))) :
                        Real)
                      (HPow.hPow.{0, 0, 0} Cmarked (2 : Nat)))
                    totalWeight)
                  gamma)
                (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeCoefficientL2Sq c)) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceRegressionLoss_primeValuationScore_le_of_marked
