-- Prove2me | Definitions.Def_erdos390_analytic_foundations_003
-- name    : erdos390_analytic_foundations_003
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-17T14:47:30.020569+00:00
-- url     : https://prove2.me/theorems/8adc2a77-42e9-47f1-b931-cfb68e16dd5d
-- title:
--   Prime quadrature, explicit cutoffs and conditioned Poisson laws
-- statement:
--   This bundle defines the continuum-to-prime discretization data: Abel summation weights and error kernels, interval partition certificates, explicit natural prime cutoffs, harmonic and logarithmic cell moments, conditioned Poisson sample laws, and the covariance kernel and its continuous divided-difference representatives.
--
--   Given a relative mesh with endpoints $t_k$ and the arithmetic smoothness scale $y(n)$, the natural cutoffs are
--   $$c_0=W,\qquad c_{k+1}=\left\lfloor\exp(t_k\log y(n))\right\rfloor.$$
--   Interval certificates relate each band to its natural cutoff endpoints. The conditioned-law covariance kernel is recorded in the form
--   $$K(s,t)=F(s+t)-F(s)F(t),$$
--   where $F$ is the Dickman profile used by the source construction. Finite shell laws and their product/global versions encode the corresponding Poisson sampling framework.
--
--   Moment-readiness and scale-separation structures package the inequalities required to construct an occupied arithmetic partition. The definitions expose the finite and continuum quantities whose comparison is established by the separate quadrature theorems.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/RegularMeshPrimeCutoffs.lean; grouped definitions extracted from multiple source modules at this commit, including Erdos390.Full.PaperEffectiveScoreBound, Erdos390.Full.PrimeBandQuadrature, Erdos390.Full.PositiveCellTransfer, with the remaining originating modules identified by source-module comments in the definition body.

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002


/- Source module: Erdos390.Full.PaperEffectiveScoreBound -/
section


/-!
# Dimension-free score control in the paper's effective parameter norm

The Euclidean parameter norm has one coordinate per prime band and is not the
norm used in the non-circular argument of Proposition 8.7.  This file proves
the exact re-expansion of the finite exponential-family score into the
effective prime fugacities and the fixed nuisance block.  It then obtains a
pointwise score bound whose constant is independent of the number of bands.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit
namespace BridgeData

open ArithmeticModel ArithmeticBandGeometry
open Erdos390.Full.PaperStatisticNorm
open Erdos390.Full.PaperStatisticNorm.BridgeData

noncomputable section

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Reconstructing all band coefficients from the quotient gauge gives
exactly the gauge part of the exponential score. -/
theorem sum_bandParameter_mul_bandScore_eq_gauge
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    (∑ j : Band, B.bandParameter xi j * B.bandScore j m) =
      ∑ k : B.GaugeIndex,
        xi (MomentCoord.gauge k) * B.gaugeScore k m := by
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun j : Band => B.bandParameter xi j * B.bandScore j m) B.lowBand]
  simp only [B.bandParameter_low, B.bandParameter_gauge]
  unfold gaugeScore
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hfactor :
      (∑ k : B.GaugeIndex,
        xi (MomentCoord.gauge k) *
          (B.lowRatio k * B.bandScore B.lowBand m)) =
        (∑ k : B.GaugeIndex,
          B.lowRatio k * xi (MomentCoord.gauge k)) *
            B.bandScore B.lowBand m := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hfactor]
  ring

/-- Fiberwise expansion of a band-linear valuation statistic into its
individual prime coefficients. -/
theorem sum_bandParameter_mul_bandScore_eq_primeSum
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    (∑ j : Band, B.bandParameter xi j * B.bandScore j m) =
      ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.bandParameter xi (B.partition.band p) *
          valuation p.1 (B.sampleData.value m) := by
  unfold bandScore
  rw [← Finset.sum_fiberwise Finset.univ B.partition.band
    (fun p => B.bandParameter xi (B.partition.band p) *
      valuation p.1 (B.sampleData.value m))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpj : B.partition.band p = j := (Finset.mem_filter.mp hp).2
  rw [hpj]

/-- Exact main-score identity: quotient-gauge plus compensated slow score is
the valuation sum with the literal effective prime fugacity. -/
theorem gaugeSlowScore_eq_effectivePrimeSum
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    (∑ k : B.GaugeIndex,
        xi (MomentCoord.gauge k) * B.gaugeScore k m) +
        xi MomentCoord.slow * (B.slowScore m / B.w) =
      ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.effectivePrimeCoefficient xi p *
          valuation p.1 (B.sampleData.value m) := by
  rw [← B.sum_bandParameter_mul_bandScore_eq_gauge xi m,
    B.sum_bandParameter_mul_bandScore_eq_primeSum xi m]
  unfold effectivePrimeCoefficient slowScore
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · rfl
  · have hdiv :
        xi MomentCoord.slow *
            ((∑ p : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation p *
                valuation p.1 (B.sampleData.value m)) / B.w) =
          (xi MomentCoord.slow / B.w) *
            (∑ p : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation p *
                valuation p.1 (B.sampleData.value m)) := by
        field_simp [ne_of_gt B.w_pos]
    rw [hdiv, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring

/-- Canonical splitting of the quotient/slow coordinate sum. -/
 def mainCoordEquiv (Gauge : Type*) :
    MainCoord Gauge ≃ Gauge ⊕ Unit where
  toFun
    | .gauge j => Sum.inl j
    | .slow => Sum.inr ()
  invFun
    | Sum.inl j => .gauge j
    | Sum.inr _ => .slow
  left_inv c := by cases c <;> rfl
  right_inv
    | Sum.inl j => rfl
    | Sum.inr () => rfl

 theorem sum_mainCoord {Gauge : Type*} [Fintype Gauge]
    (f : MainCoord Gauge → ℝ) :
    (∑ c : MainCoord Gauge, f c) =
      (∑ j : Gauge, f (.gauge j)) + f .slow := by
  calc
    (∑ c : MainCoord Gauge, f c) =
        ∑ s : Gauge ⊕ Unit, f ((mainCoordEquiv Gauge).symm s) := by
      exact Fintype.sum_equiv (mainCoordEquiv Gauge) f
        (fun s => f ((mainCoordEquiv Gauge).symm s)) (fun c => by simp)
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp [mainCoordEquiv]

/-- The actual exponential score decomposes into its effective-prime and
fixed-dimensional nuisance parts. -/
theorem vectorScore_eq_effectivePrime_add_nuisance [Nonempty Head]
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    B.vectorFamily.scalarFamily.score m xi =
      (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.effectivePrimeCoefficient xi p *
          valuation p.1 (B.sampleData.value m)) +
      inner ℝ (B.nuisanceParameter xi) (B.nuisanceStatistic m) := by
  simp only [VectorExponentialFamily.scalarFamily, innerSL_apply_apply]
  rw [PiLp.inner_apply]
  change (∑ c : B.Coord, xi c * B.statistic m c) = _
  rw [B.sum_coord_split]
  have hmain :
      (∑ c : MainCoord B.GaugeIndex,
        xi (match c with
          | .gauge j => MomentCoord.gauge j
          | .slow => MomentCoord.slow) *
        B.statistic m (match c with
          | .gauge j => MomentCoord.gauge j
          | .slow => MomentCoord.slow)) =
      (∑ k : B.GaugeIndex,
        xi (MomentCoord.gauge k) * B.gaugeScore k m) +
        xi MomentCoord.slow * (B.slowScore m / B.w) := by
    rw [sum_mainCoord]
    simp [rawStatistic, coordScale]
  have hnuisance :
      (∑ c : NuisanceCoord B.HeadIndex,
        xi (match c with
          | .physical => MomentCoord.physical
          | .head h => MomentCoord.head h) *
        B.statistic m (match c with
          | .physical => MomentCoord.physical
          | .head h => MomentCoord.head h)) =
      inner ℝ (B.nuisanceParameter xi) (B.nuisanceStatistic m) := by
    rw [PiLp.inner_apply]
    change _ = ∑ c : NuisanceCoord B.HeadIndex,
      B.nuisanceStatistic m c * B.nuisanceParameter xi c
    apply Finset.sum_congr rfl
    intro c hc
    cases c <;> simp [rawStatistic, coordScale] <;> ring
  calc
    (∑ c : MainCoord B.GaugeIndex,
        xi (match c with
          | .gauge j => MomentCoord.gauge j
          | .slow => MomentCoord.slow) *
        B.statistic m (match c with
          | .gauge j => MomentCoord.gauge j
          | .slow => MomentCoord.slow)) +
      ∑ c : NuisanceCoord B.HeadIndex,
        xi (match c with
          | .physical => MomentCoord.physical
          | .head h => MomentCoord.head h) *
        B.statistic m (match c with
          | .physical => MomentCoord.physical
          | .head h => MomentCoord.head h) =
        ((∑ k : B.GaugeIndex,
          xi (MomentCoord.gauge k) * B.gaugeScore k m) +
          xi MomentCoord.slow * (B.slowScore m / B.w)) +
          inner ℝ (B.nuisanceParameter xi) (B.nuisanceStatistic m) :=
      congrArg₂ (· + ·) hmain hnuisance
    _ = _ := by rw [B.gaugeSlowScore_eq_effectivePrimeSum]

/-! ## Dimension-free pointwise bounds -/

/-- Fixed-dimensional normalized envelope for the physical/head nuisance
statistic.  It depends on the fixed head set, but not on the prime mesh. -/
def nuisanceStatisticCoefficient (C : ℝ) : ℝ :=
  Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
    max (physicalLogCoefficient C) (3 / Real.log 2)

theorem nuisanceStatisticCoefficient_nonneg {C : ℝ} (hC : 1 ≤ C) :
    0 ≤ B.nuisanceStatisticCoefficient C := by
  unfold nuisanceStatisticCoefficient
  exact mul_nonneg (Real.sqrt_nonneg _)
    (le_max_left _ _ |>.trans' (physicalLogCoefficient_nonneg hC))

theorem abs_nuisanceStatistic_apply_le [Nonempty Head]
    {C : ℝ} (hC : 1 ≤ C)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (m : B.sampleData.Sample) (c : NuisanceCoord B.HeadIndex) :
    |B.nuisanceStatistic m c| ≤
      max (physicalLogCoefficient C) (3 / Real.log 2) * B.L := by
  cases c with
  | physical =>
      exact (abs_physicalScore_le B hC hhi m).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) B.L_pos.le)
  | head h =>
      exact (abs_centeredHeadScore_le_three B h m).trans
        ((three_le_headCoefficient_mul_L B).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) B.L_pos.le))

/-- Euclidean norm bound for the nuisance statistic; its dimension is fixed
by the head simplex and does not grow with the prime mesh. -/
theorem nuisanceStatistic_norm_le [Nonempty Head]
    {C : ℝ} (hC : 1 ≤ C)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (m : B.sampleData.Sample) :
    ‖B.nuisanceStatistic m‖ ≤
      B.nuisanceStatisticCoefficient C * B.L := by
  let K : ℝ := max (physicalLogCoefficient C) (3 / Real.log 2)
  have hK0 : 0 ≤ K :=
    (physicalLogCoefficient_nonneg hC).trans (le_max_left _ _)
  have hKL0 : 0 ≤ K * B.L := mul_nonneg hK0 B.L_pos.le
  have hsum : ‖B.nuisanceStatistic m‖ ^ 2 ≤
      ∑ _c : NuisanceCoord B.HeadIndex, (K * B.L) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    apply Finset.sum_le_sum
    intro c hc
    simpa only [sq_abs] using
      pow_le_pow_left₀ (abs_nonneg (B.nuisanceStatistic m c))
        (by simpa only [K] using B.abs_nuisanceStatistic_apply_le hC hhi m c) 2
  have hcard0 : 0 ≤
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) := by positivity
  have hsqrt :
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)) ^ 2 =
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) :=
    Real.sq_sqrt hcard0
  have hsumEq :
      (∑ _c : NuisanceCoord B.HeadIndex, (K * B.L) ^ 2) =
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (K * B.L) ^ 2 := by simp
  have htargetSq :
      (B.nuisanceStatisticCoefficient C * B.L) ^ 2 =
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (K * B.L) ^ 2 := by
    unfold nuisanceStatisticCoefficient
    dsimp only [K]
    rw [mul_assoc]
    nlinarith
  have htarget0 : 0 ≤ B.nuisanceStatisticCoefficient C * B.L :=
    mul_nonneg (B.nuisanceStatisticCoefficient_nonneg hC) B.L_pos.le
  rw [hsumEq] at hsum
  have hsq : ‖B.nuisanceStatistic m‖ ^ 2 ≤
      (B.nuisanceStatisticCoefficient C * B.L) ^ 2 := by
    rw [htargetSq]
    exact hsum
  nlinarith [norm_nonneg (B.nuisanceStatistic m)]

/-- The prime part of the literal score is controlled by the largest
effective fugacity times the actual total band valuation. -/
theorem abs_effectivePrimeSum_le
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    |∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.effectivePrimeCoefficient xi p *
          valuation p.1 (B.sampleData.value m)| ≤
      ‖fun p => B.effectivePrimeCoefficient xi p‖ *
        (∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
          valuation p (B.sampleData.value m)) := by
  calc
    |∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.effectivePrimeCoefficient xi p *
          valuation p.1 (B.sampleData.value m)| ≤
      ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        |B.effectivePrimeCoefficient xi p *
          valuation p.1 (B.sampleData.value m)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        ‖fun q => B.effectivePrimeCoefficient xi q‖ *
          valuation p.1 (B.sampleData.value m) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [abs_mul, abs_of_nonneg (valuation_nonneg p.1 _)]
      exact mul_le_mul_of_nonneg_right
        (by
          simpa only [Real.norm_eq_abs] using
            (norm_le_pi_norm
              (fun q : BandPrime B.sampleData.n B.sampleData.W =>
                B.effectivePrimeCoefficient xi q) p))
        (valuation_nonneg p.1 _)
    _ = ‖fun q => B.effectivePrimeCoefficient xi q‖ *
        (∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
          valuation p (B.sampleData.value m)) := by
      rw [← Finset.mul_sum]
      congr 1
      simpa only [Finset.univ_eq_attach] using
        (Finset.sum_attach
          (primeBand B.sampleData.n B.sampleData.W)
          (fun p ↦ valuation p (B.sampleData.value m)))

/-- The actual score is bounded in the effective paper norm with no loss
depending on the number of prime bands. -/
theorem abs_vectorScore_div_L_le_paperEffectiveSize [Nonempty Head]
    {C : ℝ} (hC : 1 ≤ C) (hW : 1 < B.sampleData.W)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    |B.vectorFamily.scalarFamily.score m xi / B.L| ≤
      (valuationLogCoefficient C B.sampleData.W +
        B.nuisanceStatisticCoefficient C) * B.paperEffectiveSize xi := by
  let E : ℝ := ‖fun p => B.effectivePrimeCoefficient xi p‖
  let Z : ℝ := ‖B.nuisanceParameter xi‖
  let Kp : ℝ := valuationLogCoefficient C B.sampleData.W
  let Kz : ℝ := B.nuisanceStatisticCoefficient C
  have hE0 : 0 ≤ E := norm_nonneg _
  have hZ0 : 0 ≤ Z := norm_nonneg _
  have hKp0 : 0 ≤ Kp := valuationLogCoefficient_nonneg hC hW
  have hKz0 : 0 ≤ Kz := B.nuisanceStatisticCoefficient_nonneg hC
  have hprime :
      |∑ p : BandPrime B.sampleData.n B.sampleData.W,
          B.effectivePrimeCoefficient xi p *
            valuation p.1 (B.sampleData.value m)| ≤ E * Kp * B.L := by
    calc
      |∑ p : BandPrime B.sampleData.n B.sampleData.W,
          B.effectivePrimeCoefficient xi p *
            valuation p.1 (B.sampleData.value m)| ≤
          ‖fun p => B.effectivePrimeCoefficient xi p‖ *
            (∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
              valuation p (B.sampleData.value m)) :=
        B.abs_effectivePrimeSum_le xi m
      _ ≤ E * (Kp * B.L) := by
        simpa only [E, Kp] using
          (mul_le_mul_of_nonneg_left
            (totalBandValuation_le B hC hW hhi m) hE0)
      _ = E * Kp * B.L := by ring
  have hnuisance :
      |inner ℝ (B.nuisanceParameter xi) (B.nuisanceStatistic m)| ≤
        Z * Kz * B.L := by
    calc
      |inner ℝ (B.nuisanceParameter xi) (B.nuisanceStatistic m)| ≤
          ‖B.nuisanceParameter xi‖ * ‖B.nuisanceStatistic m‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ Z * (Kz * B.L) :=
        mul_le_mul_of_nonneg_left
          (B.nuisanceStatistic_norm_le hC hhi m) hZ0
      _ = Z * Kz * B.L := by ring
  have hscore :
      |B.vectorFamily.scalarFamily.score m xi| ≤
        (Kp + Kz) * B.paperEffectiveSize xi * B.L := by
    rw [B.vectorScore_eq_effectivePrime_add_nuisance xi m]
    calc
      |_ + _| ≤ |_| + |_| := abs_add_le _ _
      _ ≤ E * Kp * B.L + Z * Kz * B.L := add_le_add hprime hnuisance
      _ ≤ (Kp + Kz) * B.paperEffectiveSize xi * B.L := by
        have hEle : E ≤ B.paperEffectiveSize xi := by
          unfold E paperEffectiveSize
          linarith [norm_nonneg (B.nuisanceParameter xi),
            abs_nonneg (xi MomentCoord.slow)]
        have hZle : Z ≤ B.paperEffectiveSize xi := by
          unfold Z paperEffectiveSize
          linarith [norm_nonneg
            (fun p => B.effectivePrimeCoefficient xi p),
            abs_nonneg (xi MomentCoord.slow)]
        have hL0 := B.L_pos.le
        have hcoeff : E * Kp + Z * Kz ≤
            B.paperEffectiveSize xi * (Kp + Kz) := by
          calc
            E * Kp + Z * Kz ≤
                B.paperEffectiveSize xi * Kp +
                  B.paperEffectiveSize xi * Kz :=
              add_le_add
                (mul_le_mul_of_nonneg_right hEle hKp0)
                (mul_le_mul_of_nonneg_right hZle hKz0)
            _ = B.paperEffectiveSize xi * (Kp + Kz) := by ring
        calc
          E * Kp * B.L + Z * Kz * B.L =
              (E * Kp + Z * Kz) * B.L := by ring
          _ ≤ (B.paperEffectiveSize xi * (Kp + Kz)) * B.L :=
            mul_le_mul_of_nonneg_right hcoeff hL0
          _ = (Kp + Kz) * B.paperEffectiveSize xi * B.L := by ring
  rw [abs_div, abs_of_pos B.L_pos]
  apply (div_le_iff₀ B.L_pos).2
  simpa only [Kp, Kz, E, Z, mul_assoc] using hscore

/-- Effective-ball form consumed by the feasibility and baseline-slack
layers of Proposition 8.7. -/
theorem effectiveScoreBound_of_paperEffectiveSize [Nonempty Head]
    {C a : ℝ} (hC : 1 ≤ C) (hW : 1 < B.sampleData.W)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (xi : B.ParamSpace) (hxi : B.paperEffectiveSize xi ≤ a) :
    ∀ m : B.sampleData.Sample,
      |B.vectorFamily.scalarFamily.score m xi / B.L| ≤
        (valuationLogCoefficient C B.sampleData.W +
          B.nuisanceStatisticCoefficient C) * a := by
  intro m
  exact (B.abs_vectorScore_div_L_le_paperEffectiveSize hC hW hhi xi m).trans
    (mul_le_mul_of_nonneg_left hxi
      (add_nonneg (valuationLogCoefficient_nonneg hC hW)
        (B.nuisanceStatisticCoefficient_nonneg hC)))



end

end BridgeData
end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PrimeBandQuadrature -/
section


/-!
# Audited harmonic prime quadrature on moving positive cells

The continuum transfer in Lemma 8.4 uses prime cells whose endpoints are
powers of the smoothness scale.  This file starts the required arithmetic
quadrature from the actual Chebyshev function.  The key identity below has no
Mertens constant: it subtracts Abel summation at two endpoints and isolates
the quantitative PNT remainder exactly.
-/

open scoped BigOperators
open Set
open Filter Topology Asymptotics

noncomputable section

namespace Erdos390.Full.PrimeBandQuadrature

open MeasureTheory
open Erdos390.Full.PrimeSums
open Erdos390.Full.FriableAsymptotic

/-- The main primitive in Abel summation for the prime harmonic sum. -/
def mertensMainPrimitive (x : ℝ) : ℝ :=
  Real.log (Real.log x) - (Real.log x)⁻¹

/-- The corresponding main integrand. -/
def mertensMainKernel (x : ℝ) : ℝ :=
  (Real.log x + 1) / (x * Real.log x ^ 2)

/-- The PNT error occurring after Abel summation. -/
def thetaError (x : ℝ) : ℝ :=
  Chebyshev.theta x - x

/-- The exact error integrand for harmonic prime quadrature. -/
def mertensErrorKernel (x : ℝ) : ℝ :=
  thetaError x * (Real.log x + 1) /
    (x ^ 2 * Real.log x ^ 2)

lemma hasDerivAt_mertensMainPrimitive {x : ℝ} (hx : 1 < x) :
    HasDerivAt mertensMainPrimitive (mertensMainKernel x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlogpos : 0 < Real.log x := Real.log_pos hx
  have hlog0 : Real.log x ≠ 0 := ne_of_gt hlogpos
  have hloglog := (Real.hasDerivAt_log hx0).log hlog0
  have hinv := (Real.hasDerivAt_log hx0).inv hlog0
  have hsub := hloglog.sub hinv
  convert hsub using 1
  unfold mertensMainKernel
  field_simp [hx0, hlog0]
  ring

lemma continuousOn_mertensMainKernel {A Y : ℝ} (hA : 1 < A) :
    ContinuousOn mertensMainKernel (Icc A Y) := by
  intro x hx
  have hx1 : 1 < x := hA.trans_le hx.1
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx1)
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  unfold mertensMainKernel
  exact (((Real.continuousAt_log hx0).add continuousAt_const).div
    (continuousAt_id.mul ((Real.continuousAt_log hx0).pow 2))
    (mul_ne_zero hx0 (pow_ne_zero 2 hlog0))).continuousWithinAt

/-- Exact integral of the Mertens main kernel. -/
lemma integral_mertensMainKernel {A Y : ℝ} (hA : 2 ≤ A) (hAY : A ≤ Y) :
    (∫ x in A..Y, mertensMainKernel x) =
      mertensMainPrimitive Y - mertensMainPrimitive A := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hAY] at hx
    exact hasDerivAt_mertensMainPrimitive (by linarith [hx.1, hA])
  · exact (continuousOn_mertensMainKernel (by linarith [hA]))
      |>.intervalIntegrable_of_Icc hAY

 def mertensAbelKernel (x : ℝ) : ℝ :=
  Chebyshev.theta x * (Real.log x + 1) /
    (x ^ 2 * Real.log x ^ 2)

 lemma mertensAbelKernel_eq_main_add_error {x : ℝ} (hx : 1 < x) :
    mertensAbelKernel x =
      mertensMainKernel x + mertensErrorKernel x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  unfold mertensAbelKernel mertensMainKernel mertensErrorKernel thetaError
  field_simp [hx0, hlog0]
  ring

 lemma intervalIntegrable_mertensAbelKernel {A Y : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    IntervalIntegrable mertensAbelKernel volume A Y := by
  have h2Y : (2 : ℝ) ≤ Y := hA.trans hAY
  have hfull :=
    Erdos390.Full.PrimeSums.intervalIntegrable_mertensIntegrand h2Y
  apply hfull.mono_set
  rw [uIcc_of_le hAY, uIcc_of_le h2Y]
  intro x hx
  exact ⟨hA.trans hx.1, hx.2⟩

 lemma integral_mertensAbelKernel_sub {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    (∫ x in (2 : ℝ)..Y, mertensAbelKernel x) -
        (∫ x in (2 : ℝ)..A, mertensAbelKernel x) =
      ∫ x in (A : ℝ)..Y, mertensAbelKernel x := by
  have h2A : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hleft : IntervalIntegrable mertensAbelKernel volume 2 (A : ℝ) := by
    simpa only [mertensAbelKernel] using
      (Erdos390.Full.PrimeSums.intervalIntegrable_mertensIntegrand h2A)
  have hright : IntervalIntegrable mertensAbelKernel volume (A : ℝ) (Y : ℝ) :=
    intervalIntegrable_mertensAbelKernel h2A hAYR
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  linarith

 lemma intervalIntegrable_mertensErrorKernel {A Y : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    IntervalIntegrable mertensErrorKernel volume A Y := by
  have habel := intervalIntegrable_mertensAbelKernel hA hAY
  have hmain : IntervalIntegrable mertensMainKernel volume A Y :=
    ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hAY
      (continuousOn_mertensMainKernel (A := A) (Y := Y)
        (by linarith [hA]))
  have hsub := habel.sub hmain
  apply hsub.congr
  intro x hx
  change mertensAbelKernel x - mertensMainKernel x =
    mertensErrorKernel x
  rw [mertensAbelKernel_eq_main_add_error (by
    rw [uIoc_of_le hAY] at hx
    linarith [hx.1, hA])]
  ring

/-- Exact two-endpoint harmonic-prime identity.  All nonconstant arithmetic
content is isolated in thetaError; in particular no Mertens constant is
introduced or assumed. -/
theorem fullReciprocalSum_interval_error_identity {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    fullReciprocalSum Y - fullReciprocalSum A -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ))) =
      thetaError (Y : ℝ) /
          ((Y : ℝ) * Real.log (Y : ℝ)) -
      thetaError (A : ℝ) /
          ((A : ℝ) * Real.log (A : ℝ)) +
      ∫ x in (A : ℝ)..Y, mertensErrorKernel x := by
  have hY : 2 ≤ Y := hA.trans hAY
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hmain := integral_mertensMainKernel hAR hAYR
  have herrInt := intervalIntegrable_mertensErrorKernel hAR hAYR
  have hmainInt : IntervalIntegrable mertensMainKernel volume (A : ℝ) (Y : ℝ) :=
    ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hAYR
      (continuousOn_mertensMainKernel
        (A := (A : ℝ)) (Y := (Y : ℝ)) (by linarith [hAR]))
  have hsplit :
      (∫ x in (A : ℝ)..Y, mertensAbelKernel x) =
        (∫ x in (A : ℝ)..Y, mertensMainKernel x) +
          ∫ x in (A : ℝ)..Y, mertensErrorKernel x := by
    rw [← intervalIntegral.integral_add hmainInt herrInt]
    apply intervalIntegral.integral_congr
    intro x hx
    exact mertensAbelKernel_eq_main_add_error (by
      rw [uIcc_of_le hAYR] at hx
      linarith [hx.1, hAR])
  rw [Erdos390.Full.PrimeSums.fullReciprocalSum_eq Y hY,
    Erdos390.Full.PrimeSums.fullReciprocalSum_eq A hA]
  have habelSub := integral_mertensAbelKernel_sub hA hAY
  calc
    (Chebyshev.theta (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) +
          (∫ x in (2 : ℝ)..Y, mertensAbelKernel x)) -
        (Chebyshev.theta (A : ℝ) / ((A : ℝ) * Real.log (A : ℝ)) +
          ∫ x in (2 : ℝ)..A, mertensAbelKernel x) -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ))) =
      Chebyshev.theta (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) -
        Chebyshev.theta (A : ℝ) / ((A : ℝ) * Real.log (A : ℝ)) +
        ((∫ x in (2 : ℝ)..Y, mertensAbelKernel x) -
          ∫ x in (2 : ℝ)..A, mertensAbelKernel x) -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ))) := by ring
    _ = Chebyshev.theta (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) -
        Chebyshev.theta (A : ℝ) / ((A : ℝ) * Real.log (A : ℝ)) +
        (∫ x in (A : ℝ)..Y, mertensMainKernel x) +
        (∫ x in (A : ℝ)..Y, mertensErrorKernel x) -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ))) := by
      rw [habelSub, hsplit]
      ring
    _ = _ := by
      rw [hmain]
      unfold mertensMainPrimitive thetaError
      have hA0 : (A : ℝ) ≠ 0 := by positivity
      have hY0 : (Y : ℝ) ≠ 0 := by positivity
      have hlogA0 : Real.log (A : ℝ) ≠ 0 :=
        ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < A by omega)))
      have hlogY0 : Real.log (Y : ℝ) ≠ 0 :=
        ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < Y by omega)))
      field_simp [hA0, hY0, hlogA0, hlogY0]
      ring

/-! ## The first logarithmic moment -/

/-- PNT remainder in Abel summation for `sum (log p)/p`. -/
def logReciprocalErrorKernel (x : ℝ) : ℝ :=
  thetaError x / x ^ 2

 lemma intervalIntegrable_thetaDivSq_segment {A Y : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    IntervalIntegrable (fun x : ℝ => Chebyshev.theta x / x ^ 2)
      volume A Y := by
  have h2Y : (2 : ℝ) ≤ Y := hA.trans hAY
  have hfull :=
    Erdos390.Full.PrimeSums.intervalIntegrable_theta_div_sq h2Y
  apply hfull.mono_set
  rw [uIcc_of_le hAY, uIcc_of_le h2Y]
  intro x hx
  exact ⟨hA.trans hx.1, hx.2⟩

 lemma integral_thetaDivSq_sub {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    (∫ x in (2 : ℝ)..Y, Chebyshev.theta x / x ^ 2) -
        (∫ x in (2 : ℝ)..A, Chebyshev.theta x / x ^ 2) =
      ∫ x in (A : ℝ)..Y, Chebyshev.theta x / x ^ 2 := by
  have h2A : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hleft :=
    Erdos390.Full.PrimeSums.intervalIntegrable_theta_div_sq h2A
  have hright := intervalIntegrable_thetaDivSq_segment h2A hAYR
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  linarith

 lemma intervalIntegrable_oneDiv_segment {A Y : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    IntervalIntegrable (fun x : ℝ => 1 / x) volume A Y := by
  apply ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hAY
  intro x hx
  have hx0 : x ≠ 0 := by linarith [hA, hx.1]
  exact (continuousAt_const.div continuousAt_id hx0).continuousWithinAt

 lemma intervalIntegrable_logReciprocalErrorKernel {A Y : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    IntervalIntegrable logReciprocalErrorKernel volume A Y := by
  have htheta := intervalIntegrable_thetaDivSq_segment hA hAY
  have hmain := intervalIntegrable_oneDiv_segment hA hAY
  apply (htheta.sub hmain).congr
  intro x hx
  have hx0 : x ≠ 0 := by
    rw [uIoc_of_le hAY] at hx
    linarith [hA, hx.1]
  unfold logReciprocalErrorKernel thetaError
  field_simp [hx0]

 lemma integral_thetaDivSq_split {A Y : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    (∫ x in A..Y, Chebyshev.theta x / x ^ 2) =
      (∫ x in A..Y, 1 / x) +
        ∫ x in A..Y, logReciprocalErrorKernel x := by
  have hmain := intervalIntegrable_oneDiv_segment hA hAY
  have herr := intervalIntegrable_logReciprocalErrorKernel hA hAY
  rw [← intervalIntegral.integral_add hmain herr]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx0 : x ≠ 0 := by
    rw [uIcc_of_le hAY] at hx
    linarith [hA, hx.1]
  unfold logReciprocalErrorKernel thetaError
  field_simp [hx0]
  ring

/-- Exact two-endpoint identity for the first logarithmic prime moment.
It is the arithmetic source of `H_j alpha_j` in the paper. -/
theorem fullLogReciprocalSum_interval_error_identity {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    fullLogReciprocalSum Y - fullLogReciprocalSum A -
        (Real.log (Y : ℝ) - Real.log (A : ℝ)) =
      thetaError (Y : ℝ) / (Y : ℝ) -
        thetaError (A : ℝ) / (A : ℝ) +
        ∫ x in (A : ℝ)..Y, logReciprocalErrorKernel x := by
  have hY : 2 ≤ Y := hA.trans hAY
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hApos : (0 : ℝ) < A := by positivity
  have hYpos : (0 : ℝ) < Y := by
    exact_mod_cast (show 0 < Y by omega)
  rw [Erdos390.Full.PrimeSums.fullLogReciprocalSum_eq Y hY,
    Erdos390.Full.PrimeSums.fullLogReciprocalSum_eq A hA]
  have hsub := integral_thetaDivSq_sub hA hAY
  have hsplit := integral_thetaDivSq_split hAR hAYR
  have hmain : (∫ x in (A : ℝ)..Y, 1 / x) =
      Real.log (Y : ℝ) - Real.log (A : ℝ) := by
    rw [integral_one_div_of_pos hApos hYpos,
      Real.log_div (ne_of_gt hYpos) (ne_of_gt hApos)]
  calc
    (Chebyshev.theta (Y : ℝ) / (Y : ℝ) +
          ∫ x in (2 : ℝ)..Y, Chebyshev.theta x / x ^ 2) -
        (Chebyshev.theta (A : ℝ) / (A : ℝ) +
          ∫ x in (2 : ℝ)..A, Chebyshev.theta x / x ^ 2) -
        (Real.log (Y : ℝ) - Real.log (A : ℝ)) =
      Chebyshev.theta (Y : ℝ) / (Y : ℝ) -
        Chebyshev.theta (A : ℝ) / (A : ℝ) +
        ((∫ x in (2 : ℝ)..Y, Chebyshev.theta x / x ^ 2) -
          ∫ x in (2 : ℝ)..A, Chebyshev.theta x / x ^ 2) -
        (Real.log (Y : ℝ) - Real.log (A : ℝ)) := by ring
    _ = Chebyshev.theta (Y : ℝ) / (Y : ℝ) -
        Chebyshev.theta (A : ℝ) / (A : ℝ) +
        (∫ x in (A : ℝ)..Y, Chebyshev.theta x / x ^ 2) -
        (Real.log (Y : ℝ) - Real.log (A : ℝ)) := by rw [hsub]
    _ = Chebyshev.theta (Y : ℝ) / (Y : ℝ) -
        Chebyshev.theta (A : ℝ) / (A : ℝ) +
        ((∫ x in (A : ℝ)..Y, 1 / x) +
          ∫ x in (A : ℝ)..Y, logReciprocalErrorKernel x) -
        (Real.log (Y : ℝ) - Real.log (A : ℝ)) := by rw [hsplit]
    _ = thetaError (Y : ℝ) / (Y : ℝ) -
        thetaError (A : ℝ) / (A : ℝ) +
        ∫ x in (A : ℝ)..Y, logReciprocalErrorKernel x := by
      rw [hmain]
      unfold thetaError
      field_simp [ne_of_gt hApos, ne_of_gt hYpos]
      ring

/-! ## Quantitative PNT remainder -/

/-- An elementary majorant for the Abel-summed PNT error. -/
def mertensErrorMajorant (C x : ℝ) : ℝ :=
  3 * C / (x * Real.log x ^ 4)

/-- Primitive of the preceding majorant. -/
def mertensErrorPrimitive (C x : ℝ) : ℝ :=
  -C / Real.log x ^ 3

lemma hasDerivAt_mertensErrorPrimitive (C : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (mertensErrorPrimitive C)
      (mertensErrorMajorant C x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hpow := (Real.hasDerivAt_log hx0).pow 3
  have hinv := hpow.inv (pow_ne_zero 3 hlog0)
  have hmul := (hasDerivAt_const x (-C)).mul hinv
  convert hmul using 1
  unfold mertensErrorMajorant
  simp only [Pi.pow_apply]
  field_simp [hx0, hlog0]
  ring

lemma continuousOn_mertensErrorMajorant (C : ℝ) {A Y : ℝ}
    (hA : 1 < A) :
    ContinuousOn (mertensErrorMajorant C) (Icc A Y) := by
  intro x hx
  have hx1 : 1 < x := hA.trans_le hx.1
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx1)
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  unfold mertensErrorMajorant
  exact continuousAt_const.div
    (continuousAt_id.mul ((Real.continuousAt_log hx0).pow 4))
    (mul_ne_zero hx0 (pow_ne_zero 4 hlog0))
    |>.continuousWithinAt

lemma integral_mertensErrorMajorant (C : ℝ) {A Y : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    (∫ x in A..Y, mertensErrorMajorant C x) =
      mertensErrorPrimitive C Y - mertensErrorPrimitive C A := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hAY] at hx
    exact hasDerivAt_mertensErrorPrimitive C (by linarith [hx.1, hA])
  · exact ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hAY
      (continuousOn_mertensErrorMajorant C (A := A) (Y := Y)
        (by linarith [hA]))

/-- A log-power-three PNT bound gives a positive-cell Abel error bounded by
the integrable log-power-four majorant. -/
lemma abs_mertensErrorKernel_le (C : ℝ) (hC : 0 ≤ C)
    {A Y x : ℝ} (hA : 2 ≤ A) (hx : x ∈ Icc A Y)
    (hTheta : |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |mertensErrorKernel x| ≤ mertensErrorMajorant C x := by
  have hx2 : 2 ≤ x := hA.trans hx.1
  have hx0 : 0 < x := by linarith
  have hloghalf : (1 / 2 : ℝ) ≤ Real.log x := by
    have hmono : Real.log 2 ≤ Real.log x :=
      Real.log_le_log (by norm_num) hx2
    nlinarith [Real.log_two_gt_d9]
  have hlogpos : 0 < Real.log x := by linarith
  have hlog0 : Real.log x ≠ 0 := ne_of_gt hlogpos
  have hlogplus : 0 ≤ Real.log x + 1 := by linarith
  have hlogthree : Real.log x + 1 ≤ 3 * Real.log x := by linarith
  unfold mertensErrorKernel mertensErrorMajorant
  rw [abs_div, abs_mul, abs_of_nonneg hlogplus,
    abs_of_pos (mul_pos (sq_pos_of_pos hx0) (sq_pos_of_pos hlogpos))]
  calc
    |thetaError x| * (Real.log x + 1) /
        (x ^ 2 * Real.log x ^ 2) ≤
      (C * x / Real.log x ^ 3) * (3 * Real.log x) /
        (x ^ 2 * Real.log x ^ 2) := by
      gcongr
    _ = 3 * C / (x * Real.log x ^ 4) := by
      field_simp [ne_of_gt hx0, hlog0]









/-! ## Exact alignment with the paper's logarithmic coordinate -/

/-- The coordinate `t = log p / log z`, allowing the real smoothness scale
`z` rather than replacing it by its integer floor. -/
def logCoordinate (z : ℝ) (X : ℕ) : ℝ :=
  Real.log (X : ℝ) / Real.log z

lemma logCoordinate_pos {z : ℝ} {X : ℕ} (hz : 1 < z) (hX : 2 ≤ X) :
    0 < logCoordinate z X := by
  exact div_pos (Real.log_pos (by exact_mod_cast (show 1 < X by omega)))
    (Real.log_pos hz)







/-- Explicit two-endpoint quadrature error, later specialized to moving
power-scale endpoints. -/
theorem fullReciprocalSum_interval_error_bound {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) {C : ℝ} (hC : 0 ≤ C)
    (hTheta : ∀ x ∈ Icc (A : ℝ) (Y : ℝ),
      |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |fullReciprocalSum Y - fullReciprocalSum A -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)))| ≤
      5 * C / Real.log (A : ℝ) ^ 3 := by
  have hY : 2 ≤ Y := hA.trans hAY
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hApos : (0 : ℝ) < A := by positivity
  have hYpos : (0 : ℝ) < Y := by
    exact_mod_cast (show 0 < Y by omega)
  have hlogAhalf : (1 / 2 : ℝ) ≤ Real.log (A : ℝ) := by
    have hmono : Real.log 2 ≤ Real.log (A : ℝ) :=
      Real.log_le_log (by norm_num) hAR
    nlinarith [Real.log_two_gt_d9]
  have hlogApos : 0 < Real.log (A : ℝ) := by linarith
  have hlogYpos : 0 < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast
    (show 1 < Y by omega))
  have hlogAY : Real.log (A : ℝ) ≤ Real.log (Y : ℝ) :=
    Real.log_le_log hApos hAYR
  have herrInt := intervalIntegrable_mertensErrorKernel hAR hAYR
  have hmajorInt : IntervalIntegrable (mertensErrorMajorant C) volume
      (A : ℝ) (Y : ℝ) :=
    ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hAYR
      (continuousOn_mertensErrorMajorant C
        (A := (A : ℝ)) (Y := (Y : ℝ)) (by linarith [hAR]))
  have habsInt : IntervalIntegrable (fun x => |mertensErrorKernel x|)
      volume (A : ℝ) (Y : ℝ) := herrInt.abs
  have hIntBound :
      |∫ x in (A : ℝ)..Y, mertensErrorKernel x| ≤
        C / Real.log (A : ℝ) ^ 3 := by
    calc
      |∫ x in (A : ℝ)..Y, mertensErrorKernel x| ≤
          ∫ x in (A : ℝ)..Y, |mertensErrorKernel x| :=
        intervalIntegral.abs_integral_le_integral_abs hAYR
      _ ≤ ∫ x in (A : ℝ)..Y, mertensErrorMajorant C x := by
        exact intervalIntegral.integral_mono_on hAYR habsInt hmajorInt
          (fun x hx => abs_mertensErrorKernel_le C hC hAR hx (hTheta x hx))
      _ = mertensErrorPrimitive C (Y : ℝ) -
          mertensErrorPrimitive C (A : ℝ) :=
        integral_mertensErrorMajorant C hAR hAYR
      _ ≤ C / Real.log (A : ℝ) ^ 3 := by
        unfold mertensErrorPrimitive
        have hnonneg : 0 ≤ C / Real.log (Y : ℝ) ^ 3 := by positivity
        have heq :
            -C / Real.log (Y : ℝ) ^ 3 -
                (-C / Real.log (A : ℝ) ^ 3) =
              C / Real.log (A : ℝ) ^ 3 -
                C / Real.log (Y : ℝ) ^ 3 := by ring
        rw [heq]
        exact sub_le_self _ hnonneg
  rw [fullReciprocalSum_interval_error_identity hA hAY]
  have hThetaA := hTheta (A : ℝ) ⟨le_rfl, hAYR⟩
  have hThetaY := hTheta (Y : ℝ) ⟨hAYR, le_rfl⟩
  have hAterm :
      |thetaError (A : ℝ) / ((A : ℝ) * Real.log (A : ℝ))| ≤
        C / Real.log (A : ℝ) ^ 4 := by
    rw [abs_div, abs_of_pos (mul_pos hApos hlogApos)]
    calc
      _ ≤ (C * (A : ℝ) / Real.log (A : ℝ) ^ 3) /
          ((A : ℝ) * Real.log (A : ℝ)) := by gcongr
      _ = C / Real.log (A : ℝ) ^ 4 := by
        field_simp [ne_of_gt hApos, ne_of_gt hlogApos]
  have hYterm :
      |thetaError (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ))| ≤
        C / Real.log (A : ℝ) ^ 4 := by
    rw [abs_div, abs_of_pos (mul_pos hYpos hlogYpos)]
    calc
      _ ≤ (C * (Y : ℝ) / Real.log (Y : ℝ) ^ 3) /
          ((Y : ℝ) * Real.log (Y : ℝ)) := by gcongr
      _ = C / Real.log (Y : ℝ) ^ 4 := by
        field_simp [ne_of_gt hYpos, ne_of_gt hlogYpos]
      _ ≤ C / Real.log (A : ℝ) ^ 4 := by gcongr
  calc
    |thetaError (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) -
        thetaError (A : ℝ) / ((A : ℝ) * Real.log (A : ℝ)) +
        ∫ x in (A : ℝ)..Y, mertensErrorKernel x| ≤
      |thetaError (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ))| +
        |thetaError (A : ℝ) / ((A : ℝ) * Real.log (A : ℝ))| +
        |∫ x in (A : ℝ)..Y, mertensErrorKernel x| := by
          calc
            _ ≤
                |thetaError (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) -
                  thetaError (A : ℝ) / ((A : ℝ) * Real.log (A : ℝ))| +
                  |∫ x in (A : ℝ)..Y, mertensErrorKernel x| :=
              abs_add_le _ _
            _ ≤ _ := by
              have hsub := abs_sub
                (thetaError (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)))
                (thetaError (A : ℝ) / ((A : ℝ) * Real.log (A : ℝ)))
              linarith
    _ ≤ C / Real.log (A : ℝ) ^ 4 +
        C / Real.log (A : ℝ) ^ 4 +
        C / Real.log (A : ℝ) ^ 3 := by linarith
    _ ≤ 5 * C / Real.log (A : ℝ) ^ 3 := by
      have hinv4 :
          1 / Real.log (A : ℝ) ^ 4 ≤
            2 / Real.log (A : ℝ) ^ 3 := by
        have hone : 1 ≤ 2 * Real.log (A : ℝ) := by linarith
        have hpowNonneg : 0 ≤ Real.log (A : ℝ) ^ 3 :=
          pow_nonneg hlogApos.le 3
        have hmul := mul_le_mul_of_nonneg_right hone hpowNonneg
        apply (div_le_div_iff₀ (pow_pos hlogApos 4)
          (pow_pos hlogApos 3)).2
        calc
          1 * Real.log (A : ℝ) ^ 3 ≤
              (2 * Real.log (A : ℝ)) * Real.log (A : ℝ) ^ 3 := hmul
          _ = 2 * Real.log (A : ℝ) ^ 4 := by ring
      have hscaled :
          C / Real.log (A : ℝ) ^ 4 ≤
            2 * C / Real.log (A : ℝ) ^ 3 := by
        calc
          C / Real.log (A : ℝ) ^ 4 =
              C * (1 / Real.log (A : ℝ) ^ 4) := by ring
          _ ≤ C * (2 / Real.log (A : ℝ) ^ 3) :=
            mul_le_mul_of_nonneg_left hinv4 hC
          _ = 2 * C / Real.log (A : ℝ) ^ 3 := by ring
      have hscaled' :
          C / Real.log (A : ℝ) ^ 4 ≤
            2 * (C / Real.log (A : ℝ) ^ 3) := by
        calc
          C / Real.log (A : ℝ) ^ 4 ≤
              2 * C / Real.log (A : ℝ) ^ 3 := hscaled
          _ = 2 * (C / Real.log (A : ℝ) ^ 3) := by ring
      calc
        C / Real.log (A : ℝ) ^ 4 +
              C / Real.log (A : ℝ) ^ 4 +
              C / Real.log (A : ℝ) ^ 3 ≤
            2 * (C / Real.log (A : ℝ) ^ 3) +
              2 * (C / Real.log (A : ℝ) ^ 3) +
              C / Real.log (A : ℝ) ^ 3 :=
          add_le_add (add_le_add hscaled' hscaled') le_rfl
        _ = 5 * C / Real.log (A : ℝ) ^ 3 := by ring



/-- The genuine PNT supplies the log-cube hypothesis in the preceding
estimate, with one constant and one threshold valid for every later
interval. -/
theorem exists_thetaError_log_cube_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ x, X₀ ≤ x →
      |thetaError x| ≤ C * x / Real.log x ^ 3 := by
  obtain ⟨C, hC, hbound⟩ :=
    (theta_error_isBigO_log_power (3 : ℝ)).exists_pos
  rw [IsBigOWith, eventually_atTop] at hbound
  obtain ⟨X₀, hX₀⟩ := hbound
  refine ⟨C, hC, max X₀ 2, fun x hx => ?_⟩
  have hxX₀ : X₀ ≤ x := (le_max_left X₀ 2).trans hx
  have hx2 : (2 : ℝ) ≤ x := (le_max_right X₀ 2).trans hx
  have htargetR : 0 ≤ x / Real.log x ^ ((3 : ℕ) : ℝ) := by
    have hxpos : 0 < x := by linarith
    have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
    positivity
  have hb := hX₀ x hxX₀
  simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs] at hb
  calc
    |thetaError x| = |Chebyshev.theta x - x| := rfl
    _ ≤ C * |x / Real.log x ^ ((3 : ℕ) : ℝ)| := by
      exact hb
    _ = C * (x / Real.log x ^ ((3 : ℕ) : ℝ)) := by
      congr 1
      exact abs_of_nonneg htargetR
    _ = C * x / Real.log x ^ 3 := by
      rw [Real.rpow_natCast]
      ring

/-- Unconditional positive-cell harmonic-prime quadrature.  Unlike a bare
Mertens asymptotic, the same `C` and `X₀` work simultaneously for every
pair of moving endpoints beyond the threshold. -/
theorem exists_fullReciprocalSum_interval_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ A Y : ℕ,
      X₀ ≤ A → A ≤ Y →
      |fullReciprocalSum Y - fullReciprocalSum A -
          (Real.log (Real.log (Y : ℝ)) -
            Real.log (Real.log (A : ℝ)))| ≤
        5 * C / Real.log (A : ℝ) ^ 3 := by
  obtain ⟨C, hC, X₀, hTheta⟩ := exists_thetaError_log_cube_bound
  obtain ⟨N, hX₀N⟩ := exists_nat_gt X₀
  refine ⟨C, hC, max N 2, fun A Y hA hAY => ?_⟩
  have hA2 : 2 ≤ A := (le_max_right N 2).trans hA
  apply fullReciprocalSum_interval_error_bound hA2 hAY hC.le
  intro x hx
  apply hTheta x
  have hNA : N ≤ A := (le_max_left N 2).trans hA
  have hNAR : (N : ℝ) ≤ (A : ℝ) := by exact_mod_cast hNA
  linarith [hx.1]

/-- Named global witnesses for reciprocal-prime mass quadrature. -/
noncomputable def fullReciprocalSumUniformConstant : ℝ :=
  Classical.choose exists_fullReciprocalSum_interval_error_bound



noncomputable def fullReciprocalSumUniformCutoff : ℕ :=
  Classical.choose
    (Classical.choose_spec
      exists_fullReciprocalSum_interval_error_bound).2





end Erdos390.Full.PrimeBandQuadrature

end

/- Source module: Erdos390.Full.PositiveCellTransfer -/
section


/-!
# Actual positive-cell prime-band transfer

This file connects the exact arithmetic band geometry to the unconditional
two-endpoint PNT quadrature.  A certificate records that each finite band is
literally a prime interval `(A_j,Y_j]` inside the actual moving prime band.
From that elementary membership statement we derive, rather than assume,

* `H_j = sum_{A_j < p <= Y_j} 1/p`, and
* `H_j * alpha_j = (sum_{A_j < p <= Y_j} log p / p) / log y`.

The final theorems then import the uniform constants and threshold from
`PrimeBandQuadrature`; no Mertens constant or moving-cell asymptotic appears
as a structure field.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PositiveCellTransfer

open ArithmeticModel PrimeSums PrimeBandQuadrature
open ArithmeticBandGeometry

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]





/-- The concrete endpoint data certifying that every arithmetic band is one
positive prime interval inside `W < p <= floor(y)`. -/
structure IntervalCertificate (P : Partition n W Band) where
  lower : Band → ℕ
  upper : Band → ℕ
  lower_le_upper : ∀ j, lower j ≤ upper j
  cutoff_le_lower : ∀ j, W ≤ lower j
  upper_le_yNat : ∀ j, upper j ≤ yNat n
  band_eq_iff : ∀ (p : ArithmeticBandGeometry.BandPrime n W) (j : Band),
    P.band p = j ↔ lower j < p.1 ∧ p.1 ≤ upper j

namespace IntervalCertificate

variable {P : Partition n W Band} (E : IntervalCertificate P)

/-- Natural primes in the certified interval. -/
def cellPrimes (j : Band) : Finset ℕ :=
  primesUpTo (E.upper j) \ primesUpTo (E.lower j)

/-- Continuum harmonic mass of the certified endpoint interval. -/
def continuumMass (j : Band) : ℝ :=
  Real.log (Real.log (E.upper j : ℝ)) -
    Real.log (Real.log (E.lower j : ℝ))

/-- Continuum first logarithmic moment on the arithmetic scale `log y`. -/
def continuumMoment (j : Band) : ℝ :=
  (Real.log (E.upper j : ℝ) -
    Real.log (E.lower j : ℝ)) / Real.log (y n)

/-- Continuum cell center, defined as first moment divided by mass. -/
def continuumCenter (j : Band) : ℝ :=
  E.continuumMoment j / E.continuumMass j



























end IntervalCertificate

end Erdos390.Full.PositiveCellTransfer

end

/- Source module: Erdos390.Full.PrimeIntervalPartitionConstructor -/
section


/-!
# Constructing the arithmetic prime partition from ordered cutoffs

This module removes the set-theoretic part of the interval certificate.
Given a finite monotone sequence of natural cutoffs from `W` to `floor y`
and one prime in every consecutive interval, it constructs the actual
`ArithmeticBandGeometry.Partition` and proves its `IntervalCertificate`.
The remaining analytic task for a concrete mesh is therefore exactly the
prime-existence statement for its explicit cutoffs.
-/

namespace Erdos390.Full.PrimeIntervalPartitionConstructor

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PositiveCellTransfer

/-- A point strictly above the first cutoff and no larger than the last one
belongs to some consecutive interval. -/
theorem exists_fin_cell_of_endpoints
    {K p : ℕ} (hK : 0 < K) (cut : ℕ → ℕ)
    (hstart : cut 0 < p) (hend : p ≤ cut K) :
    ∃ j : Fin K, cut j.1 < p ∧ p ≤ cut (j.1 + 1) := by
  have hexists : ∃ k : ℕ, k < K ∧ p ≤ cut (k + 1) := by
    have hKone : 1 ≤ K := hK
    have heq : K - 1 + 1 = K := Nat.sub_add_cancel hKone
    refine ⟨K - 1, by omega, ?_⟩
    rw [heq]
    exact hend
  let k : ℕ := Nat.find hexists
  have hk := Nat.find_spec hexists
  refine ⟨⟨k, hk.1⟩, ?_, hk.2⟩
  by_cases hkzero : k = 0
  · simpa only [hkzero] using hstart
  · have hpred : k - 1 < k := by omega
    have hminimal := Nat.find_min hexists hpred
    by_contra hnot
    apply hminimal
    constructor
    · omega
    · have hp : p ≤ cut k := Nat.le_of_not_gt hnot
      have hkone : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hkzero
      have heq : k - 1 + 1 = k := Nat.sub_add_cancel hkone
      rw [heq]
      exact hp

/-- Consecutive cells of a monotone cutoff sequence are disjoint, so the
cell supplied above is unique. -/
theorem existsUnique_fin_cell_of_monotone_endpoints
    {K p : ℕ} (hK : 0 < K) (cut : ℕ → ℕ)
    (hcut : Monotone cut) (hstart : cut 0 < p) (hend : p ≤ cut K) :
    ∃! j : Fin K, cut j.1 < p ∧ p ≤ cut (j.1 + 1) := by
  obtain ⟨j, hj⟩ := exists_fin_cell_of_endpoints hK cut hstart hend
  refine ⟨j, hj, ?_⟩
  intro i hi
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hsucc : i.1 + 1 ≤ j.1 := by omega
    have hbetween := hcut hsucc
    exact (Nat.not_lt_of_ge (hi.2.trans hbetween)) hj.1
  · have hsucc : j.1 + 1 ≤ i.1 := by omega
    have hbetween := hcut hsucc
    exact (Nat.not_lt_of_ge (hj.2.trans hbetween)) hi.1

section Constructor

variable {n W K : ℕ} (hK : 0 < K) (cut : ℕ → ℕ)
  (hcut : Monotone cut) (hcutZero : cut 0 = W)
  (hcutLast : cut K = yNat n)

include hK cut hcut hcutZero hcutLast

 theorem prime_has_unique_cell
    (p : BandPrime n W) :
    ∃! j : Fin K, cut j.1 < p.1 ∧ p.1 ≤ cut (j.1 + 1) := by
  apply existsUnique_fin_cell_of_monotone_endpoints hK cut hcut
  · rw [hcutZero]
    exact cutoff_lt_of_mem_primeBand p.2
  · rw [hcutLast]
    exact le_yNat_of_mem_primeBand p.2

/-- The unique interval index of an actual band prime. -/
def intervalBand (p : BandPrime n W) : Fin K :=
  Classical.choose (prime_has_unique_cell hK cut hcut hcutZero hcutLast p)

theorem intervalBand_spec (p : BandPrime n W) :
    cut (intervalBand hK cut hcut hcutZero hcutLast p).1 < p.1 ∧
      p.1 ≤ cut ((intervalBand hK cut hcut hcutZero hcutLast p).1 + 1) :=
  (Classical.choose_spec
    (prime_has_unique_cell hK cut hcut hcutZero hcutLast p)).1

theorem intervalBand_eq_iff (p : BandPrime n W) (j : Fin K) :
    intervalBand hK cut hcut hcutZero hcutLast p = j ↔
      cut j.1 < p.1 ∧ p.1 ≤ cut (j.1 + 1) := by
  let H := prime_has_unique_cell hK cut hcut hcutZero hcutLast p
  constructor
  · intro h
    rw [← h]
    exact intervalBand_spec hK cut hcut hcutZero hcutLast p
  · intro hj
    have hunique := (Classical.choose_spec H).2 j hj
    exact hunique.symm

omit hK in
/-- Every cutoff is between the first and last cutoffs. -/
theorem cutoff_bounds (j : Fin K) :
    W ≤ cut j.1 ∧ cut (j.1 + 1) ≤ yNat n := by
  constructor
  · rw [← hcutZero]
    exact hcut (Nat.zero_le j.1)
  · rw [← hcutLast]
    exact hcut (Nat.succ_le_iff.mpr j.2)

/-- Construct the arithmetic partition.  The only additional input is the
genuine prime-existence statement for every consecutive cutoff interval. -/
def partition
    (hprime : ∀ j : Fin K, ∃ p : ℕ,
      p.Prime ∧ cut j.1 < p ∧ p ≤ cut (j.1 + 1)) :
    ArithmeticBandGeometry.Partition n W (Fin K) where
  band := intervalBand hK cut hcut hcutZero hcutLast
  fiber_nonempty := by
    intro j
    obtain ⟨p, hpPrime, hpLower, hpUpper⟩ := hprime j
    have hb := cutoff_bounds cut hcut hcutZero hcutLast j
    have hpBand : p ∈ primeBand n W := mem_primeBand.mpr
      ⟨hpPrime, hb.1.trans_lt hpLower, hpUpper.trans hb.2⟩
    let q : BandPrime n W := ⟨p, hpBand⟩
    refine ⟨q, ?_⟩
    exact (intervalBand_eq_iff hK cut hcut hcutZero hcutLast q j).2
      ⟨hpLower, hpUpper⟩

/-- The interval certificate of the constructed partition is a theorem, not
an independent input. -/
def intervalCertificate
    (hprime : ∀ j : Fin K, ∃ p : ℕ,
      p.Prime ∧ cut j.1 < p ∧ p ≤ cut (j.1 + 1)) :
    IntervalCertificate
      (partition hK cut hcut hcutZero hcutLast hprime) where
  lower := fun j ↦ cut j.1
  upper := fun j ↦ cut (j.1 + 1)
  lower_le_upper := fun j ↦ hcut (Nat.le_succ j.1)
  cutoff_le_lower := fun j ↦
    (cutoff_bounds cut hcut hcutZero hcutLast j).1
  upper_le_yNat := fun j ↦
    (cutoff_bounds cut hcut hcutZero hcutLast j).2
  band_eq_iff := by
    intro p j
    exact intervalBand_eq_iff hK cut hcut hcutZero hcutLast p j

end Constructor

end

end Erdos390.Full.PrimeIntervalPartitionConstructor

end

/- Source module: Erdos390.Full.RegularMeshPrimeCutoffs -/
section


/-!
# Explicit natural prime cutoffs from the regular relative mesh

The continuum endpoints are converted to natural endpoints by
`floor (exp(t log y))`.  This file proves monotonicity, identifies the last
cutoff with the paper's `floor y`, and uses Bertrand's postulate to populate
every cell once the explicit scale-separation inequalities hold.
-/

open Filter

namespace Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

open ArithmeticModel RegularRelativeMesh
open PrimeIntervalPartitionConstructor PositiveCellTransfer

/-- The positive number whose logarithmic coordinate is `t`. -/
def scalePoint (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (t * Real.log (y n))

/-- Natural cutoffs for one low cell followed by the positive geometric
cells. -/
def fullCutoff {delta eta : ℝ} (M : Mesh delta eta)
    (n W : ℕ) : ℕ → ℕ
  | 0 => W
  | k + 1 => ⌊M.endpoint k |> scalePoint n⌋₊

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

theorem endpoint_mono (hdelta : 0 < delta) : Monotone M.endpoint := by
  intro a b hab
  unfold RegularRelativeMesh.Mesh.endpoint
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by linarith [M.ratio_pos]) hab) hdelta.le

theorem fullCutoff_zero (n W : ℕ) :
    fullCutoff M n W 0 = W := rfl

theorem fullCutoff_succ (n W k : ℕ) :
    fullCutoff M n W (k + 1) = ⌊scalePoint n (M.endpoint k)⌋₊ := rfl

/-- The final explicit cutoff is exactly `floor y`. -/
theorem fullCutoff_last {n W : ℕ} (hn : 0 < n) :
    fullCutoff M n W (M.cellCount + 1) = yNat n := by
  rw [fullCutoff_succ M, M.endpoint_cellCount]
  unfold scalePoint yNat
  simp only [one_mul, Real.exp_log (Scale.y_pos hn)]

/-- Monotonicity of all explicit cutoffs, including the junction from the
fixed cutoff `W` to the moving low-cell endpoint. -/
theorem fullCutoff_monotone
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≤ fullCutoff M n W 1) :
    Monotone (fullCutoff M n W) := by
  have hylog : 0 ≤ Real.log (y n) := by
    have hyOne : 1 < y n := by
      have hlog : 0 < Real.log (y n) := by
        rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
        exact mul_pos (by norm_num)
          (Real.log_pos (by exact_mod_cast hn))
      exact (Real.log_pos_iff (Scale.y_pos
        (Nat.zero_lt_of_lt hn)).le).mp hlog
    exact (Real.log_pos hyOne).le
  intro a b hab
  cases a with
  | zero =>
      cases b with
      | zero => exact le_rfl
      | succ b =>
          calc
            fullCutoff M n W 0 ≤ fullCutoff M n W 1 := hW
            _ ≤ fullCutoff M n W (b + 1) := by
              rw [fullCutoff_succ M, fullCutoff_succ M]
              apply Nat.floor_mono
              unfold scalePoint
              rw [Real.exp_le_exp]
              exact mul_le_mul_of_nonneg_right
                (endpoint_mono M hdelta (Nat.zero_le b)) hylog
  | succ a =>
      cases b with
      | zero => omega
      | succ b =>
          have hab' : a ≤ b := by omega
          rw [fullCutoff_succ M, fullCutoff_succ M]
          apply Nat.floor_mono
          unfold scalePoint
          rw [Real.exp_le_exp]
          exact mul_le_mul_of_nonneg_right
            (endpoint_mono M hdelta hab') hylog

end Mesh

/-- Bertrand's postulate populates a floored interval whenever the upper
real endpoint is at least twice the lower one. -/
theorem exists_prime_between_floors
    {x z : ℝ} (hx : 1 ≤ x) (hdouble : 2 * x ≤ z) :
    ∃ p : ℕ, p.Prime ∧ ⌊x⌋₊ < p ∧ p ≤ ⌊z⌋₊ := by
  have hfloorOne : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by
    exact_mod_cast hx)
  obtain ⟨p, hpPrime, hpLower, hpUpper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul ⌊x⌋₊ (by omega)
  refine ⟨p, hpPrime, hpLower, hpUpper.trans ?_⟩
  apply Nat.le_floor
  have hfloorLe : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by positivity)
  calc
    ((2 * ⌊x⌋₊ : ℕ) : ℝ) = 2 * (⌊x⌋₊ : ℝ) := by norm_num
    _ ≤ 2 * x := mul_le_mul_of_nonneg_left hfloorLe (by norm_num)
    _ ≤ z := hdouble

/-- Explicit scale conditions under which all natural mesh cells contain a
prime.  These inequalities are proved eventually below; they are displayed
here to keep the finite Bertrand step transparent. -/
structure ScaleSeparation {delta eta : ℝ} (M : Mesh delta eta)
    (n W : ℕ) : Prop where
  low : (2 * W : ℝ) ≤ scalePoint n delta
  positive : ∀ k : Fin M.cellCount,
    1 ≤ scalePoint n (M.lower k) ∧
      2 * scalePoint n (M.lower k) ≤ scalePoint n (M.upper k)

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- Every consecutive explicit cutoff interval contains a genuine prime. -/
theorem every_fullCutoff_cell_has_prime
    {n W : ℕ} (hW : W ≠ 0)
    (S : ScaleSeparation M n W) :
    ∀ j : Fin (M.cellCount + 1), ∃ p : ℕ,
      p.Prime ∧ fullCutoff M n W j.1 < p ∧
        p ≤ fullCutoff M n W (j.1 + 1) := by
  intro j
  by_cases hj : j.1 = 0
  · have hfloor : (2 * W : ℕ) ≤ ⌊scalePoint n delta⌋₊ := by
      apply Nat.le_floor
      exact_mod_cast S.low
    obtain ⟨p, hpPrime, hpLower, hpUpper⟩ :=
      Nat.exists_prime_lt_and_le_two_mul W hW
    refine ⟨p, hpPrime, ?_, ?_⟩
    · simpa only [hj, fullCutoff_zero M] using hpLower
    · have hp := hpUpper.trans hfloor
      have hendpoint : M.endpoint 0 = delta := M.endpoint_zero
      simpa only [hj, Nat.zero_add, fullCutoff_succ M, hendpoint] using hp
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj
    have hklt : k < M.cellCount := by omega
    let q : Fin M.cellCount := ⟨k, hklt⟩
    obtain ⟨p, hpPrime, hpLower, hpUpper⟩ :=
      exists_prime_between_floors (S.positive q).1 (S.positive q).2
    refine ⟨p, hpPrime, ?_, ?_⟩
    · simpa only [hk, fullCutoff_succ M,
        RegularRelativeMesh.Mesh.lower] using hpLower
    · have hsucc : j.1 + 1 = k + 1 + 1 := by omega
      rw [hsucc, fullCutoff_succ M]
      simpa only [RegularRelativeMesh.Mesh.upper] using hpUpper



end Mesh

end

end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.ConditionedPoisson -/
section


/-!
# Finite scale-invariant Poisson configurations and the conditioned bridge

This file starts the probability-theoretic construction used in the
Poisson--Dickman part of the paper.  The construction is deliberately made
from elementary probability measures rather than assuming the existence of a
Poisson point process or a Palm formula.

For a cutoff `eps`, logarithmic coordinates identify `(eps,1]`, equipped with
`dt/t`, with an interval of length `-log eps`.  We sample a Poisson number of
independent uniform logarithmic coordinates and map them back by the
exponential.  An infinite iid coordinate sequence is used only as a convenient
ambient sample space; the active configuration consists of its first `N`
coordinates and is finite.

The exact layer completed below comprises:

* the finite-cutoff probability law and its normalization;
* its Poisson count and iid coordinate marginals;
* the Poisson size-bias recurrence and the resulting Janossy
  Campbell--Mecke identity;
* a cofinal shell construction whose finite restrictions are literally
  projectively compatible as the cutoff decreases to zero.

What is not yet claimed here is the paper's canonical conditional law at an
exact total mass `u`.  Reaching that statement still requires formalizing the
continuous density of the infinite small-atom mass (the Dickman density), its
convolution identity, and the density-weighted consistency calculation.  In
particular, no regular conditional law, Palm identity, covariance formula, or
kernel conclusion is postulated as a hypothesis in this file.
-/

open Filter Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace Erdos390.Full.ConditionedPoisson

open MeasureTheory ProbabilityTheory Real

/-- A genuine cutoff strictly between zero and one. -/
structure Cutoff where
  eps : ℝ
  eps_pos : 0 < eps
  eps_lt_one : eps < 1

/-- Length of the cutoff interval in logarithmic coordinates. -/
def Cutoff.logLength (c : Cutoff) : ℝ := -log c.eps

lemma Cutoff.logLength_pos (c : Cutoff) : 0 < c.logLength := by
  rw [Cutoff.logLength, neg_pos]
  exact log_neg c.eps_pos c.eps_lt_one

/-- The Poisson rate corresponding to the intensity `dt/t` on `(eps,1]`. -/
def Cutoff.rate (c : Cutoff) : ℝ≥0 :=
  ⟨c.logLength, c.logLength_pos.le⟩

@[simp] lemma Cutoff.rate_toReal (c : Cutoff) : c.rate.toReal = c.logLength := rfl

/-- Uniform probability measure on `(0,1]`.  Endpoints are immaterial, but
`Ioc` is convenient for exact volume normalization. -/
def unitLaw : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)





/-- An iid supply of uniform logarithmic coordinates. -/
def coordinateLaw : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => unitLaw)



/-- Ambient sample: a Poisson count and an independent iid sequence. -/
abbrev Sample := ℕ × (ℕ → ℝ)

/-- The elementary finite-cutoff Poisson configuration law. -/
def finiteLaw (c : Cutoff) : Measure Sample :=
  (poissonMeasure c.rate).prod coordinateLaw





/-- Map one uniform logarithmic coordinate back to `(eps,1]`. -/
def atom (c : Cutoff) (u : ℝ) : ℝ := exp (-(c.logLength * u))







/-- The active finite list of atoms.  It is a concrete configuration; the
ordering is auxiliary and is forgotten by every symmetric Janossy test. -/
def activeAtoms (c : Cutoff) (omega : Sample) : List ℝ :=
  List.ofFn fun i : Fin omega.1 => atom c (omega.2 i.val)

@[simp] lemma activeAtoms_length (c : Cutoff) (omega : Sample) :
    (activeAtoms c omega).length = omega.1 := by
  simp [activeAtoms]







/-! ## The Janossy count identity -/























/-! ## Spatial Janossy coefficients and the finite Palm formula -/



/-- Law of one atom under normalized logarithmic intensity. -/
def pointLaw (c : Cutoff) : Measure ℝ := unitLaw.map (atom c)













/-- Product law of `n` residual atoms. -/
def residualLaw (c : Cutoff) (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => pointLaw c























/-! ## A cofinal projective construction as the cutoff decreases -/

/-- One logarithmic shell has unit intensity. -/
def shellLaw : Measure Sample :=
  (poissonMeasure (1 : ℝ≥0)).prod coordinateLaw



/-- Independent configurations in all logarithmic shells. -/
abbrev GlobalSample := ℕ → Sample

def globalLaw : Measure GlobalSample :=
  Measure.infinitePi fun _ : ℕ => shellLaw







/-- Raw restriction to the first `K` shells.  Each shell still carries its
Poisson count and iid coordinate supply. -/
def rawRestriction (K : ℕ) (omega : GlobalSample) : Fin K → Sample :=
  fun k => omega k.val



def rawRestrictionLaw (K : ℕ) : Measure (Fin K → Sample) :=
  globalLaw.map (rawRestriction K)













/-- Map a coordinate in shell `k` back to the physical scale. -/
def shellAtom (k : ℕ) (u : ℝ) : ℝ := exp (-((k : ℝ) + u))





/-- Concrete finite atom list in one logarithmic shell. -/
def activeShellAtoms (k : ℕ) (omega : Sample) : List ℝ :=
  List.ofFn fun i : Fin omega.1 => shellAtom k (omega.2 i.val)

@[simp] lemma activeShellAtoms_length (k : ℕ) (omega : Sample) :
    (activeShellAtoms k omega).length = omega.1 := by
  simp [activeShellAtoms]





/-- A cofinal cutoff sequence, with shell indices `0,...,K`. -/
def cofinalCutoff (K : ℕ) : Cutoff where
  eps := exp (-((K : ℝ) + 1))
  eps_pos := exp_pos _
  eps_lt_one := by
    rw [exp_lt_one_iff]
    have hK : 0 < (K : ℝ) + 1 := by positivity
    linarith

@[simp] lemma cofinalCutoff_eps (K : ℕ) :
    (cofinalCutoff K).eps = exp (-((K : ℝ) + 1)) := rfl





/-! ## Compatible window-conditioned restrictions -/





























/-!
The family `windowRestrictionLaw u delta K` is therefore an actual compatible
projective conditioned family for every positive-width window having nonzero
probability, and the physical cutoff tends to zero by
`tendsto_cofinalCutoff_zero`.  The remaining step needed for the paper is not
hidden here: one must prove that these laws have a canonical limit as
`delta ↓ 0`, identify it with the Dickman-density bridge, and establish the
density-weighted one- and two-point Palm disintegrations.  Those statements are
not assumed in the present file.
-/

end Erdos390.Full.ConditionedPoisson

end

/- Source module: Erdos390.Full.ConditionedPoissonLimit -/
section


/-!
# Exact analytic identities for the Poisson--Dickman bridge

This file continues the explicit finite-cutoff construction in
`ConditionedPoisson`.  The first layer below isolates the identities which
are needed by the covariance operator and proves them directly from the
method-of-steps Dickman equation.  In particular, the fact that the scale
function `t` is a null direction is not postulated.

The probability-theoretic exact-total projective limit is kept separate from
these analytic identities: this prevents a choice of a regular conditional
law on a null fibre from silently entering the operator calculation.
-/

open Filter Set
open scoped Interval BigOperators ENNReal NNReal

noncomputable section

namespace Erdos390.Full.ConditionedPoissonLimit

open MeasureTheory ProbabilityTheory Real
open DickmanBasic

/-! ## A global method-of-steps Dickman function -/

/-- Later stages of the method of steps agree with every earlier stage on
the interval already constructed. -/
lemma rhoApprox_eq_of_le {m n : ℕ} (hmn : m ≤ n) {x : ℝ}
    (hx : x ≤ (m : ℝ) + 1) : rhoApprox n x = rhoApprox m x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show m + (k + 1) = (m + k) + 1 by omega,
        rhoApprox_succ_eq_prev]
      · exact ih (Nat.le_add_right m k)
      · have hmk : (m : ℝ) ≤ (m + k : ℕ) := by
          exact_mod_cast Nat.le_add_right m k
        linarith

/-- The genuine global method-of-steps solution: at `x` use the first stage
whose constructed interval has reached `x`. -/
def rhoGlobal (x : ℝ) : ℝ := rhoApprox ⌈x⌉₊ x

lemma rhoGlobal_eq_rhoApprox_of_le_nat (n : ℕ) {x : ℝ} (hx : x ≤ n) :
    rhoGlobal x = rhoApprox n x := by
  have hceil : ⌈x⌉₊ ≤ n := Nat.ceil_le.mpr hx
  unfold rhoGlobal
  symm
  apply rhoApprox_eq_of_le hceil
  have hxceil : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  linarith

lemma rhoGlobal_eq_one_of_le_one {x : ℝ} (hx : x ≤ 1) : rhoGlobal x = 1 := by
  rw [rhoGlobal_eq_rhoApprox_of_le_nat 1 (by norm_num at hx ⊢; exact hx)]
  simp [rhoApprox, hx]

@[simp] lemma rhoGlobal_zero : rhoGlobal 0 = 1 :=
  rhoGlobal_eq_one_of_le_one (by norm_num)

/-- On every bounded interval `rhoGlobal` is literally one fixed finite
approximant.  This proves global continuity without gluing by fiat. -/
lemma continuous_rhoGlobal : Continuous rhoGlobal := by
  rw [continuous_iff_continuousAt]
  intro x
  let n : ℕ := ⌈x⌉₊ + 1
  have hxn : x < (n : ℝ) := by
    have hxceil : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    dsimp [n]
    push_cast
    linarith
  have heq : rhoGlobal =ᶠ[nhds x] rhoApprox n := by
    filter_upwards [Iio_mem_nhds hxn] with z hz
    apply rhoGlobal_eq_rhoApprox_of_le_nat n
    exact hz.le
  exact (continuous_rhoApprox n).continuousAt.congr_of_eventuallyEq heq

/-- The global object agrees with the already audited finite object throughout
the range used by the covariance kernel. -/
lemma rhoGlobal_eq_rho {x : ℝ} (hx : x ≤ 5) : rhoGlobal x = rho x := by
  exact rhoGlobal_eq_rhoApprox_of_le_nat 5 hx

/-- Global delay differential equation. -/
lemma hasDerivAt_rhoGlobal {x : ℝ} (hx : 1 < x) :
    HasDerivAt rhoGlobal (-rhoGlobal (x - 1) / x) x := by
  let n : ℕ := ⌈x⌉₊
  have hxn : x ≤ (n : ℝ) := by exact Nat.le_ceil x
  have heq : rhoGlobal =ᶠ[nhds x] rhoApprox (n + 1) := by
    have hxlt : x < ((n + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    filter_upwards [Iio_mem_nhds hxlt] with z hz
    apply rhoGlobal_eq_rhoApprox_of_le_nat (n + 1)
    exact hz.le
  have hprev : rhoGlobal (x - 1) = rhoApprox n (x - 1) := by
    apply rhoGlobal_eq_rhoApprox_of_le_nat n
    linarith
  have hfinite := hasDerivAt_rhoApprox_succ n hx
  rw [hprev]
  exact hfinite.congr_of_eventuallyEq heq

lemma deriv_rhoGlobal {x : ℝ} (hx : 1 < x) :
    deriv rhoGlobal x = -rhoGlobal (x - 1) / x :=
  (hasDerivAt_rhoGlobal hx).deriv





lemma integral_rhoGlobal_zero_one :
    (∫ t in (0 : ℝ)..1, rhoGlobal t) = 1 := by
  calc
    (∫ t in (0 : ℝ)..1, rhoGlobal t) =
        ∫ _t in (0 : ℝ)..1, (1 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          apply rhoGlobal_eq_one_of_le_one
          have ht' : t ∈ Icc (0 : ℝ) 1 := by
            simpa [uIcc_of_le zero_le_one] using ht
          exact ht'.2
    _ = 1 := by simp

/-- Global positive averaging identity. -/
lemma rhoGlobal_average_eq {x : ℝ} (hx : 1 ≤ x) :
    x * rhoGlobal x = ∫ t in (x - 1)..x, rhoGlobal t := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [rhoGlobal_eq_one_of_le_one, integral_rhoGlobal_zero_one]
  · have hderiv : ∀ t ∈ Ioo (1 : ℝ) x,
        HasDerivWithinAt (fun u : ℝ => u * rhoGlobal u)
          (rhoGlobal t - rhoGlobal (t - 1)) (Ioi t) t := by
      intro t ht
      have h := (hasDerivAt_id t).mul (hasDerivAt_rhoGlobal ht.1)
      have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans ht.1)
      have heq : 1 * rhoGlobal t + t * (-rhoGlobal (t - 1) / t) =
          rhoGlobal t - rhoGlobal (t - 1) := by
        field_simp
        ring
      exact (h.congr_deriv heq).hasDerivWithinAt
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      hx.le
      ((continuous_id.mul continuous_rhoGlobal).continuousOn)
      hderiv
      ((continuous_rhoGlobal.sub
        (continuous_rhoGlobal.comp
          (continuous_id.sub continuous_const))).intervalIntegrable 1 x)
    have hshift : (∫ t in (1 : ℝ)..x, rhoGlobal (t - 1)) =
        ∫ t in (0 : ℝ)..(x - 1), rhoGlobal t := by
      convert intervalIntegral.integral_comp_sub_right
        (a := (1 : ℝ)) (b := x) rhoGlobal 1 using 1
      norm_num
    have hsub : (∫ t in (1 : ℝ)..x, rhoGlobal t - rhoGlobal (t - 1)) =
        (∫ t in (1 : ℝ)..x, rhoGlobal t) -
          ∫ t in (1 : ℝ)..x, rhoGlobal (t - 1) := by
      apply intervalIntegral.integral_sub
      · exact continuous_rhoGlobal.intervalIntegrable 1 x
      · exact (continuous_rhoGlobal.comp
          (continuous_id.sub continuous_const)).intervalIntegrable 1 x
    have hadd₁ := intervalIntegral.integral_add_adjacent_intervals
      (μ := volume)
      (continuous_rhoGlobal.intervalIntegrable (0 : ℝ) 1)
      (continuous_rhoGlobal.intervalIntegrable (1 : ℝ) x)
    have hadd₂ := intervalIntegral.integral_add_adjacent_intervals
      (μ := volume)
      (continuous_rhoGlobal.intervalIntegrable (0 : ℝ) (x - 1))
      (continuous_rhoGlobal.intervalIntegrable (x - 1) x)
    rw [hsub, hshift] at hFTC
    rw [integral_rhoGlobal_zero_one] at hadd₁
    have hrho1 : rhoGlobal (1 : ℝ) = 1 :=
      rhoGlobal_eq_one_of_le_one le_rfl
    change _ = x * rhoGlobal x - 1 * rhoGlobal 1 at hFTC
    rw [hrho1] at hFTC
    norm_num at hFTC
    linarith

 lemma rhoGlobal_pos_step {a : ℝ} (ha1 : 1 ≤ a)
    (hprev : ∀ x ∈ Icc (a - 1) a, 0 < rhoGlobal x) :
    ∀ x ∈ Icc a (a + 1), 0 < rhoGlobal x := by
  have hanti : AntitoneOn rhoGlobal (Icc a (a + 1)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a (a + 1))
      continuous_rhoGlobal.continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_rhoGlobal (by linarith [hx.1, ha1])).differentiableAt
        |>.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hshift : x - 1 ∈ Icc (a - 1) a := by
        constructor <;> linarith [hx.1, hx.2]
      have hpos := hprev (x - 1) hshift
      rw [deriv_rhoGlobal (by linarith [hx.1, ha1])]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hpos.le)
        (by linarith [hx.1, ha1])
  have hend_le (x : ℝ) (hx : x ∈ Icc a (a + 1)) :
      rhoGlobal (a + 1) ≤ rhoGlobal x :=
    hanti hx (right_mem_Icc.mpr (by linarith)) hx.2
  have hIntegralLower :
      rhoGlobal (a + 1) ≤ ∫ t in a..(a + 1), rhoGlobal t := by
    have hmono := intervalIntegral.integral_mono_on (μ := volume)
      (show a ≤ a + 1 by linarith)
      (continuous_const.intervalIntegrable a (a + 1))
      (continuous_rhoGlobal.intervalIntegrable a (a + 1))
      (fun x hx => hend_le x hx)
    simpa using hmono
  have hAverage :
      (a + 1) * rhoGlobal (a + 1) = ∫ t in a..(a + 1), rhoGlobal t := by
    have h := rhoGlobal_average_eq (x := a + 1) (by linarith)
    rw [show a + 1 - 1 = a by ring] at h
    exact h
  have hend_nonneg : 0 ≤ rhoGlobal (a + 1) := by nlinarith
  have hnonneg (x : ℝ) (hx : x ∈ Icc a (a + 1)) : 0 ≤ rhoGlobal x :=
    hend_nonneg.trans (hend_le x hx)
  have hIntegralPos : 0 < ∫ t in a..(a + 1), rhoGlobal t := by
    apply intervalIntegral.integral_pos (by linarith)
      continuous_rhoGlobal.continuousOn
    · intro x hx
      exact hnonneg x ⟨hx.1.le, hx.2⟩
    · refine ⟨a, left_mem_Icc.mpr (by linarith), ?_⟩
      exact hprev a ⟨by linarith, le_rfl⟩
  have hend_pos : 0 < rhoGlobal (a + 1) := by nlinarith
  intro x hx
  exact hend_pos.trans_le (hend_le x hx)

/-- Global strict positivity, established one unit interval at a time. -/
lemma rhoGlobal_pos {x : ℝ} (hx : 0 ≤ x) : 0 < rhoGlobal x := by
  have hnat : ∀ n : ℕ, ∀ z ∈ Icc (0 : ℝ) n, 0 < rhoGlobal z := by
    intro n
    induction n with
    | zero =>
        intro z hz
        have hzle : z ≤ 0 := by simpa using hz.2
        have hz0 : z = 0 := le_antisymm hzle hz.1
        simp [hz0]
    | succ n ih =>
        intro z hz
        by_cases hn0 : n = 0
        · subst n
          rw [rhoGlobal_eq_one_of_le_one]
          · norm_num
          · norm_num at hz ⊢
            exact hz.2
        · by_cases hzn : z ≤ (n : ℝ)
          · exact ih z ⟨hz.1, hzn⟩
          · have hn1 : (1 : ℝ) ≤ n := by
              exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0)
            have hprev : ∀ w ∈ Icc ((n : ℝ) - 1) n,
                0 < rhoGlobal w := by
              intro w hw
              exact ih w ⟨by linarith [hw.1, hn1], hw.2⟩
            have hstep := rhoGlobal_pos_step hn1 hprev
            apply hstep z
            constructor
            · exact le_of_not_ge hzn
            · norm_num [Nat.cast_add, Nat.cast_one] at hz ⊢
              exact hz.2
  let n : ℕ := ⌈x⌉₊
  apply hnat n x
  exact ⟨hx, Nat.le_ceil x⟩

/-- Beyond the constant initial interval, the global Dickman function is
strictly decreasing. -/
lemma strictAntiOn_rhoGlobal_Ici_one :
    StrictAntiOn rhoGlobal (Ici (1 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici (1 : ℝ))
    continuous_rhoGlobal.continuousOn
  intro x hx
  have hx' : 1 < x := by simpa only [interior_Ici, Set.mem_Ioi] using hx
  rw [deriv_rhoGlobal hx']
  have hnum : 0 < rhoGlobal (x - 1) := rhoGlobal_pos (sub_nonneg.mpr hx'.le)
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hnum) (zero_lt_one.trans hx')











































/-- The two-point defect appearing in the conditioned covariance kernel. -/
def covarianceKernel (s t : ℝ) : ℝ := F (s + t) - F s * F t



















/-! ## Density-weighted Palm moments and covariance -/

lemma continuous_F : Continuous F := by
  unfold F
  exact (continuous_rho.comp
    (continuous_const.sub continuous_id)).div_const (rho U)



/-! ## The removable axis singularity and a continuous kernel representative -/

/-- A globally continuous extension of `F'` obtained by projecting to the
compact interval on which the covariance kernel is evaluated. -/
def derivFExtension (x : ℝ) : ℝ :=
  deriv F (projIcc (0 : ℝ) 2 (by norm_num) x)

lemma continuous_derivFExtension : Continuous derivFExtension := by
  have hrestrict : Continuous
      (fun x : Icc (0 : ℝ) 2 => deriv F x) := (continuousOn_deriv_F).restrict
  exact hrestrict.comp continuous_projIcc

/-- Jointly continuous divided-difference extension, defined by the
fundamental-theorem-of-calculus average of the extended derivative. -/
def FdifferenceQuotient (a t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, derivFExtension (a + u * t)

lemma continuous_uncurry_FdifferenceQuotient :
    Continuous (Function.uncurry FdifferenceQuotient) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (a₀ := (0 : ℝ)) (b₀ := 1)
  exact continuous_derivFExtension.comp
    ((continuous_fst.comp continuous_fst).add
      (continuous_snd.mul (continuous_snd.comp continuous_fst)))

lemma derivFExtension_eq_deriv_of_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 2) :
    derivFExtension x = deriv F x := by
  simp [derivFExtension,
    projIcc_of_mem (show (0 : ℝ) ≤ 2 by norm_num) hx]

lemma mul_FdifferenceQuotient_eq_sub {a t : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    t * FdifferenceQuotient a t = F (a + t) - F a := by
  have hat : a ≤ a + t := le_add_of_nonneg_right ht.1
  have hpath (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      a + u * t ∈ Icc (0 : ℝ) 2 := by
    constructor
    · exact add_nonneg ha.1 (mul_nonneg hu.1 ht.1)
    · nlinarith [ha.2, ht.2, hu.2, mul_nonneg hu.1 ht.1]
  have hreplace :
      (∫ u in (0 : ℝ)..1, derivFExtension (a + u * t)) =
        ∫ u in (0 : ℝ)..1, deriv F (a + t * u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have humem : u ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hu
    change derivFExtension (a + u * t) = deriv F (a + t * u)
    rw [derivFExtension_eq_deriv_of_mem (hpath u humem)]
    congr 2
    ring
  have hsubset : Icc a (a + t) ⊆ Icc (0 : ℝ) 2 := by
    intro x hx
    constructor
    · exact ha.1.trans hx.1
    · nlinarith [hx.2, ha.2, ht.2]
  have hint : IntervalIntegrable (deriv F) volume a (a + t) :=
    (continuousOn_deriv_F.mono hsubset).intervalIntegrable_of_Icc hat
  have hdiff : ∀ x ∈ [[a, a + t]], DifferentiableAt ℝ F x := by
    intro x hx
    apply differentiableAt_F
    apply hsubset
    simpa [uIcc_of_le hat] using hx
  rw [FdifferenceQuotient, hreplace]
  change t • (∫ u in (0 : ℝ)..1, deriv F (a + t * u)) = _
  rw [intervalIntegral.smul_integral_comp_add_mul]
  simp only [mul_zero, add_zero, mul_one]
  exact intervalIntegral.integral_deriv_eq_sub hdiff hint

/-- Continuous extension of `covarianceKernel s t / t` across `t = 0`. -/
def covarianceKernelQuotient (s t : ℝ) : ℝ :=
  FdifferenceQuotient s t - F s * FdifferenceQuotient 0 t

lemma continuous_uncurry_covarianceKernelQuotient :
    Continuous (Function.uncurry covarianceKernelQuotient) := by
  exact continuous_uncurry_FdifferenceQuotient.sub
    ((continuous_F.comp continuous_fst).mul
      (continuous_uncurry_FdifferenceQuotient.comp
        (continuous_const.prodMk continuous_snd)))

lemma mul_covarianceKernelQuotient_eq_kernel {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    t * covarianceKernelQuotient s t = covarianceKernel s t := by
  have hqst := mul_FdifferenceQuotient_eq_sub hs ht
  have hq0t := mul_FdifferenceQuotient_eq_sub
    (a := (0 : ℝ)) (by norm_num) ht
  unfold covarianceKernelQuotient covarianceKernel
  calc
    t * (FdifferenceQuotient s t - F s * FdifferenceQuotient 0 t) =
        t * FdifferenceQuotient s t -
          F s * (t * FdifferenceQuotient 0 t) := by ring
    _ = (F (s + t) - F s) - F s * (F (0 + t) - F 0) := by
      rw [hqst, hq0t]
    _ = F (s + t) - F s * F t := by simp [F_zero]; ring































/-! ## The measurable Cauchy endpoint of the kernel argument -/





/-! The Palm argument produces additivity first on the positive triangle.
The following deterministic lemma records that no global Cauchy equation is
needed: continuity on the closed unit interval and local additivity already
force one common slope. -/







end Erdos390.Full.ConditionedPoissonLimit

end

/- Source module: Erdos390.Full.KernelPrimeQuadrature -/
section


/-!
# Weighted prime quadrature for the Poisson--Dickman kernel

This file generalizes the scalar Abel summation used for `H_j` to a smooth
test function on logarithmic prime coordinates.  The first layer is an exact
finite identity for the actual primes; later declarations specialize it to
the Poisson--Dickman covariance kernel and its compact derivative bounds.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.KernelPrimeQuadrature

open MeasureTheory
open ArithmeticModel PrimeSums PrimeBandQuadrature
open DickmanBasic ConditionedPoissonLimit

/-- Ordinary derivative of the covariance kernel in its second coordinate. -/
def covarianceKernelDerivativeSecond (s t : ℝ) : ℝ :=
  deriv F (s + t) - F s * deriv F t

/-- Globally continuous extension of the second-coordinate derivative. -/
def covarianceKernelDerivativeSecondExtension (s t : ℝ) : ℝ :=
  derivFExtension (s + t) - F s * derivFExtension t













/-- Logarithmic coordinate at a positive real scale. -/
def realLogCoordinate (z x : ℝ) : ℝ := Real.log x / Real.log z



/-- The Abel coefficient whose multiplication by `log p` gives
`phi(log p / log z) / p`. -/
def weightedAbelCoefficient (phi : ℝ → ℝ) (z x : ℝ) : ℝ :=
  phi (realLogCoordinate z x) / (x * Real.log x)

/-- Explicit derivative of the weighted Abel coefficient. -/
def weightedAbelCoefficientDerivative
    (phi phiPrime : ℝ → ℝ) (z x : ℝ) : ℝ :=
  phiPrime (realLogCoordinate z x) /
      (x ^ 2 * Real.log x * Real.log z) -
    phi (realLogCoordinate z x) * (Real.log x + 1) /
      (x ^ 2 * Real.log x ^ 2)

lemma hasDerivAt_weightedAbelCoefficient
    (phi phiPrime : ℝ → ℝ) {z x : ℝ}
    (hz : 1 < z) (hx : 1 < x)
    (hphi : HasDerivAt phi (phiPrime (realLogCoordinate z x))
      (realLogCoordinate z x)) :
    HasDerivAt (weightedAbelCoefficient phi z)
      (weightedAbelCoefficientDerivative phi phiPrime z x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlogx0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hlogz0 : Real.log z ≠ 0 := ne_of_gt (Real.log_pos hz)
  have hcoord : HasDerivAt (realLogCoordinate z)
      (1 / (x * Real.log z)) x := by
    have h := (Real.hasDerivAt_log hx0).div_const (Real.log z)
    convert h using 1
    field_simp [hx0, hlogz0]
  have hnum := hphi.comp x hcoord
  have hden : HasDerivAt (fun u : ℝ => u * Real.log u)
      (Real.log x + 1) x := by
    have h := (hasDerivAt_id x).mul (Real.hasDerivAt_log hx0)
    convert h using 1
    simp only [id_eq]
    field_simp [hx0]
  have hquot := hnum.div hden (mul_ne_zero hx0 hlogx0)
  convert hquot using 1
  unfold weightedAbelCoefficientDerivative
  simp only [Function.comp_apply]
  field_simp [hx0, hlogx0, hlogz0]

lemma continuousAt_weightedAbelCoefficientDerivative
    (phi phiPrime : ℝ → ℝ)
    (hphi : Continuous phi) (hphiPrime : Continuous phiPrime)
    {z x : ℝ} (hz : 1 < z) (hx : 1 < x) :
    ContinuousAt (weightedAbelCoefficientDerivative phi phiPrime z) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlogx0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hlogz0 : Real.log z ≠ 0 := ne_of_gt (Real.log_pos hz)
  have hcoord : ContinuousAt (realLogCoordinate z) x := by
    unfold realLogCoordinate
    exact (Real.continuousAt_log hx0).div_const (Real.log z)
  have hnumPrime : ContinuousAt
      (fun u : ℝ => phiPrime (realLogCoordinate z u)) x :=
    hphiPrime.continuousAt.comp hcoord
  have hnum : ContinuousAt
      (fun u : ℝ => phi (realLogCoordinate z u)) x :=
    hphi.continuousAt.comp hcoord
  have hdenPrime : ContinuousAt
      (fun u : ℝ => u ^ 2 * Real.log u * Real.log z) x :=
    ((continuousAt_id.pow 2).mul (Real.continuousAt_log hx0)).mul
      continuousAt_const
  have hdenPrime0 : x ^ 2 * Real.log x * Real.log z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hx0) hlogx0) hlogz0
  have hfactor : ContinuousAt (fun u : ℝ => Real.log u + 1) x :=
    (Real.continuousAt_log hx0).add continuousAt_const
  have hden : ContinuousAt
      (fun u : ℝ => u ^ 2 * Real.log u ^ 2) x :=
    (continuousAt_id.pow 2).mul ((Real.continuousAt_log hx0).pow 2)
  have hden0 : x ^ 2 * Real.log x ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hx0) (pow_ne_zero 2 hlogx0)
  unfold weightedAbelCoefficientDerivative
  exact (hnumPrime.div hdenPrime hdenPrime0).sub
    ((hnum.mul hfactor).div hden hden0)

/-- Actual weighted harmonic prime sum up to a natural endpoint. -/
def fullWeightedReciprocalSum (phi : ℝ → ℝ) (z : ℝ) (Y : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo Y, phi (realLogCoordinate z (p : ℝ)) / (p : ℝ)

/-- Actual Abel coefficient for one fixed first kernel coordinate. -/
def kernelWeightedAbelCoefficient (s z x : ℝ) : ℝ :=
  weightedAbelCoefficient (covarianceKernel s) z x

/-- Its continuous explicit derivative on the physical range. -/
def kernelWeightedAbelDerivative (s z x : ℝ) : ℝ :=
  weightedAbelCoefficientDerivative (covarianceKernel s)
    (covarianceKernelDerivativeSecondExtension s) z x



















/-- A continuous coefficient times the actual Chebyshev step function is
interval-integrable on every positive compact interval. -/
theorem intervalIntegrable_continuous_mul_theta
    {g : ℝ → ℝ} {A Y : ℝ} (hA : 2 ≤ A) (hAY : A ≤ Y)
    (hg : ContinuousOn g (Icc A Y)) :
    IntervalIntegrable (fun x => g x * Chebyshev.theta x) volume A Y := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hAY]
  conv =>
    arg 1
    ext x
    rw [Chebyshev.theta, Finset.sum_filter]
  refine integrableOn_mul_sum_Icc _ (by linarith [hA]) ?_
  exact hg.integrableOn_Icc





lemma continuousAt_weightedAbelCoefficient (phi : ℝ → ℝ)
    (hphi : Continuous phi) {z x : ℝ} (hz : 1 < z) (hx : 1 < x) :
    ContinuousAt (weightedAbelCoefficient phi z) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlogx0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hlogz0 : Real.log z ≠ 0 := ne_of_gt (Real.log_pos hz)
  unfold weightedAbelCoefficient realLogCoordinate
  exact (hphi.continuousAt.comp
      ((Real.continuousAt_log hx0).div_const (Real.log z))).div
    (continuousAt_id.mul (Real.continuousAt_log hx0))
    (mul_ne_zero hx0 hlogx0)

/-- Change of variables from the real prime coordinate to `t=log x/log z`.
The statement is exact and keeps the actual natural endpoints. -/
theorem integral_weightedAbelCoefficient_eq_logCoordinate
    (phi : ℝ → ℝ) (hphi : Continuous phi) {z : ℝ} (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y) :
    (∫ x in (A : ℝ)..Y, weightedAbelCoefficient phi z x) =
      ∫ t in realLogCoordinate z (A : ℝ)..realLogCoordinate z (Y : ℝ),
        phi t / t := by
  let a : ℝ := realLogCoordinate z (A : ℝ)
  let b : ℝ := realLogCoordinate z (Y : ℝ)
  let path : ℝ → ℝ := fun t => Real.exp (Real.log z * t)
  let path' : ℝ → ℝ := fun t => Real.log z * Real.exp (Real.log z * t)
  have hlogzpos : 0 < Real.log z := Real.log_pos hz
  have hApos : (0 : ℝ) < (A : ℝ) := by positivity
  have hYpos : (0 : ℝ) < (Y : ℝ) := by
    exact_mod_cast (show 0 < Y by omega)
  have hlogApos : 0 < Real.log (A : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have hlogAY : Real.log (A : ℝ) ≤ Real.log (Y : ℝ) := by
    exact Real.log_le_log hApos (by exact_mod_cast hAY)
  have hab : a ≤ b := by
    dsimp [a, b, realLogCoordinate]
    exact div_le_div_of_nonneg_right hlogAY hlogzpos.le
  have hpath (t : ℝ) : HasDerivAt path (path' t) t := by
    have hlin : HasDerivAt (fun u : ℝ => Real.log z * u)
        (Real.log z) t := by
      simpa only [id_eq, mul_one] using
        (hasDerivAt_id t).const_mul (Real.log z)
    simpa only [path, path', Function.comp_def, mul_comm] using
      (Real.hasDerivAt_exp (Real.log z * t)).comp t hlin
  have hpath' : ContinuousOn path' (uIcc a b) := by
    exact (continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn
  have hcoeff : ContinuousOn (weightedAbelCoefficient phi z)
      (path '' uIcc a b) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := hx
    have htIcc : t ∈ Icc a b := by
      simpa only [uIcc_of_le hab] using ht
    have haPos : 0 < a := by
      dsimp [a, realLogCoordinate]
      exact div_pos hlogApos hlogzpos
    have htPos : 0 < t := haPos.trans_le htIcc.1
    have hpathOne : 1 < path t := by
      dsimp [path]
      rw [Real.one_lt_exp_iff]
      exact mul_pos hlogzpos htPos
    exact (continuousAt_weightedAbelCoefficient phi hphi hz hpathOne).continuousWithinAt
  have hsubst := intervalIntegral.integral_comp_mul_deriv'
    (a := a) (b := b) (f := path) (f' := path')
    (g := weightedAbelCoefficient phi z)
    (fun t _ht => hpath t) hpath' hcoeff
  have hpathA : path a = (A : ℝ) := by
    dsimp [path, a, realLogCoordinate]
    have hlogz0 : Real.log z ≠ 0 := ne_of_gt hlogzpos
    rw [mul_div_cancel₀ _ hlogz0, Real.exp_log hApos]
  have hpathY : path b = (Y : ℝ) := by
    dsimp [path, b, realLogCoordinate]
    have hlogz0 : Real.log z ≠ 0 := ne_of_gt hlogzpos
    rw [mul_div_cancel₀ _ hlogz0, Real.exp_log hYpos]
  have hintegrand :
      (∫ t in a..b,
        (weightedAbelCoefficient phi z ∘ path) t * path' t) =
      ∫ t in a..b, phi t / t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Icc a b := by
      simpa only [uIcc_of_le hab] using ht
    have haPos : 0 < a := by
      dsimp [a, realLogCoordinate]
      exact div_pos hlogApos hlogzpos
    have ht0 : t ≠ 0 := ne_of_gt (haPos.trans_le htIcc.1)
    have hlogz0 : Real.log z ≠ 0 := ne_of_gt hlogzpos
    dsimp [Function.comp_def, weightedAbelCoefficient, realLogCoordinate,
      path, path']
    rw [Real.log_exp, mul_div_cancel_left₀ t hlogz0]
    field_simp [ht0, hlogz0, Real.exp_ne_zero]
  rw [hintegrand, hpathA, hpathY] at hsubst
  simpa only [a, b] using hsubst.symm

 noncomputable def primeLogCoefficient (k : ℕ) : ℝ :=
  if k.Prime then Real.log (k : ℝ) else 0

 theorem sum_primeLogCoefficient_Icc (x : ℝ) :
    (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, primeLogCoefficient k) =
      Chebyshev.theta x := by
  rw [Chebyshev.theta_eq_sum_Icc]
  rw [Finset.sum_filter]
  rfl

/-- Exact Abel summation for a smooth logarithmic test function.  This is a
finite identity; the PNT enters only when the `theta` term is estimated. -/
theorem fullWeightedReciprocalSum_eq_abel
    (phi : ℝ → ℝ) (z : ℝ) (Y : ℕ) (hY : 2 ≤ Y)
    (hdiff : ∀ x ∈ Icc (2 : ℝ) (Y : ℝ),
      DifferentiableAt ℝ (weightedAbelCoefficient phi z) x)
    (hint : IntegrableOn (deriv (weightedAbelCoefficient phi z))
      (Icc (2 : ℝ) (Y : ℝ))) :
    fullWeightedReciprocalSum phi z Y =
      weightedAbelCoefficient phi z (Y : ℝ) * Chebyshev.theta (Y : ℝ) -
        ∫ x in (2 : ℝ)..Y,
          deriv (weightedAbelCoefficient phi z) x * Chebyshev.theta x := by
  let c : ℕ → ℝ := primeLogCoefficient
  have hc0 : c 0 = 0 := by simp [c, primeLogCoefficient]
  have hc1 : c 1 = 0 := by simp [c, primeLogCoefficient]
  have habel := sum_mul_eq_sub_integral_mul₁
    (f := weightedAbelCoefficient phi z) c hc0 hc1 (Y : ℝ) hdiff hint
  rw [← intervalIntegral.integral_of_le (by exact_mod_cast hY)] at habel
  rw [show (⌊(Y : ℝ)⌋₊ : ℕ) = Y by simp] at habel
  have hcumY : (∑ k ∈ Finset.Icc 0 Y, c k) =
      Chebyshev.theta (Y : ℝ) := by
    simpa [c] using sum_primeLogCoefficient_Icc (Y : ℝ)
  have hcum : ∀ x : ℝ,
      (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, c k) = Chebyshev.theta x := by
    intro x
    simpa [c] using sum_primeLogCoefficient_Icc x
  rw [hcumY] at habel
  simp_rw [hcum] at habel
  have hlhs :
      (∑ k ∈ Finset.Icc 0 Y,
        weightedAbelCoefficient phi z (k : ℝ) * c k) =
          fullWeightedReciprocalSum phi z Y := by
    rw [fullWeightedReciprocalSum, primesUpTo, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hkPrime : k.Prime
    · have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hkPrime.ne_zero
      have hlogk0 : Real.log (k : ℝ) ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one
          (by exact_mod_cast hkPrime.pos) (by exact_mod_cast hkPrime.ne_one)
      simp only [c, primeLogCoefficient, hkPrime, if_true,
        weightedAbelCoefficient]
      field_simp [hk0, hlogk0]
    · simp [c, primeLogCoefficient, hkPrime]
  rw [hlhs] at habel
  linarith

/-- Exact two-endpoint Abel formula on `(A,Y]`. -/
theorem fullWeightedReciprocalSum_interval_eq_abel
    (phi : ℝ → ℝ) (z : ℝ) {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y)
    (hdiff : ∀ x ∈ Icc (2 : ℝ) (Y : ℝ),
      DifferentiableAt ℝ (weightedAbelCoefficient phi z) x)
    (hint : IntegrableOn (deriv (weightedAbelCoefficient phi z))
      (Icc (2 : ℝ) (Y : ℝ)))
    (hThetaInt : IntervalIntegrable
      (fun x : ℝ => deriv (weightedAbelCoefficient phi z) x *
        Chebyshev.theta x) volume (2 : ℝ) (Y : ℝ)) :
    fullWeightedReciprocalSum phi z Y -
        fullWeightedReciprocalSum phi z A =
      weightedAbelCoefficient phi z (Y : ℝ) * Chebyshev.theta (Y : ℝ) -
        weightedAbelCoefficient phi z (A : ℝ) * Chebyshev.theta (A : ℝ) -
        ∫ x in (A : ℝ)..Y,
          deriv (weightedAbelCoefficient phi z) x * Chebyshev.theta x := by
  have hY : 2 ≤ Y := hA.trans hAY
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have h2Y : (2 : ℝ) ≤ (Y : ℝ) := hAR.trans hAYR
  have hdiffA : ∀ x ∈ Icc (2 : ℝ) (A : ℝ),
      DifferentiableAt ℝ (weightedAbelCoefficient phi z) x := by
    intro x hx
    exact hdiff x ⟨hx.1, hx.2.trans hAYR⟩
  have hintA : IntegrableOn (deriv (weightedAbelCoefficient phi z))
      (Icc (2 : ℝ) (A : ℝ)) :=
    hint.mono_set (Icc_subset_Icc_right hAYR)
  rw [fullWeightedReciprocalSum_eq_abel phi z Y hY hdiff hint,
    fullWeightedReciprocalSum_eq_abel phi z A hA hdiffA hintA]
  have hleft : IntervalIntegrable
      (fun x : ℝ => deriv (weightedAbelCoefficient phi z) x *
        Chebyshev.theta x) volume (2 : ℝ) (A : ℝ) := by
    apply hThetaInt.mono_set
    rw [uIcc_of_le hAR, uIcc_of_le h2Y]
    intro x hx
    exact ⟨hx.1, hx.2.trans hAYR⟩
  have hright : IntervalIntegrable
      (fun x : ℝ => deriv (weightedAbelCoefficient phi z) x *
        Chebyshev.theta x) volume (A : ℝ) (Y : ℝ) := by
    apply hThetaInt.mono_set
    rw [uIcc_of_le hAYR, uIcc_of_le h2Y]
    intro x hx
    exact ⟨hAR.trans hx.1, hx.2⟩
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  linarith

/-- The continuum term obtained by replacing `theta(x)` with `x` in the
weighted Abel formula. -/
def weightedAbelMain (phi : ℝ → ℝ) (z : ℝ) (A Y : ℝ) : ℝ :=
  weightedAbelCoefficient phi z Y * Y -
    weightedAbelCoefficient phi z A * A -
      ∫ x in A..Y, deriv (weightedAbelCoefficient phi z) x * x

/-- Exact PNT remainder in the weighted Abel formula. -/
def weightedAbelRemainder (phi : ℝ → ℝ) (z : ℝ) (A Y : ℝ) : ℝ :=
  weightedAbelCoefficient phi z Y * thetaError Y -
    weightedAbelCoefficient phi z A * thetaError A -
      ∫ x in A..Y,
        deriv (weightedAbelCoefficient phi z) x * thetaError x

/-- The Abel main term is exactly the integral of the coefficient.  This is
the integration-by-parts step before changing from `x` to logarithmic prime
coordinates. -/
theorem weightedAbelMain_eq_integral_coefficient
    (phi : ℝ → ℝ) (z : ℝ) {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y)
    (hdiff : ∀ x ∈ Icc (2 : ℝ) (Y : ℝ),
      DifferentiableAt ℝ (weightedAbelCoefficient phi z) x)
    (hint : IntegrableOn (deriv (weightedAbelCoefficient phi z))
      (Icc (2 : ℝ) (Y : ℝ))) :
    weightedAbelMain phi z (A : ℝ) (Y : ℝ) =
      ∫ x in (A : ℝ)..Y, weightedAbelCoefficient phi z x := by
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hderivInt : IntervalIntegrable
      (deriv (weightedAbelCoefficient phi z)) volume (A : ℝ) (Y : ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hAYR]
    apply hint.mono_set
    exact Icc_subset_Icc hAR le_rfl
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (A : ℝ)) (b := (Y : ℝ))
    (u := id) (v := weightedAbelCoefficient phi z)
    (u' := fun _x : ℝ => 1)
    (v' := deriv (weightedAbelCoefficient phi z))
    (fun x _hx => hasDerivAt_id x)
    (fun x hx => by
      have hx' : x ∈ Icc (A : ℝ) (Y : ℝ) := by
        simpa only [uIcc_of_le hAYR] using hx
      exact (hdiff x ⟨hAR.trans hx'.1, hx'.2⟩).hasDerivAt)
    (continuous_const.intervalIntegrable _ _)
    hderivInt
  unfold weightedAbelMain
  have hone : (∫ x in (A : ℝ)..Y,
      (1 : ℝ) * weightedAbelCoefficient phi z x) =
      ∫ x in (A : ℝ)..Y, weightedAbelCoefficient phi z x := by
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  rw [hone] at hibp
  have hcomm : (∫ x in (A : ℝ)..Y,
      x * deriv (weightedAbelCoefficient phi z) x) =
      ∫ x in (A : ℝ)..Y,
        deriv (weightedAbelCoefficient phi z) x * x := by
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  simp only [id_eq] at hibp
  rw [hcomm] at hibp
  linarith

/-- The continuum Abel main term in the paper's logarithmic coordinate. -/
theorem weightedAbelMain_eq_logCoordinateIntegral
    (phi : ℝ → ℝ) (hphi : Continuous phi) {z : ℝ} (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y)
    (hdiff : ∀ x ∈ Icc (2 : ℝ) (Y : ℝ),
      DifferentiableAt ℝ (weightedAbelCoefficient phi z) x)
    (hint : IntegrableOn (deriv (weightedAbelCoefficient phi z))
      (Icc (2 : ℝ) (Y : ℝ))) :
    weightedAbelMain phi z (A : ℝ) (Y : ℝ) =
      ∫ t in realLogCoordinate z (A : ℝ)..realLogCoordinate z (Y : ℝ),
        phi t / t := by
  rw [weightedAbelMain_eq_integral_coefficient phi z hA hAY hdiff hint]
  exact integral_weightedAbelCoefficient_eq_logCoordinate phi hphi hz hA hAY

/-- Exact decomposition of the actual weighted prime sum into its continuum
Abel term and a literal PNT remainder. -/
theorem fullWeightedReciprocalSum_interval_sub_main_eq_remainder
    (phi : ℝ → ℝ) (z : ℝ) {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y)
    (hdiff : ∀ x ∈ Icc (2 : ℝ) (Y : ℝ),
      DifferentiableAt ℝ (weightedAbelCoefficient phi z) x)
    (hint : IntegrableOn (deriv (weightedAbelCoefficient phi z))
      (Icc (2 : ℝ) (Y : ℝ)))
    (hThetaInt : IntervalIntegrable
      (fun x : ℝ => deriv (weightedAbelCoefficient phi z) x *
        Chebyshev.theta x) volume (2 : ℝ) (Y : ℝ))
    (hMainInt : IntervalIntegrable
      (fun x : ℝ => deriv (weightedAbelCoefficient phi z) x * x)
      volume (A : ℝ) (Y : ℝ))
    (hErrorInt : IntervalIntegrable
      (fun x : ℝ => deriv (weightedAbelCoefficient phi z) x * thetaError x)
      volume (A : ℝ) (Y : ℝ)) :
    fullWeightedReciprocalSum phi z Y -
        fullWeightedReciprocalSum phi z A -
          weightedAbelMain phi z (A : ℝ) (Y : ℝ) =
      weightedAbelRemainder phi z (A : ℝ) (Y : ℝ) := by
  rw [fullWeightedReciprocalSum_interval_eq_abel phi z hA hAY
    hdiff hint hThetaInt]
  unfold weightedAbelMain weightedAbelRemainder thetaError
  have hsplit :
      (∫ x in (A : ℝ)..Y,
        deriv (weightedAbelCoefficient phi z) x * Chebyshev.theta x) =
      (∫ x in (A : ℝ)..Y,
        deriv (weightedAbelCoefficient phi z) x * x) +
      ∫ x in (A : ℝ)..Y,
        deriv (weightedAbelCoefficient phi z) x *
          (Chebyshev.theta x - x) := by
    have hErrorInt' : IntervalIntegrable
        (fun x : ℝ => deriv (weightedAbelCoefficient phi z) x *
          (Chebyshev.theta x - x)) volume (A : ℝ) (Y : ℝ) := by
      simpa only [thetaError] using hErrorInt
    rw [← intervalIntegral.integral_add hMainInt hErrorInt']
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  rw [hsplit]
  ring

/-- Triangle-inequality form of the exact weighted PNT remainder. -/
theorem abs_weightedAbelRemainder_le
    (phi : ℝ → ℝ) (z : ℝ) {A Y : ℝ} (hAY : A ≤ Y) :
    |weightedAbelRemainder phi z A Y| ≤
      |weightedAbelCoefficient phi z Y| * |thetaError Y| +
        |weightedAbelCoefficient phi z A| * |thetaError A| +
        ∫ x in A..Y,
          |deriv (weightedAbelCoefficient phi z) x * thetaError x| := by
  unfold weightedAbelRemainder
  calc
    |weightedAbelCoefficient phi z Y * thetaError Y -
        weightedAbelCoefficient phi z A * thetaError A -
        ∫ x in A..Y,
          deriv (weightedAbelCoefficient phi z) x * thetaError x| ≤
      |weightedAbelCoefficient phi z Y * thetaError Y| +
        |weightedAbelCoefficient phi z A * thetaError A| +
        |∫ x in A..Y,
          deriv (weightedAbelCoefficient phi z) x * thetaError x| := by
            have h₁ := abs_sub
              (weightedAbelCoefficient phi z Y * thetaError Y)
              (weightedAbelCoefficient phi z A * thetaError A)
            have h₂ := abs_sub
              (weightedAbelCoefficient phi z Y * thetaError Y -
                weightedAbelCoefficient phi z A * thetaError A)
              (∫ x in A..Y,
                deriv (weightedAbelCoefficient phi z) x * thetaError x)
            linarith
    _ ≤ |weightedAbelCoefficient phi z Y| * |thetaError Y| +
        |weightedAbelCoefficient phi z A| * |thetaError A| +
        ∫ x in A..Y,
          |deriv (weightedAbelCoefficient phi z) x * thetaError x| := by
      rw [abs_mul, abs_mul]
      exact add_le_add_right
        (intervalIntegral.abs_integral_le_integral_abs hAY) _







end Erdos390.Full.KernelPrimeQuadrature

end

/- Source module: Erdos390.Full.PrimeCoordinateSecondMoment -/
section


/-!
# Prime quadrature for the second logarithmic coordinate moment

The compensated-score geometry uses
`sum (log p / log z)^2 / p`.  This file derives its interval quadrature
directly from the genuine Chebyshev error, with a remainder uniform in the
moving upper endpoint.  It is the missing second-moment companion to the
mass and first-moment estimates in `PrimeBandQuadrature`.
-/

open Set MeasureTheory
open scoped BigOperators

namespace Erdos390.Full.PrimeCoordinateSecondMoment

open PrimeSums PrimeBandQuadrature KernelPrimeQuadrature

noncomputable section

def squareCoordinate (t : ℝ) : ℝ := t ^ 2

def squareCoordinateDerivative (t : ℝ) : ℝ := 2 * t

lemma continuous_squareCoordinate : Continuous squareCoordinate := by
  unfold squareCoordinate
  fun_prop

lemma continuous_squareCoordinateDerivative :
    Continuous squareCoordinateDerivative := by
  unfold squareCoordinateDerivative
  fun_prop

lemma hasDerivAt_squareCoordinate (t : ℝ) :
    HasDerivAt squareCoordinate (squareCoordinateDerivative t) t := by
  simpa [squareCoordinate, squareCoordinateDerivative] using
    (hasDerivAt_id t).pow 2

lemma hasDerivAt_squareWeightedAbelCoefficient
    {z x : ℝ} (hz : 1 < z) (hx : 1 < x) :
    HasDerivAt (weightedAbelCoefficient squareCoordinate z)
      (weightedAbelCoefficientDerivative squareCoordinate
        squareCoordinateDerivative z x) x := by
  exact hasDerivAt_weightedAbelCoefficient squareCoordinate
    squareCoordinateDerivative hz hx
      (hasDerivAt_squareCoordinate (realLogCoordinate z x))

lemma deriv_squareWeightedAbelCoefficient
    {z x : ℝ} (hz : 1 < z) (hx : 1 < x) :
    deriv (weightedAbelCoefficient squareCoordinate z) x =
      weightedAbelCoefficientDerivative squareCoordinate
        squareCoordinateDerivative z x :=
  (hasDerivAt_squareWeightedAbelCoefficient hz hx).deriv

lemma continuousOn_squareWeightedAbelDerivative
    {z A Y : ℝ} (hz : 1 < z) (hA : 1 < A) :
    ContinuousOn
      (weightedAbelCoefficientDerivative squareCoordinate
        squareCoordinateDerivative z) (Icc A Y) := by
  intro x hx
  exact (continuousAt_weightedAbelCoefficientDerivative
    squareCoordinate squareCoordinateDerivative
    continuous_squareCoordinate continuous_squareCoordinateDerivative
    hz (hA.trans_le hx.1)).continuousWithinAt

lemma integrableOn_deriv_squareWeightedAbelCoefficient
    {z : ℝ} (hz : 1 < z) {Y : ℕ} (hY : 2 ≤ Y) :
    IntegrableOn (deriv (weightedAbelCoefficient squareCoordinate z))
      (Icc (2 : ℝ) (Y : ℝ)) := by
  have h2Y : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hcont := continuousOn_squareWeightedAbelDerivative
    (z := z) (A := (2 : ℝ)) (Y := (Y : ℝ)) hz (by norm_num)
  apply hcont.integrableOn_Icc.congr_fun
  · intro x hx
    symm
    exact deriv_squareWeightedAbelCoefficient hz (by linarith [hx.1])
  · exact measurableSet_Icc

lemma intervalIntegrable_deriv_squareWeighted_mul_theta
    {z : ℝ} (hz : 1 < z) {Y : ℕ} (hY : 2 ≤ Y) :
    IntervalIntegrable
      (fun x : ℝ ↦
        deriv (weightedAbelCoefficient squareCoordinate z) x *
          Chebyshev.theta x) volume (2 : ℝ) (Y : ℝ) := by
  have h2Y : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hbase := intervalIntegrable_continuous_mul_theta
    (g := weightedAbelCoefficientDerivative squareCoordinate
      squareCoordinateDerivative z)
    (A := (2 : ℝ)) (Y := (Y : ℝ)) (by norm_num) h2Y
    (continuousOn_squareWeightedAbelDerivative hz (by norm_num))
  apply hbase.congr
  intro x hx
  have hx' : x ∈ Ioc (2 : ℝ) (Y : ℝ) := by
    simpa only [uIoc_of_le h2Y] using hx
  change weightedAbelCoefficientDerivative squareCoordinate
      squareCoordinateDerivative z x * Chebyshev.theta x =
    deriv (weightedAbelCoefficient squareCoordinate z) x *
      Chebyshev.theta x
  rw [deriv_squareWeightedAbelCoefficient hz (by linarith [hx'.1])]

lemma intervalIntegrable_deriv_squareWeighted_mul_id
    {z : ℝ} (hz : 1 < z) {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    IntervalIntegrable
      (fun x : ℝ ↦
        deriv (weightedAbelCoefficient squareCoordinate z) x * x)
      volume (A : ℝ) (Y : ℝ) := by
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hcont : ContinuousOn
      (fun x : ℝ ↦
        weightedAbelCoefficientDerivative squareCoordinate
          squareCoordinateDerivative z x * x)
      (Icc (A : ℝ) (Y : ℝ)) :=
    (continuousOn_squareWeightedAbelDerivative hz (by linarith [hAR])).mul
      continuousOn_id
  have hbase := hcont.intervalIntegrable_of_Icc (μ := volume) hAYR
  apply hbase.congr
  intro x hx
  have hx' : x ∈ Ioc (A : ℝ) (Y : ℝ) := by
    simpa only [uIoc_of_le hAYR] using hx
  change weightedAbelCoefficientDerivative squareCoordinate
      squareCoordinateDerivative z x * x =
    deriv (weightedAbelCoefficient squareCoordinate z) x * x
  rw [deriv_squareWeightedAbelCoefficient hz (by linarith [hAR, hx'.1])]

lemma intervalIntegrable_deriv_squareWeighted_mul_thetaError
    {z : ℝ} (hz : 1 < z) {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    IntervalIntegrable
      (fun x : ℝ ↦
        deriv (weightedAbelCoefficient squareCoordinate z) x * thetaError x)
      volume (A : ℝ) (Y : ℝ) := by
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hthetaFull := intervalIntegrable_deriv_squareWeighted_mul_theta hz
    (hA.trans hAY)
  have htheta : IntervalIntegrable
      (fun x : ℝ ↦
        deriv (weightedAbelCoefficient squareCoordinate z) x *
          Chebyshev.theta x) volume (A : ℝ) (Y : ℝ) := by
    apply hthetaFull.mono_set
    rw [uIcc_of_le hAYR]
    have h2Y : (2 : ℝ) ≤ (Y : ℝ) := hAR.trans hAYR
    rw [uIcc_of_le h2Y]
    intro x hx
    exact ⟨hAR.trans hx.1, hx.2⟩
  have hmain := intervalIntegrable_deriv_squareWeighted_mul_id hz hA hAY
  have hsub := htheta.sub hmain
  apply hsub.congr
  intro x hx
  unfold thetaError
  ring

/-- Exact actual-prime second-moment quadrature with the literal PNT
remainder still displayed. -/
theorem squarePrimeCell_sub_continuum_eq_remainder
    {z : ℝ} (hz : 1 < z) {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    fullWeightedReciprocalSum squareCoordinate z Y -
        fullWeightedReciprocalSum squareCoordinate z A -
        (∫ t in realLogCoordinate z (A : ℝ)..
          realLogCoordinate z (Y : ℝ), squareCoordinate t / t) =
      weightedAbelRemainder squareCoordinate z (A : ℝ) (Y : ℝ) := by
  have hY := hA.trans hAY
  have hdiff : ∀ x ∈ Icc (2 : ℝ) (Y : ℝ),
      DifferentiableAt ℝ (weightedAbelCoefficient squareCoordinate z) x := by
    intro x hx
    exact (hasDerivAt_squareWeightedAbelCoefficient hz
      (by linarith [hx.1])).differentiableAt
  have hint := integrableOn_deriv_squareWeightedAbelCoefficient hz hY
  have hdecomp := fullWeightedReciprocalSum_interval_sub_main_eq_remainder
    squareCoordinate z hA hAY hdiff hint
    (intervalIntegrable_deriv_squareWeighted_mul_theta hz hY)
    (intervalIntegrable_deriv_squareWeighted_mul_id hz hA hAY)
    (intervalIntegrable_deriv_squareWeighted_mul_thetaError hz hA hAY)
  rw [weightedAbelMain_eq_logCoordinateIntegral squareCoordinate
    continuous_squareCoordinate hz hA hAY hdiff hint] at hdecomp
  exact hdecomp

lemma squareCoordinate_integral_formula
    {z : ℝ} (hz : 1 < z) {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    (∫ t in realLogCoordinate z (A : ℝ)..
      realLogCoordinate z (Y : ℝ), squareCoordinate t / t) =
      (realLogCoordinate z (Y : ℝ) ^ 2 -
        realLogCoordinate z (A : ℝ) ^ 2) / 2 := by
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have hlogA : 0 < Real.log (A : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have ha : 0 < realLogCoordinate z (A : ℝ) := by
    unfold realLogCoordinate
    exact div_pos hlogA hlogz
  have hApos : (0 : ℝ) < (A : ℝ) := by positivity
  have hlogAY : Real.log (A : ℝ) ≤ Real.log (Y : ℝ) :=
    Real.log_le_log hApos (by exact_mod_cast hAY)
  have hab : realLogCoordinate z (A : ℝ) ≤
      realLogCoordinate z (Y : ℝ) := by
    unfold realLogCoordinate
    exact div_le_div_of_nonneg_right hlogAY hlogz.le
  calc
    (∫ t in realLogCoordinate z (A : ℝ)..
        realLogCoordinate z (Y : ℝ), squareCoordinate t / t) =
        ∫ t in realLogCoordinate z (A : ℝ)..
          realLogCoordinate z (Y : ℝ), t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htIcc : t ∈ Icc (realLogCoordinate z (A : ℝ))
          (realLogCoordinate z (Y : ℝ)) := by
        simpa only [uIcc_of_le hab] using ht
      have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le htIcc.1)
      unfold squareCoordinate
      field_simp
    _ = _ := integral_id

/-- Closed-form exact decomposition for the actual second-coordinate prime
sum on `(A,Y]`. -/
theorem squarePrimeCell_sub_formula_eq_remainder
    {z : ℝ} (hz : 1 < z) {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    fullWeightedReciprocalSum squareCoordinate z Y -
        fullWeightedReciprocalSum squareCoordinate z A -
        ((realLogCoordinate z (Y : ℝ) ^ 2 -
          realLogCoordinate z (A : ℝ) ^ 2) / 2) =
      weightedAbelRemainder squareCoordinate z (A : ℝ) (Y : ℝ) := by
  rw [← squareCoordinate_integral_formula hz hA hAY]
  exact squarePrimeCell_sub_continuum_eq_remainder hz hA hAY

lemma squareWeightedAbelCoefficient_eq
    {z x : ℝ} (hz : 1 < z) (hx : 1 < x) :
    weightedAbelCoefficient squareCoordinate z x =
      Real.log x / (x * Real.log z ^ 2) := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hlogz : Real.log z ≠ 0 := ne_of_gt (Real.log_pos hz)
  unfold weightedAbelCoefficient squareCoordinate realLogCoordinate
  field_simp

lemma squareWeightedAbelDerivative_eq
    {z x : ℝ} (hz : 1 < z) (hx : 1 < x) :
    deriv (weightedAbelCoefficient squareCoordinate z) x =
      (1 - Real.log x) / (x ^ 2 * Real.log z ^ 2) := by
  rw [deriv_squareWeightedAbelCoefficient hz hx]
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hlogz : Real.log z ≠ 0 := ne_of_gt (Real.log_pos hz)
  unfold weightedAbelCoefficientDerivative squareCoordinate
    squareCoordinateDerivative realLogCoordinate
  field_simp
  ring

/-- Integrable majorant for the square-coordinate PNT remainder. -/
def squareMomentTailMajorant (C z x : ℝ) : ℝ :=
  C / Real.log z ^ 2 / (x * Real.log x ^ 2)

def squareMomentTailPrimitive (C z x : ℝ) : ℝ :=
  -(C / Real.log z ^ 2) / Real.log x

lemma hasDerivAt_squareMomentTailPrimitive
    (C z : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (squareMomentTailPrimitive C z)
      (squareMomentTailMajorant C z x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hinv := (Real.hasDerivAt_log hx0).inv hlogx
  have hmul := (hasDerivAt_const x (-(C / Real.log z ^ 2))).mul hinv
  convert hmul using 1
  · unfold squareMomentTailMajorant
    field_simp [hx0, hlogx]
    ring

lemma continuousOn_squareMomentTailMajorant
    (C z : ℝ) {A Y : ℝ} (hA : 1 < A) :
    ContinuousOn (squareMomentTailMajorant C z) (Icc A Y) := by
  intro x hx
  have hx1 : 1 < x := hA.trans_le hx.1
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx1)
  have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  unfold squareMomentTailMajorant
  exact (continuousAt_const.div_const (Real.log z ^ 2)).div
    (continuousAt_id.mul ((Real.continuousAt_log hx0).pow 2))
    (mul_ne_zero hx0 (pow_ne_zero 2 hlogx)) |>.continuousWithinAt

lemma integral_squareMomentTailMajorant
    (C z : ℝ) {A Y : ℝ} (hA : 2 ≤ A) (hAY : A ≤ Y) :
    (∫ x in A..Y, squareMomentTailMajorant C z x) =
      squareMomentTailPrimitive C z Y -
        squareMomentTailPrimitive C z A := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hAY] at hx
    exact hasDerivAt_squareMomentTailPrimitive C z
      (by linarith [hA, hx.1])
  · exact ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hAY
      (continuousOn_squareMomentTailMajorant C z (by linarith [hA]))

lemma one_le_log_of_eight_le {x : ℝ} (hx : 8 ≤ x) :
    1 ≤ Real.log x := by
  have h8pos : (0 : ℝ) < 8 := by norm_num
  have hlog := Real.log_le_log h8pos hx
  have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    ring
  rw [hlog8] at hlog
  nlinarith [Real.log_two_gt_d9]

lemma abs_squareWeightedCoefficient_mul_thetaError_le
    {C z x : ℝ} (hz : 1 < z) (hx : 8 ≤ x)
    (hTheta : |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |weightedAbelCoefficient squareCoordinate z x * thetaError x| ≤
      C / (Real.log z ^ 2 * Real.log x ^ 2) := by
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlogz : 0 < Real.log z := Real.log_pos hz
  rw [squareWeightedAbelCoefficient_eq hz hx1, abs_mul, abs_div,
    abs_of_pos hlogx, abs_of_pos
      (mul_pos hx0 (sq_pos_of_pos hlogz))]
  calc
    Real.log x / (x * Real.log z ^ 2) * |thetaError x| ≤
        (Real.log x / (x * Real.log z ^ 2)) *
          (C * x / Real.log x ^ 3) := by
      exact mul_le_mul_of_nonneg_left hTheta (by positivity)
    _ = C / (Real.log z ^ 2 * Real.log x ^ 2) := by
      field_simp [ne_of_gt hx0, ne_of_gt hlogx, ne_of_gt hlogz]

lemma abs_squareWeightedDerivative_mul_thetaError_le
    {C z x : ℝ} (hz : 1 < z) (hx : 8 ≤ x)
    (hTheta : |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |deriv (weightedAbelCoefficient squareCoordinate z) x * thetaError x| ≤
      squareMomentTailMajorant C z x := by
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have hlogOne : 1 ≤ Real.log x := one_le_log_of_eight_le hx
  have habs : |1 - Real.log x| ≤ Real.log x := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  rw [squareWeightedAbelDerivative_eq hz hx1, abs_mul, abs_div,
    abs_of_pos (mul_pos (sq_pos_of_pos hx0) (sq_pos_of_pos hlogz))]
  calc
    |1 - Real.log x| / (x ^ 2 * Real.log z ^ 2) * |thetaError x| ≤
        (Real.log x / (x ^ 2 * Real.log z ^ 2)) *
          (C * x / Real.log x ^ 3) := by
      exact mul_le_mul
        (div_le_div_of_nonneg_right habs (by positivity)) hTheta
        (abs_nonneg _) (by positivity)
    _ = squareMomentTailMajorant C z x := by
      unfold squareMomentTailMajorant
      field_simp [ne_of_gt hx0, ne_of_gt hlogx, ne_of_gt hlogz]

/-- Uniform quantitative PNT bound for the square-coordinate remainder.
The lower endpoint alone controls the error; the upper endpoint may move all
the way to the ambient scale. -/
theorem abs_squareWeightedAbelRemainder_le
    {C z : ℝ} (hC : 0 ≤ C) (hz : 1 < z)
    {A Y : ℕ} (hA : 8 ≤ A) (hAY : A ≤ Y)
    (hTheta : ∀ x ∈ Icc (A : ℝ) (Y : ℝ),
      |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |weightedAbelRemainder squareCoordinate z (A : ℝ) (Y : ℝ)| ≤
      3 * C / (Real.log z ^ 2 * Real.log (A : ℝ)) := by
  have hAR : (8 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hApos : (0 : ℝ) < A := by positivity
  have hYpos : (0 : ℝ) < Y := hApos.trans_le hAYR
  have hlogA : 0 < Real.log (A : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have hlogY : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have hlogAY : Real.log (A : ℝ) ≤ Real.log (Y : ℝ) :=
    Real.log_le_log hApos hAYR
  have hlogAOne : 1 ≤ Real.log (A : ℝ) :=
    one_le_log_of_eight_le hAR
  let K : ℝ := C / Real.log z ^ 2
  have hK0 : 0 ≤ K := by dsimp only [K]; positivity
  have hmajorInt : IntervalIntegrable (squareMomentTailMajorant C z)
      volume (A : ℝ) (Y : ℝ) :=
    ContinuousOn.intervalIntegrable_of_Icc hAYR
      (continuousOn_squareMomentTailMajorant C z (by linarith [hAR]))
  have herrorInt :=
    intervalIntegrable_deriv_squareWeighted_mul_thetaError hz
      (show 2 ≤ A by omega) hAY
  have hIntBound :
      (∫ x in (A : ℝ)..Y,
        |deriv (weightedAbelCoefficient squareCoordinate z) x *
          thetaError x|) ≤ K / Real.log (A : ℝ) := by
    calc
      (∫ x in (A : ℝ)..Y,
          |deriv (weightedAbelCoefficient squareCoordinate z) x *
            thetaError x|) ≤
          ∫ x in (A : ℝ)..Y, squareMomentTailMajorant C z x := by
        exact intervalIntegral.integral_mono_on hAYR herrorInt.abs hmajorInt
          (fun x hx ↦ abs_squareWeightedDerivative_mul_thetaError_le
            hz (hAR.trans hx.1) (hTheta x hx))
      _ = squareMomentTailPrimitive C z (Y : ℝ) -
          squareMomentTailPrimitive C z (A : ℝ) :=
        integral_squareMomentTailMajorant C z (by linarith [hAR]) hAYR
      _ ≤ K / Real.log (A : ℝ) := by
        have hnonneg : 0 ≤ K /
            Real.log (Y : ℝ) := by positivity
        have heq :
            squareMomentTailPrimitive C z (Y : ℝ) -
                squareMomentTailPrimitive C z (A : ℝ) =
              K / Real.log (A : ℝ) - K / Real.log (Y : ℝ) := by
          dsimp only [squareMomentTailPrimitive, K]
          ring
        rw [heq]
        exact sub_le_self _ hnonneg
  have hAterm :
      |weightedAbelCoefficient squareCoordinate z (A : ℝ) *
        thetaError (A : ℝ)| ≤
        K / Real.log (A : ℝ) ^ 2 := by
    simpa only [K, div_div] using
      abs_squareWeightedCoefficient_mul_thetaError_le hz hAR
        (hTheta (A : ℝ) ⟨le_rfl, hAYR⟩)
  have hYterm :
      |weightedAbelCoefficient squareCoordinate z (Y : ℝ) *
        thetaError (Y : ℝ)| ≤
        K / Real.log (A : ℝ) ^ 2 := by
    have hyRaw := abs_squareWeightedCoefficient_mul_thetaError_le hz
      (hAR.trans hAYR) (hTheta (Y : ℝ) ⟨hAYR, le_rfl⟩)
    calc
      _ ≤ C / (Real.log z ^ 2 * Real.log (Y : ℝ) ^ 2) := hyRaw
      _ ≤ C / (Real.log z ^ 2 * Real.log (A : ℝ) ^ 2) := by
        gcongr
      _ = K / Real.log (A : ℝ) ^ 2 := by
        dsimp only [K]
        ring
  have hinvSq : K / Real.log (A : ℝ) ^ 2 ≤
      K / Real.log (A : ℝ) := by
    have hsq : Real.log (A : ℝ) ≤ Real.log (A : ℝ) ^ 2 := by
      nlinarith
    exact div_le_div_of_nonneg_left hK0 hlogA hsq
  calc
    |weightedAbelRemainder squareCoordinate z (A : ℝ) (Y : ℝ)| ≤
        |weightedAbelCoefficient squareCoordinate z (Y : ℝ)| *
            |thetaError (Y : ℝ)| +
          |weightedAbelCoefficient squareCoordinate z (A : ℝ)| *
            |thetaError (A : ℝ)| +
          ∫ x in (A : ℝ)..Y,
            |deriv (weightedAbelCoefficient squareCoordinate z) x *
              thetaError x| :=
      abs_weightedAbelRemainder_le squareCoordinate z hAYR
    _ ≤ K / Real.log (A : ℝ) ^ 2 +
        K / Real.log (A : ℝ) ^ 2 +
          K / Real.log (A : ℝ) := by
      exact add_le_add (add_le_add (by simpa [abs_mul] using hYterm)
        (by simpa [abs_mul] using hAterm)) hIntBound
    _ ≤ 3 * (K / Real.log (A : ℝ)) := by linarith
    _ = 3 * C / (Real.log z ^ 2 * Real.log (A : ℝ)) := by
      dsimp only [K]
      ring

/-- The genuine PNT supplies one constant and one lower threshold before
the ambient scale and both moving endpoints are chosen. -/
theorem exists_uniform_squarePrimeCell_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ,
      ∀ z : ℝ, 1 < z → ∀ A Y : ℕ,
        X₀ ≤ A → A ≤ Y →
        |fullWeightedReciprocalSum squareCoordinate z Y -
            fullWeightedReciprocalSum squareCoordinate z A -
            ((realLogCoordinate z (Y : ℝ) ^ 2 -
              realLogCoordinate z (A : ℝ) ^ 2) / 2)| ≤
          3 * C / (Real.log z ^ 2 * Real.log (A : ℝ)) := by
  obtain ⟨C, hC, X₀R, hTheta⟩ := exists_thetaError_log_cube_bound
  obtain ⟨N, hX₀N⟩ := exists_nat_gt X₀R
  refine ⟨C, hC, max N 8, ?_⟩
  intro z hz A Y hA hAY
  have hA8 : 8 ≤ A := (le_max_right N 8).trans hA
  have hNA : N ≤ A := (le_max_left N 8).trans hA
  rw [squarePrimeCell_sub_formula_eq_remainder hz (show 2 ≤ A by omega) hAY]
  apply abs_squareWeightedAbelRemainder_le hC.le hz hA8 hAY
  intro x hx
  apply hTheta x
  have hNAR : (N : ℝ) ≤ (A : ℝ) := by exact_mod_cast hNA
  exact (le_of_lt hX₀N).trans (hNAR.trans hx.1)







end

end Erdos390.Full.PrimeCoordinateSecondMoment

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

def deviation (p : BandPrime n W) : ℝ :=
  P.center (P.band p) - tPrime n p.1

def bandL1 (j : Band) : ℝ :=
  ∑ p ∈ P.data.fiber j, (1 / (p.1 : ℝ)) * |P.deviation p|

def totalL1 : ℝ :=
  ∑ p : BandPrime n W, (1 / (p.1 : ℝ)) * |P.deviation p|

def bandSecondMoment (j : Band) : ℝ :=
  ∑ p ∈ P.data.fiber j, (1 / (p.1 : ℝ)) * (tPrime n p.1) ^ 2

def bandVariance (j : Band) : ℝ :=
  ∑ p ∈ P.data.fiber j, (1 / (p.1 : ℝ)) * P.deviation p ^ 2























end

end Erdos390.Full.ArithmeticBandGeometry.Partition

end

/- Source module: Erdos390.Full.MovingLowMomentQuadrature -/
section


/-!
# Endpoint-uniform first logarithmic prime moment

For the moving low cell the lower cutoff is fixed while the upper endpoint
grows.  Keeping the integrable `1/(x log^3 x)` PNT majorant, rather than
freezing `log x` at the lower endpoint, gives an error independent of the
upper endpoint.  Division by the ambient logarithmic scale therefore tends
to zero and supplies the relative low-center transfer.
-/

open Set

noncomputable section

namespace Erdos390.Full.MovingLowMomentQuadrature

open MeasureTheory PrimeSums PrimeBandQuadrature

def logMomentTailMajorant (C x : ℝ) : ℝ :=
  C / (x * Real.log x ^ 3)

def logMomentTailPrimitive (C x : ℝ) : ℝ :=
  -C / (2 * Real.log x ^ 2)

lemma hasDerivAt_logMomentTailPrimitive (C : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (logMomentTailPrimitive C)
      (logMomentTailMajorant C x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hpow := (Real.hasDerivAt_log hx0).pow 2
  have hinv := hpow.inv (pow_ne_zero 2 hlog0)
  have hmul := (hasDerivAt_const x (-(C / 2))).mul hinv
  convert hmul using 1
  · unfold logMomentTailPrimitive
    funext z
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply]
    ring_nf
  · unfold logMomentTailMajorant
    simp only [Pi.pow_apply]
    field_simp [hx0, hlog0]
    ring

lemma continuousOn_logMomentTailMajorant (C : ℝ) {A Y : ℝ}
    (hA : 1 < A) :
    ContinuousOn (logMomentTailMajorant C) (Icc A Y) := by
  intro x hx
  have hx1 : 1 < x := hA.trans_le hx.1
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx1)
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  unfold logMomentTailMajorant
  exact continuousAt_const.div
    (continuousAt_id.mul ((Real.continuousAt_log hx0).pow 3))
    (mul_ne_zero hx0 (pow_ne_zero 3 hlog0)) |>.continuousWithinAt

lemma integral_logMomentTailMajorant (C : ℝ) {A Y : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    (∫ x in A..Y, logMomentTailMajorant C x) =
      logMomentTailPrimitive C Y - logMomentTailPrimitive C A := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hAY] at hx
    exact hasDerivAt_logMomentTailPrimitive C (by linarith [hx.1, hA])
  · exact ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hAY
      (continuousOn_logMomentTailMajorant C (A := A) (Y := Y)
        (by linarith [hA]))

lemma intervalIntegrable_logReciprocalErrorKernel
    {A Y : ℝ} (hA : 2 ≤ A) (hAY : A ≤ Y) :
    IntervalIntegrable logReciprocalErrorKernel volume A Y := by
  have htheta := PrimeSums.intervalIntegrable_theta_div_sq
    (hA.trans hAY)
  have hthetaCell : IntervalIntegrable
      (fun x : ℝ => Chebyshev.theta x / x ^ 2) volume A Y := by
    apply htheta.mono_set
    rw [uIcc_of_le hAY, uIcc_of_le (hA.trans hAY)]
    intro x hx
    exact ⟨hA.trans hx.1, hx.2⟩
  have hmain : IntervalIntegrable (fun x : ℝ => 1 / x) volume A Y := by
    apply ContinuousOn.intervalIntegrable_of_Icc hAY
    intro x hx
    exact (continuousAt_const.div continuousAt_id
      (by simpa only [id_eq] using
        (ne_of_gt (show 0 < x by linarith [hA, hx.1])))).continuousWithinAt
  apply (hthetaCell.sub hmain).congr
  intro x hx
  have hx0 : x ≠ 0 := by
    have hx' : x ∈ uIcc A Y := uIoc_subset_uIcc hx
    rw [uIcc_of_le hAY] at hx'
    exact ne_of_gt (by linarith [hA, hx'.1])
  unfold logReciprocalErrorKernel thetaError
  field_simp [hx0]

lemma abs_logReciprocalErrorKernel_le_tail (C : ℝ)
    {x : ℝ} (hx : 2 ≤ x)
    (hTheta : |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |logReciprocalErrorKernel x| ≤ logMomentTailMajorant C x := by
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  unfold logReciprocalErrorKernel logMomentTailMajorant
  rw [abs_div, abs_of_pos (sq_pos_of_pos hxpos)]
  calc
    |thetaError x| / x ^ 2 ≤
        (C * x / Real.log x ^ 3) / x ^ 2 := by gcongr
    _ = C / (x * Real.log x ^ 3) := by
      field_simp [ne_of_gt hxpos, ne_of_gt hlogpos]

theorem fullLogReciprocalSum_interval_uniform_error_bound {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) {C : ℝ} (hC : 0 ≤ C)
    (hTheta : ∀ x ∈ Icc (A : ℝ) (Y : ℝ),
      |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |fullLogReciprocalSum Y - fullLogReciprocalSum A -
        (Real.log (Y : ℝ) - Real.log (A : ℝ))| ≤
      2 * C / Real.log (A : ℝ) ^ 3 +
        C / (2 * Real.log (A : ℝ) ^ 2) := by
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hApos : (0 : ℝ) < A := by positivity
  have hYpos : (0 : ℝ) < Y := hApos.trans_le hAYR
  have hlogApos : 0 < Real.log (A : ℝ) := Real.log_pos (by exact_mod_cast
    (show 1 < A by omega))
  have hlogYpos : 0 < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast
    (show 1 < Y by omega))
  have hlogAY : Real.log (A : ℝ) ≤ Real.log (Y : ℝ) :=
    Real.log_le_log hApos hAYR
  have herrInt := intervalIntegrable_logReciprocalErrorKernel hAR hAYR
  have hmajorInt : IntervalIntegrable (logMomentTailMajorant C) volume
      (A : ℝ) (Y : ℝ) :=
    ContinuousOn.intervalIntegrable_of_Icc hAYR
      (continuousOn_logMomentTailMajorant C (by linarith [hAR]))
  have hIntBound :
      |∫ x in (A : ℝ)..Y, logReciprocalErrorKernel x| ≤
        C / (2 * Real.log (A : ℝ) ^ 2) := by
    calc
      |∫ x in (A : ℝ)..Y, logReciprocalErrorKernel x| ≤
          ∫ x in (A : ℝ)..Y, |logReciprocalErrorKernel x| :=
        intervalIntegral.abs_integral_le_integral_abs hAYR
      _ ≤ ∫ x in (A : ℝ)..Y, logMomentTailMajorant C x := by
        exact intervalIntegral.integral_mono_on hAYR herrInt.abs hmajorInt
          (fun x hx => abs_logReciprocalErrorKernel_le_tail C
            (hAR.trans hx.1) (hTheta x hx))
      _ = logMomentTailPrimitive C (Y : ℝ) -
          logMomentTailPrimitive C (A : ℝ) :=
        integral_logMomentTailMajorant C hAR hAYR
      _ ≤ C / (2 * Real.log (A : ℝ) ^ 2) := by
        unfold logMomentTailPrimitive
        have hnonneg : 0 ≤ C / (2 * Real.log (Y : ℝ) ^ 2) := by positivity
        have heq :
            -C / (2 * Real.log (Y : ℝ) ^ 2) -
                (-C / (2 * Real.log (A : ℝ) ^ 2)) =
              C / (2 * Real.log (A : ℝ) ^ 2) -
                C / (2 * Real.log (Y : ℝ) ^ 2) := by ring
        rw [heq]
        exact sub_le_self _ hnonneg
  rw [fullLogReciprocalSum_interval_error_identity hA hAY]
  have hAterm : |thetaError (A : ℝ) / (A : ℝ)| ≤
      C / Real.log (A : ℝ) ^ 3 := by
    rw [abs_div, abs_of_pos hApos]
    calc
      _ ≤ (C * (A : ℝ) / Real.log (A : ℝ) ^ 3) / (A : ℝ) := by
        exact div_le_div_of_nonneg_right
          (hTheta (A : ℝ) ⟨le_rfl, hAYR⟩) hApos.le
      _ = _ := by field_simp [ne_of_gt hApos]
  have hYterm : |thetaError (Y : ℝ) / (Y : ℝ)| ≤
      C / Real.log (A : ℝ) ^ 3 := by
    rw [abs_div, abs_of_pos hYpos]
    calc
      _ ≤ (C * (Y : ℝ) / Real.log (Y : ℝ) ^ 3) / (Y : ℝ) := by
        exact div_le_div_of_nonneg_right
          (hTheta (Y : ℝ) ⟨hAYR, le_rfl⟩) hYpos.le
      _ = C / Real.log (Y : ℝ) ^ 3 := by field_simp [ne_of_gt hYpos]
      _ ≤ C / Real.log (A : ℝ) ^ 3 := by gcongr
  calc
    |thetaError (Y : ℝ) / (Y : ℝ) -
        thetaError (A : ℝ) / (A : ℝ) +
        ∫ x in (A : ℝ)..Y, logReciprocalErrorKernel x| ≤
      |thetaError (Y : ℝ) / (Y : ℝ)| +
        |thetaError (A : ℝ) / (A : ℝ)| +
        |∫ x in (A : ℝ)..Y, logReciprocalErrorKernel x| := by
      have h₁ := abs_add_le
        (thetaError (Y : ℝ) / (Y : ℝ) - thetaError (A : ℝ) / (A : ℝ))
        (∫ x in (A : ℝ)..Y, logReciprocalErrorKernel x)
      have h₂ := abs_sub (thetaError (Y : ℝ) / (Y : ℝ))
        (thetaError (A : ℝ) / (A : ℝ))
      linarith
    _ ≤ 2 * C / Real.log (A : ℝ) ^ 3 +
        C / (2 * Real.log (A : ℝ) ^ 2) := by
      calc
        _ ≤ C / Real.log (A : ℝ) ^ 3 +
              C / Real.log (A : ℝ) ^ 3 +
              C / (2 * Real.log (A : ℝ) ^ 2) :=
          add_le_add (add_le_add hYterm hAterm) hIntBound
        _ = _ := by ring



theorem exists_fullLogReciprocalSum_interval_uniform_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ A Y : ℕ,
      X₀ ≤ A → A ≤ Y →
      |fullLogReciprocalSum Y - fullLogReciprocalSum A -
          (Real.log (Y : ℝ) - Real.log (A : ℝ))| ≤
        2 * C / Real.log (A : ℝ) ^ 3 +
          C / (2 * Real.log (A : ℝ) ^ 2) := by
  obtain ⟨C, hC, X₀R, hTheta⟩ := exists_thetaError_log_cube_bound
  obtain ⟨N, hX₀N⟩ := exists_nat_gt X₀R
  refine ⟨C, hC, max N 2, ?_⟩
  intro A Y hA hAY
  have hA2 : 2 ≤ A := (le_max_right N 2).trans hA
  apply fullLogReciprocalSum_interval_uniform_error_bound hA2 hAY hC.le
  intro x hx
  apply hTheta x
  have hNA : N ≤ A := (le_max_left N 2).trans hA
  have hNAR : (N : ℝ) ≤ (A : ℝ) := by exact_mod_cast hNA
  exact (le_of_lt hX₀N).trans (hNAR.trans hx.1)

/-- A named global witness for the first-logarithmic-moment PNT constant. -/
noncomputable def fullLogReciprocalSumUniformConstant : ℝ :=
  Classical.choose exists_fullLogReciprocalSum_interval_uniform_error_bound



/-- The corresponding named arithmetic cutoff.  Both this cutoff and the
preceding constant are independent of every later regular mesh. -/
noncomputable def fullLogReciprocalSumUniformCutoff : ℕ :=
  Classical.choose
    (Classical.choose_spec
      exists_fullLogReciprocalSum_interval_uniform_error_bound).2





end Erdos390.Full.MovingLowMomentQuadrature

end

/- Source module: Erdos390.Full.RegularMeshMomentBounds -/
section


/-!
# Moment budgets for the regular relative mesh

This is the elementary continuum census behind the arithmetic estimates in
Lemma 8.6.  The moving-low cell provides the quadratic lower bound, while the
geometric positive cells have total `L¹` cost at most their common relative
width and total quadratic cost at most its square.
-/

open scoped BigOperators

namespace Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- Continuum harmonic mass `integral dt/t` of a positive cell. -/
def cellHarmonicMass (k : Fin M.cellCount) : ℝ :=
  Real.log (M.upper k / M.lower k)

























end Mesh





















end

end Erdos390.Full.RegularRelativeMesh

end

/- Source module: Erdos390.Full.RegularMeshActualMomentBounds -/
section


/-!
# Actual arithmetic `L¹` and variance bounds for the regular mesh

The endpoints in this file are the explicit floored endpoints from
`RegularMeshPrimeCutoffs`, and every sum is over the actual primes.  The
first part proves the finite deterministic assembly.  The final part derives
its moment inputs from the proved PNT quadratures.
-/

open scoped BigOperators
open Filter

namespace Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer KernelPrimeQuadrature
open PrimeIntervalPartitionConstructor









namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)
  {n W : ℕ} (P : Partition n W (Fin (M.cellCount + 1)))
  (E : IntervalCertificate P)
  (hLower : ∀ j, E.lower j = fullCutoff M n W j.1)
  (hUpper : ∀ j, E.upper j = fullCutoff M n W (j.1 + 1))

include E hLower hUpper





/-- Concrete finite moment conditions isolated from their PNT proof. -/
structure MomentReady : Prop where
  positiveMass : ∀ k : Fin M.cellCount, P.mass k.succ ≤ 3 * M.ratio
  lowFirst : P.mass 0 * P.center 0 ≤ 2 * delta
  lowSecondLower : delta ^ 2 / 3 ≤ P.bandSecondMoment 0
  lowSecondUpper : P.bandSecondMoment 0 ≤ delta ^ 2
  lowMass : 48 ≤ P.mass 0









end Mesh

end

end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.CanonicalRegularMeshEndpointFamily -/
section


/-!
# The canonical `n`-indexed endpoint family for a regular mesh

This module exposes the actual partition constructed from the explicit
cutoffs, rather than only asserting its existence.  Consequently the low
cell and every later lower endpoint can be audited definitionally.
-/

open Filter

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry
open RegularRelativeMesh
open PrimeIntervalPartitionConstructor PositiveCellTransfer

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- Index of the unique moving-low cell. -/
def lowBand : Fin (M.cellCount + 1) := ⟨0, by omega⟩

/-- Embedding of a positive regular-mesh cell after the low cell. -/
def positiveBand (k : Fin M.cellCount) : Fin (M.cellCount + 1) :=
  ⟨k.1 + 1, by omega⟩

theorem W_le_first_fullCutoff
    {n W : ℕ} (S : ScaleSeparation M n W) :
    W ≤ fullCutoff M n W 1 := by
  apply Nat.le_floor
  have htwo : (W : ℝ) ≤ (2 * W : ℝ) := by
    calc
      (W : ℝ) ≤ (W : ℝ) + (W : ℝ) :=
        le_add_of_nonneg_right (Nat.cast_nonneg W)
      _ = (2 : ℝ) * W := by ring
  have hscale : (W : ℝ) ≤ scalePoint n delta := htwo.trans S.low
  simpa only [fullCutoff, M.endpoint_zero] using hscale

/-- The actual partition attached to the explicit cutoff family. -/
def canonicalPartition
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W) :
    ArithmeticBandGeometry.Partition n W (Fin (M.cellCount + 1)) :=
  PrimeIntervalPartitionConstructor.partition
    (by omega : 0 < M.cellCount + 1)
    (fullCutoff M n W)
    (fullCutoff_monotone M hdelta hn (W_le_first_fullCutoff M S))
    rfl
    (fullCutoff_last M (Nat.zero_lt_of_lt hn))
    (every_fullCutoff_cell_has_prime M hW S)

/-- Its canonical interval certificate. -/
def canonicalCertificate
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W) :
    IntervalCertificate (canonicalPartition M hdelta hn hW S) :=
  PrimeIntervalPartitionConstructor.intervalCertificate
    (by omega : 0 < M.cellCount + 1)
    (fullCutoff M n W)
    (fullCutoff_monotone M hdelta hn (W_le_first_fullCutoff M S))
    rfl
    (fullCutoff_last M (Nat.zero_lt_of_lt hn))
    (every_fullCutoff_cell_has_prime M hW S)

@[simp] theorem canonicalCertificate_lower
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (j : Fin (M.cellCount + 1)) :
    (canonicalCertificate M hdelta hn hW S).lower j =
      fullCutoff M n W j.1 := rfl

@[simp] theorem canonicalCertificate_upper
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (j : Fin (M.cellCount + 1)) :
    (canonicalCertificate M hdelta hn hW S).upper j =
      fullCutoff M n W (j.1 + 1) := rfl





theorem canonicalCertificate_lower_ge_cutoff
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (j : Fin (M.cellCount + 1)) :
    W ≤ (canonicalCertificate M hdelta hn hW S).lower j := by
  rw [canonicalCertificate_lower]
  exact (fullCutoff_monotone M hdelta hn
    (W_le_first_fullCutoff M S)) (Nat.zero_le j.1)





end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.FirstFailure -/
section


/-!
# A compact first-failure principle

This isolates the order/topology step used in the Dickman log-slope
continuation argument.  It prevents the phrase "take the first failure
point" from hiding a compactness argument.
-/

open Set

namespace Erdos390.Full.FirstFailure

/-- If a continuous real function is positive at every point provided it
was positive at every strictly earlier point of a compact interval, then it
is positive throughout that interval. -/
theorem positiveOn_Icc_of_positive_at_first_failure
    (g : ℝ → ℝ) {a b : ℝ} (hg : ContinuousOn g (Icc a b))
    (hstep : ∀ x ∈ Icc a b,
      (∀ y ∈ Icc a x, y < x → 0 < g y) → 0 < g x) :
    ∀ x ∈ Icc a b, 0 < g x := by
  let bad : Set ℝ := Icc a b ∩ {x | g x ≤ 0}
  have hbadCompact : IsCompact bad := by
    have hbadClosed : IsClosed bad := by
      dsimp only [bad]
      exact isClosed_Icc.isClosed_le hg continuousOn_const
    exact isCompact_Icc.of_isClosed_subset hbadClosed (fun _ hx ↦ hx.1)
  by_contra hfail
  push_neg at hfail
  obtain ⟨x₀, hx₀Icc, hx₀bad⟩ := hfail
  have hbadNonempty : bad.Nonempty := ⟨x₀, hx₀Icc, hx₀bad⟩
  obtain ⟨x, hxBad, hxMin⟩ :=
    hbadCompact.exists_isMinOn hbadNonempty continuousOn_id
  have hprev : ∀ y ∈ Icc a x, y < x → 0 < g y := by
    intro y hyIcc hyx
    by_contra hyNot
    have hyNonpos : g y ≤ 0 := le_of_not_gt hyNot
    have hyFull : y ∈ Icc a b := by
      exact ⟨hyIcc.1, hyIcc.2.trans hxBad.1.2⟩
    have hyBad : y ∈ bad := ⟨hyFull, hyNonpos⟩
    have hxy : x ≤ y := hxMin hyBad
    exact (not_lt_of_ge hxy) hyx
  have hxPos := hstep x hxBad.1 hprev
  exact (not_lt_of_ge hxBad.2) hxPos

end Erdos390.Full.FirstFailure

end


