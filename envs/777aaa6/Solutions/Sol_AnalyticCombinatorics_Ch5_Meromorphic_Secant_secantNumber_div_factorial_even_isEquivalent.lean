-- Prove2me | solution 1 for AnalyticCombinatorics.Ch5.Meromorphic.Secant.secantNumber_div_factorial_even_isEquivalent
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T22:11:06.810755+00:00
-- url     : https://prove2.me/submissions/c29c505a-bcf6-457a-bed0-49149555a74d

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch5_Meromorphic_SupercriticalSeqGenuine
import Definitions.Def_AnalyticCombinatorics_Ch5_Meromorphic_Secant
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Filter ENNReal
open scoped PowerSeries Topology NNReal ENNReal

noncomputable section

namespace PowerSeries

@[simp] lemma coeff_toFMLS (f : PowerSeries ℂ) (n : ℕ) :
    (toFMLS f).coeff n = PowerSeries.coeff (R := ℂ) n f := by
  simp [toFMLS]

end PowerSeries
end

open Complex
open scoped NNReal ENNReal

noncomputable section

theorem coeff_eq_cauchy_circleIntegral_of_hasFPowerSeriesAt
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {R : ℝ}
    (hR : 0 < R)
    (hp : HasFPowerSeriesAt f p 0)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 R)) (n : ℕ) :
    p.coeff n =
      (2 * Real.pi * I : ℂ)⁻¹ •
        circleIntegral
          (fun z => ((1 : ℂ) / (z - 0)) ^ n • (z - 0)⁻¹ • f z)
          0 R := by
  have hq : HasFPowerSeriesAt f (cauchyPowerSeries f 0 R) 0 := by
    have hnn : 0 < ((⟨R, hR.le⟩ : ℝ≥0)) := by
      exact_mod_cast hR
    exact (hd.hasFPowerSeriesOnBall hnn).hasFPowerSeriesAt
  have hpq : p = cauchyPowerSeries f 0 R := hp.eq_formalMultilinearSeries hq
  calc
    p.coeff n = (cauchyPowerSeries f 0 R).coeff n := by rw [hpq]
    _ = (cauchyPowerSeries f 0 R n fun _ => (1 : ℂ)) := by rfl
    _ = _ := by exact cauchyPowerSeries_apply f 0 R n 1

theorem norm_coeff_le_of_circleIntegral
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {R M : ℝ}
    (hR : 0 < R)
    (hp : HasFPowerSeriesAt f p 0)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 R))
    (hM : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ M) (n : ℕ) :
    ‖p.coeff n‖ ≤ M * R⁻¹ ^ n := by
  let g : ℂ → ℂ := fun z => ((1 : ℂ) / (z - 0)) ^ n • (z - 0)⁻¹ • f z
  have hcoeff :
      p.coeff n = (2 * Real.pi * I : ℂ)⁻¹ • circleIntegral g 0 R := by
    simpa [g] using coeff_eq_cauchy_circleIntegral_of_hasFPowerSeriesAt hR hp hd n
  rw [hcoeff]
  calc
    ‖(2 * Real.pi * I : ℂ)⁻¹ • circleIntegral g 0 R‖
        ≤ R * (M * R⁻¹ ^ (n + 1)) := by
      refine circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
        hR.le ?_
      intro z hz
      have hz_norm : ‖z‖ = R := by
        simpa using (Metric.mem_sphere.1 hz)
      calc
        ‖g z‖ = R⁻¹ ^ n * R⁻¹ * ‖f z‖ := by
          simp [g, norm_pow, div_eq_mul_inv, hz_norm, inv_pow, mul_assoc]
        _ ≤ R⁻¹ ^ n * R⁻¹ * M := by
          exact mul_le_mul_of_nonneg_left (hM z hz)
            (mul_nonneg (pow_nonneg (inv_nonneg.mpr hR.le) n)
              (inv_nonneg.mpr hR.le))
        _ = M * R⁻¹ ^ (n + 1) := by
          rw [pow_succ]
          ring
    _ = M * R⁻¹ ^ n := by
      rw [pow_succ]
      field_simp [hR.ne']

end

open Filter Asymptotics
open scoped PowerSeries Topology BigOperators

noncomputable section

namespace PowerSeries

lemma coeff_rescale_invUnitsSub_one (a : ℂ) (n : ℕ) :
    coeff (R := ℂ) n (rescale a (invUnitsSub (1 : ℂˣ))) = a ^ n := by
  simp [coeff_rescale]

end PowerSeries
end

open Filter Asymptotics
open scoped BigOperators ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic

private lemma closedBall_subset_eball_of_ofReal_lt_radius
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {R : ℝ}
    (hRrad : ENNReal.ofReal R < p.radius) :
    Metric.closedBall (0 : ℂ) R ⊆ Metric.eball (0 : ℂ) p.radius := by
  intro z hz
  have hdist : dist z (0 : ℂ) ≤ R := by
    simpa [Metric.mem_closedBall] using hz
  have hed : edist z (0 : ℂ) ≤ ENNReal.ofReal R := by
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal hdist
  exact hed.trans_lt hRrad

private lemma exists_norm_bound_on_sphere
    {g : ℂ → ℂ} {R : ℝ}
    (hg : ContinuousOn g (Metric.sphere (0 : ℂ) R)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖g z‖ ≤ M := by
  have hnorm : ContinuousOn (fun z : ℂ => ‖g z‖) (Metric.sphere (0 : ℂ) R) :=
    continuous_norm.comp_continuousOn hg
  have hbdd :
      BddAbove ((fun z : ℂ => ‖g z‖) '' Metric.sphere (0 : ℂ) R) :=
    (isCompact_sphere (0 : ℂ) R).bddAbove_image hnorm
  rcases hbdd with ⟨M, hM⟩
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro z hz
  exact (hM (Set.mem_image_of_mem (fun z : ℂ => ‖g z‖) hz)).trans (le_max_left _ _)

/-- Cauchy's coefficient estimate on a circle gives geometric decay for the coefficients of an
analytic remainder on the closed disk. -/
theorem coeff_norm_isBigO_of_hasFPowerSeriesAt_differentiableOn
    {g : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {R : ℝ}
    (hR : 0 < R)
    (hp : HasFPowerSeriesAt g p 0)
    (hd : DifferentiableOn ℂ g (Metric.closedBall (0 : ℂ) R)) :
    (fun n : ℕ => ‖p.coeff n‖) =O[atTop] (fun n : ℕ => R⁻¹ ^ n) := by
  have hcont_closed : ContinuousOn g (Metric.closedBall (0 : ℂ) R) :=
    hd.continuousOn
  have hcont_sphere : ContinuousOn g (Metric.sphere (0 : ℂ) R) :=
    hcont_closed.mono Metric.sphere_subset_closedBall
  rcases exists_norm_bound_on_sphere (g := g) (R := R) hcont_sphere with
    ⟨M, hM_nonneg, hM⟩
  have hcoeff : ∀ n : ℕ, ‖p.coeff n‖ ≤ M * R⁻¹ ^ n := by
    intro n
    exact norm_coeff_le_of_circleIntegral hR hp hd hM n
  refine isBigO_of_le' (l := atTop) (c := M) ?_
  intro n
  have hpow_nonneg : 0 ≤ R⁻¹ ^ n := pow_nonneg (inv_nonneg.mpr hR.le) n
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (p.coeff n)),
    abs_of_nonneg hpow_nonneg, abs_of_nonneg hR.le] using hcoeff n

/-- Radius form of the analytic-remainder estimate for a formal power series. -/
theorem coeff_norm_isBigO_of_radius
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {R : ℝ}
    (hR : 0 < R) (hRrad : ENNReal.ofReal R < p.radius) :
    (fun n : ℕ => ‖p.coeff n‖) =O[atTop] (fun n : ℕ => R⁻¹ ^ n) := by
  have hpos : 0 < p.radius :=
    (ENNReal.ofReal_pos.mpr hR).trans hRrad
  have hpball : HasFPowerSeriesOnBall p.sum p (0 : ℂ) p.radius :=
    FormalMultilinearSeries.hasFPowerSeriesOnBall p hpos
  have hd_eball : DifferentiableOn ℂ p.sum (Metric.eball (0 : ℂ) p.radius) :=
    hpball.differentiableOn
  have hd_closed : DifferentiableOn ℂ p.sum (Metric.closedBall (0 : ℂ) R) :=
    hd_eball.mono (closedBall_subset_eball_of_ofReal_lt_radius (p := p) hRrad)
  exact coeff_norm_isBigO_of_hasFPowerSeriesAt_differentiableOn hR
    hpball.hasFPowerSeriesAt hd_closed

/-- Radius form specialized to the project's `PowerSeries.toFMLS` bridge. -/
theorem powerSeries_coeff_norm_isBigO_of_radius
    (g : PowerSeries ℂ) {R : ℝ}
    (hR : 0 < R) (hRrad : ENNReal.ofReal R < (PowerSeries.toFMLS g).radius) :
    (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n g‖) =O[atTop]
      (fun n : ℕ => R⁻¹ ^ n) := by
  simpa using coeff_norm_isBigO_of_radius
    (p := PowerSeries.toFMLS g) hR hRrad

/-- If a power series is a finite simple-pole sum plus a remainder analytic past `R`, then the
coefficient error after subtracting the principal part is geometrically small. -/
theorem coeff_sub_principalPart_isBigO_of_remainder_radius
    (f S g : PowerSeries ℂ) {R : ℝ}
    (hR : 0 < R) (hgR : ENNReal.ofReal R < (PowerSeries.toFMLS g).radius)
    (hfg : f = S + g) :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n f -
      PowerSeries.coeff (R := ℂ) n S) =O[atTop] (fun n : ℕ => R⁻¹ ^ n) := by
  have hgO :
      (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n g‖) =O[atTop]
        (fun n : ℕ => R⁻¹ ^ n) :=
    powerSeries_coeff_norm_isBigO_of_radius g hR hgR
  have hgO_complex :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n g) =O[atTop]
        (fun n : ℕ => R⁻¹ ^ n) :=
    IsBigO.of_norm_left hgO
  have hcoeff :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n f -
        PowerSeries.coeff (R := ℂ) n S) =ᶠ[atTop]
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n g) := by
    exact Eventually.of_forall fun n => by
      rw [hfg]
      simp
  exact hcoeff.trans_isBigO hgO_complex

end Meromorphic
end Ch5
end AnalyticCombinatorics
end

open Complex Filter Asymptotics
open scoped ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic

namespace SupercriticalSeqGenuine

theorem principalFun_hasFPowerSeriesAt_zero
    {ρ c : ℂ} (hρ : 0 < ‖ρ‖) :
    HasFPowerSeriesAt (principalFun ρ c) (PowerSeries.toFMLS (principalSeries ρ c)) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hρ] with z hz
  have hz_norm : ‖z‖ < ‖ρ‖ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hρ_ne : ρ ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hρ)
  have hzr : ‖z * ρ⁻¹‖ < 1 := by
    rw [norm_mul, norm_inv]
    have hpos : 0 < ‖ρ‖⁻¹ := inv_pos.mpr hρ
    calc
      ‖z‖ * ‖ρ‖⁻¹ < ‖ρ‖ * ‖ρ‖⁻¹ :=
        mul_lt_mul_of_pos_right hz_norm hpos
      _ = 1 := by
        field_simp [ne_of_gt hρ]
  have hlin_ne : 1 - z * ρ⁻¹ ≠ 0 := by
    intro h
    have hzreq : z * ρ⁻¹ = 1 := (sub_eq_zero.mp h).symm
    have hnorm : ‖z * ρ⁻¹‖ = 1 := by
      rw [hzreq, norm_one]
    linarith
  have hrz_ne : ρ - z ≠ 0 := by
    intro h
    have hzrho : ρ = z := sub_eq_zero.mp h
    have hnorm : ‖z‖ = ‖ρ‖ := by
      rw [← hzrho]
    linarith
  have hsum :
      HasSum (fun n : ℕ => (c * ρ⁻¹) * (z * ρ⁻¹) ^ n)
        ((c * ρ⁻¹) * (1 - z * ρ⁻¹)⁻¹) :=
    (hasSum_geometric_of_norm_lt_one hzr).mul_left (c * ρ⁻¹)
  convert hsum using 1
  · ext n
    rw [PowerSeries.coeff_toFMLS]
    change z ^ n * PowerSeries.coeff (R := ℂ) n (principalSeries ρ c) =
      (c * ρ⁻¹) * (z * ρ⁻¹) ^ n
    rw [principalSeries, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale_invUnitsSub_one]
    rw [mul_pow]
    ring
  · simp [principalFun]
    field_simp [hρ_ne, hlin_ne, hrz_ne]

/-- If a `PowerSeries` represents a function that is differentiable on a larger closed disk of
radius `S`, then its convergence radius is strictly larger than every real `R < S`. -/
theorem powerSeries_radius_gt_of_hasFPowerSeriesAt_differentiableOn_larger
    (G : PowerSeries ℂ) {gfun : ℂ → ℂ} {R S : ℝ}
    (hS : 0 < S) (hRS : R < S)
    (hp : HasFPowerSeriesAt gfun (PowerSeries.toFMLS G) 0)
    (hd : DifferentiableOn ℂ gfun (Metric.closedBall (0 : ℂ) S)) :
    ENNReal.ofReal R < (PowerSeries.toFMLS G).radius := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ := PowerSeries.toFMLS G
  have hcoeffO :
      (fun n : ℕ => ‖p.coeff n‖) =O[atTop] (fun n : ℕ => S⁻¹ ^ n) :=
    coeff_norm_isBigO_of_hasFPowerSeriesAt_differentiableOn
      (g := gfun) (p := p) (R := S) hS hp hd
  have hcancel :
      (fun n : ℕ => (S⁻¹ ^ n) * S ^ n) =O[atTop]
        (fun _ : ℕ => (1 : ℝ)) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    have hpow : S⁻¹ ^ n * S ^ n = 1 := by
      rw [← mul_pow]
      field_simp [ne_of_gt hS]
      simp
    rw [hpow]
    norm_num
  have hcoeffMul :
      (fun n : ℕ => ‖p.coeff n‖ * S ^ n) =O[atTop]
        (fun _ : ℕ => (1 : ℝ)) := by
    exact (hcoeffO.mul (isBigO_refl (fun n : ℕ => S ^ n) atTop)).trans hcancel
  have hnorm_eq :
      (fun n : ℕ => ‖p n‖ * S ^ n) =ᶠ[atTop]
        (fun n : ℕ => ‖p.coeff n‖ * S ^ n) := by
    exact Eventually.of_forall fun n => by
      have hpn : ‖p n‖ = ‖p.coeff n‖ := by
        simp [p, PowerSeries.toFMLS]
      change ‖p n‖ * S ^ n = ‖p.coeff n‖ * S ^ n
      rw [hpn]
  have hterm :
      (fun n : ℕ => ‖p n‖ * S ^ n) =O[atTop]
        (fun _ : ℕ => (1 : ℝ)) :=
    hnorm_eq.trans_isBigO hcoeffMul
  have hle : ((Real.toNNReal S : ℝ≥0) : ℝ≥0∞) ≤ p.radius :=
    p.le_radius_of_isBigO (r := Real.toNNReal S) (by
      simpa [p, Real.coe_toNNReal _ hS.le] using hterm)
  have hRltS : ENNReal.ofReal R < ((Real.toNNReal S : ℝ≥0) : ℝ≥0∞) := by
    simpa [ENNReal.ofNNReal_toNNReal] using
      (ENNReal.ofReal_lt_ofReal_iff hS).mpr hRS
  exact hRltS.trans_le hle

end SupercriticalSeqGenuine
end Meromorphic
end Ch5
end AnalyticCombinatorics
end

open Complex Filter Asymptotics
open scoped ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic
namespace Tangent

namespace PowerSeries

@[simp] theorem coeff_ofFMLS (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (ofFMLS p) = p.coeff n := by
  simp [ofFMLS]

theorem toFMLS_ofFMLS (p : FormalMultilinearSeries ℂ ℂ ℂ) :
    PowerSeries.toFMLS (ofFMLS p) = p := by
  ext n
  rw [← FormalMultilinearSeries.mkPiRing_coeff_eq (PowerSeries.toFMLS (ofFMLS p)) n,
    ← FormalMultilinearSeries.mkPiRing_coeff_eq p n]
  simp

end PowerSeries

lemma toFMLS_add (f g : PowerSeries ℂ) :
    PowerSeries.toFMLS (f + g) = PowerSeries.toFMLS f + PowerSeries.toFMLS g := by
  ext n
  simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars]

lemma toFMLS_sub (f g : PowerSeries ℂ) :
    PowerSeries.toFMLS (f - g) = PowerSeries.toFMLS f - PowerSeries.toFMLS g := by
  ext n
  simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars]

lemma coeff_simplePolePrincipal (ρ c : ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (simplePolePrincipal ρ c) =
      c * ρ⁻¹ ^ (n + 1) := by
  rw [simplePolePrincipal, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_rescale_invUnitsSub_one]
  rw [pow_succ]
  ring

lemma rhoReal_pos : 0 < rhoReal := by
  rw [rhoReal]
  exact half_pos Real.pi_pos

lemma rho_norm : ‖rho‖ = rhoReal := by
  rw [rho]
  exact Complex.norm_of_nonneg rhoReal_pos.le

lemma rho_norm_pos : 0 < ‖rho‖ := by
  rw [rho_norm]
  exact rhoReal_pos

lemma rho_norm_lt_two : ‖rho‖ < (2 : ℝ) := by
  rw [rho_norm, rhoReal]
  nlinarith [Real.pi_lt_four]

theorem simplePolePrincipalFun_hasFPowerSeriesAt_zero
    {ρ c : ℂ} (hρ : 0 < ‖ρ‖) :
    HasFPowerSeriesAt (simplePolePrincipalFun ρ c)
      (PowerSeries.toFMLS (simplePolePrincipal ρ c)) (0 : ℂ) := by
  simpa [simplePolePrincipalFun, simplePolePrincipal,
    SupercriticalSeqGenuine.principalFun, SupercriticalSeqGenuine.principalSeries] using
    (SupercriticalSeqGenuine.principalFun_hasFPowerSeriesAt_zero
      (ρ := ρ) (c := c) hρ)

lemma sinDiv_zero : sinDiv 0 = 1 := by
  rw [sinDiv, dslope_same, Complex.deriv_sin]
  simp

lemma sinDiv_of_ne {z : ℂ} (hz : z ≠ 0) :
    sinDiv z = z⁻¹ * Complex.sin z := by
  rw [sinDiv, dslope_of_ne Complex.sin hz]
  simp [slope_def_module, smul_eq_mul]

private lemma analyticAt_dslope_zero {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f (0 : ℂ)) :
    AnalyticAt ℂ (dslope f 0) (0 : ℂ) := by
  rcases hf with ⟨p, hp⟩
  exact ⟨p.fslope, by simpa using hp.has_fpower_series_dslope_fslope⟩

lemma sinDiv_analyticAt_zero : AnalyticAt ℂ sinDiv (0 : ℂ) := by
  have hsin : AnalyticAt ℂ Complex.sin (0 : ℂ) :=
    (Complex.contDiff_sin (n := (⊤ : WithTop ℕ∞))).contDiffAt.analyticAt
  simpa [sinDiv] using analyticAt_dslope_zero hsin

private lemma abs_int_cast_lt_three_of_norm_cos_zero_le_three
    {z : ℂ} (hz_norm : ‖z‖ ≤ 3) (hcos : Complex.cos z = 0) :
    ∃ k : ℤ, z = ((2 * k + 1 : ℤ) : ℂ) * ((Real.pi : ℝ) : ℂ) / 2 ∧
      |(((2 * k + 1 : ℤ) : ℝ))| < 3 := by
  rcases Complex.cos_eq_zero_iff.mp hcos with ⟨k, hk⟩
  have hk' : z = ((2 * k + 1 : ℤ) : ℂ) * ((Real.pi : ℝ) : ℂ) / 2 := by
    simpa using hk
  refine ⟨k, hk', ?_⟩
  have hnorm_eq :
      ‖(((2 * k + 1 : ℤ) : ℂ) * ((Real.pi : ℝ) : ℂ) / 2)‖ =
        |(((2 * k + 1 : ℤ) : ℝ))| * Real.pi / 2 := by
    have hint :
        ‖(((2 * k + 1 : ℤ) : ℂ))‖ =
          |(((2 * k + 1 : ℤ) : ℝ))| := by
      simpa using (RCLike.norm_ofReal (K := ℂ) (((2 * k + 1 : ℤ) : ℝ)))
    have hpi : ‖(((Real.pi : ℝ) : ℂ))‖ = Real.pi := by
      simp [abs_of_pos Real.pi_pos]
    have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
    rw [norm_div, norm_mul, hint, hpi, htwo]
  have hle : |(((2 * k + 1 : ℤ) : ℝ))| * Real.pi / 2 ≤ 3 := by
    have hle0 :
        ‖(((2 * k + 1 : ℤ) : ℂ) * ((Real.pi : ℝ) : ℂ) / 2)‖ ≤ 3 := by
      simpa [hk'] using hz_norm
    rw [hnorm_eq] at hle0
    exact hle0
  by_contra hnot
  have hge : 3 ≤ |(((2 * k + 1 : ℤ) : ℝ))| := le_of_not_gt hnot
  have hbig : 3 < |(((2 * k + 1 : ℤ) : ℝ))| * Real.pi / 2 := by
    nlinarith [Real.pi_gt_three]
  linarith

lemma eq_pm_rho_of_cos_eq_zero_of_norm_le_three {z : ℂ}
    (hz_norm : ‖z‖ ≤ 3) (hcos : Complex.cos z = 0) :
    z = rho ∨ z = -rho := by
  rcases abs_int_cast_lt_three_of_norm_cos_zero_le_three hz_norm hcos with
    ⟨k, hkz, habs⟩
  have hlt : (2 * k + 1 : ℤ) < 3 := by
    have hreal : (((2 * k + 1 : ℤ) : ℝ)) < 3 :=
      (le_abs_self _).trans_lt habs
    exact_mod_cast hreal
  have hgt : -(3 : ℤ) < (2 * k + 1 : ℤ) := by
    have hreal : (-(3 : ℝ)) < (((2 * k + 1 : ℤ) : ℝ)) := by
      have hneg_le : -(((2 * k + 1 : ℤ) : ℝ)) ≤
          |(((2 * k + 1 : ℤ) : ℝ))| := neg_le_abs _
      linarith
    exact_mod_cast hreal
  have hkodd : (2 * k + 1 : ℤ) = -1 ∨ (2 * k + 1 : ℤ) = 1 := by
    omega
  rcases hkodd with hkodd | hkodd
  · right
    rw [hkz, hkodd]
    simp [rho, rhoReal]
    ring
  · left
    rw [hkz, hkodd]
    simp [rho, rhoReal]

lemma Complex_ofReal_rho_inv_eq_two_div_pi :
    rho⁻¹ = (((2 / Real.pi : ℝ) : ℂ)) := by
  rw [rho, rhoReal]
  norm_num [Complex.ofReal_inv]

end Tangent
end Meromorphic
end Ch5
end AnalyticCombinatorics
end

open Complex Filter Asymptotics
open scoped ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic
namespace Secant

lemma rho_norm_pos : 0 < ‖rho‖ :=
  Tangent.rho_norm_pos

lemma rho_norm_lt_two : ‖rho‖ < (2 : ℝ) :=
  Tangent.rho_norm_lt_two

lemma one_ne_zero_complex : (1 : ℂ) ≠ 0 :=
  one_ne_zero

lemma coeff_oppositeTwoPolePrincipal (ρ c : ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (oppositeTwoPolePrincipal ρ c) =
      c * ρ⁻¹ ^ (n + 1) - c * (-ρ)⁻¹ ^ (n + 1) := by
  simp [oppositeTwoPolePrincipal, Tangent.coeff_simplePolePrincipal]
  ring

lemma neg_inv_pow_odd (ρ : ℂ) (k : ℕ) :
    (-ρ)⁻¹ ^ (2 * k + 1) = -ρ⁻¹ ^ (2 * k + 1) := by
  rw [inv_neg]
  have hOdd : Odd (2 * k + 1) := odd_two_mul_add_one k
  exact hOdd.neg_pow ρ⁻¹

lemma coeff_oppositeTwoPolePrincipal_even (ρ c : ℂ) (k : ℕ) :
    PowerSeries.coeff (R := ℂ) (2 * k) (oppositeTwoPolePrincipal ρ c) =
      2 * c * ρ⁻¹ ^ (2 * k + 1) := by
  rw [coeff_oppositeTwoPolePrincipal, neg_inv_pow_odd]
  ring

private lemma tendsto_two_mul_atTop :
    Tendsto (fun k : ℕ => 2 * k) atTop atTop := by
  simpa [nsmul_eq_mul] using
    ((tendsto_id : Tendsto (fun k : ℕ => k) atTop atTop).nsmul_atTop
      (by norm_num : 0 < 2))

private lemma inv_lt_inv_of_pos_lt {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    y⁻¹ < x⁻¹ := by
  simpa [one_div] using one_div_lt_one_div_of_lt hx hxy

private lemma inv_radius_pow_isLittleO_oppositeTwoPole_even
    {ρ c : ℂ} {R : ℝ}
    (hρ : 0 < ‖ρ‖) (hρR : ‖ρ‖ < R) (hc : c ≠ 0) :
    (fun k : ℕ => R⁻¹ ^ (2 * k) : ℕ → ℝ) =o[atTop]
      (fun k : ℕ => 2 * c * ρ⁻¹ ^ (2 * k + 1)) := by
  have hR : 0 < R := hρ.trans hρR
  have hinv_lt : R⁻¹ < ‖ρ‖⁻¹ :=
    inv_lt_inv_of_pos_lt hρ hρR
  have hpowLittle :
      (fun n : ℕ => R⁻¹ ^ n : ℕ → ℝ) =o[atTop]
        (fun n : ℕ => ‖ρ‖⁻¹ ^ n : ℕ → ℝ) :=
    isLittleO_pow_pow_of_lt_left (inv_nonneg.mpr hR.le) hinv_lt
  have hpowLittleEven :
      (fun k : ℕ => R⁻¹ ^ (2 * k) : ℕ → ℝ) =o[atTop]
        (fun k : ℕ => ‖ρ‖⁻¹ ^ (2 * k) : ℕ → ℝ) :=
    hpowLittle.comp_tendsto tendsto_two_mul_atTop
  have hmainO :
      (fun k : ℕ => ‖ρ‖⁻¹ ^ (2 * k) : ℕ → ℝ) =O[atTop]
        (fun k : ℕ => 2 * c * ρ⁻¹ ^ (2 * k + 1)) := by
    have hcnorm : ‖2 * c‖ ≠ 0 := by
      rw [norm_ne_zero_iff]
      exact mul_ne_zero (by norm_num) hc
    have hρnorm : ‖ρ‖ ≠ 0 := ne_of_gt hρ
    have hρinv : ‖ρ‖⁻¹ ≠ 0 := inv_ne_zero hρnorm
    refine isBigO_of_le' (l := atTop) (c := (‖2 * c‖ * ‖ρ‖⁻¹)⁻¹) ?_
    intro k
    have hbase_nonneg : 0 ≤ ‖ρ‖⁻¹ := inv_nonneg.mpr (norm_nonneg ρ)
    have hpow_nonneg : 0 ≤ ‖ρ‖⁻¹ ^ (2 * k) :=
      pow_nonneg hbase_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg]
    apply le_of_eq
    have hnorm_main :
        ‖2 * c * ρ⁻¹ ^ (2 * k + 1)‖ =
          ‖2 * c‖ * ‖ρ‖⁻¹ ^ (2 * k + 1) := by
      rw [norm_mul, norm_pow, norm_inv]
    calc
      ‖ρ‖⁻¹ ^ (2 * k) =
          (‖2 * c‖ * ‖ρ‖⁻¹)⁻¹ *
            (‖2 * c‖ * (‖ρ‖⁻¹ ^ (2 * k + 1))) := by
        rw [show 2 * k + 1 = 2 * k + 1 by rfl, pow_succ]
        field_simp [hcnorm, hρnorm, hρinv]
      _ = (‖2 * c‖ * ‖ρ‖⁻¹)⁻¹ *
            ‖2 * c * ρ⁻¹ ^ (2 * k + 1)‖ := by rw [hnorm_main]
  exact hpowLittleEven.trans_isBigO hmainO

/-- Two opposite dominant simple poles transfer, restricted to even indices. -/
theorem oppositeTwoDominantSimplePole_isEquivalent_even
    (f g : PowerSeries ℂ) {ρ c : ℂ} {R : ℝ}
    (hρ : 0 < ‖ρ‖) (hρR : ‖ρ‖ < R) (hc : c ≠ 0)
    (hgR : ENNReal.ofReal R < (PowerSeries.toFMLS g).radius)
    (hfg : f = oppositeTwoPolePrincipal ρ c + g) :
    (fun k : ℕ => PowerSeries.coeff (R := ℂ) (2 * k) f) ~[atTop]
      (fun k : ℕ => 2 * c * ρ⁻¹ ^ (2 * k + 1)) := by
  let S : PowerSeries ℂ := oppositeTwoPolePrincipal ρ c
  have hR : 0 < R := hρ.trans hρR
  have hremO :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n f -
        PowerSeries.coeff (R := ℂ) n S) =O[atTop] (fun n : ℕ => R⁻¹ ^ n) :=
    coeff_sub_principalPart_isBigO_of_remainder_radius f S g hR hgR (by simpa [S] using hfg)
  have hremOEven :
      (fun k : ℕ => PowerSeries.coeff (R := ℂ) (2 * k) f -
        PowerSeries.coeff (R := ℂ) (2 * k) S) =O[atTop]
        (fun k : ℕ => R⁻¹ ^ (2 * k)) :=
    hremO.comp_tendsto tendsto_two_mul_atTop
  have hgeom :
      (fun k : ℕ => R⁻¹ ^ (2 * k) : ℕ → ℝ) =o[atTop]
        (fun k : ℕ => 2 * c * ρ⁻¹ ^ (2 * k + 1)) :=
    inv_radius_pow_isLittleO_oppositeTwoPole_even hρ hρR hc
  have hremLittle :
      (fun k : ℕ => PowerSeries.coeff (R := ℂ) (2 * k) f -
        PowerSeries.coeff (R := ℂ) (2 * k) S) =o[atTop]
        (fun k : ℕ => 2 * c * ρ⁻¹ ^ (2 * k + 1)) :=
    hremOEven.trans_isLittleO hgeom
  have hS :
      (fun k : ℕ => PowerSeries.coeff (R := ℂ) (2 * k) S) ~[atTop]
        (fun k : ℕ => 2 * c * ρ⁻¹ ^ (2 * k + 1)) := by
    apply Filter.EventuallyEq.isEquivalent
    exact Eventually.of_forall fun k => by
      simpa [S] using coeff_oppositeTwoPolePrincipal_even (ρ := ρ) (c := c) k
  have hsum :
      (fun k : ℕ => PowerSeries.coeff (R := ℂ) (2 * k) S +
        (PowerSeries.coeff (R := ℂ) (2 * k) f -
          PowerSeries.coeff (R := ℂ) (2 * k) S)) ~[atTop]
        (fun k : ℕ => 2 * c * ρ⁻¹ ^ (2 * k + 1)) :=
    hS.add_isLittleO hremLittle
  exact hsum.congr_left (Eventually.of_forall fun k => by ring)

theorem secantEGFℂ_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt (fun z : ℂ => (Complex.cos z)⁻¹)
      (PowerSeries.toFMLS secantEGFℂ) (0 : ℂ) := by
  rw [secantEGFℂ, Tangent.PowerSeries.toFMLS_ofFMLS]
  exact Classical.choose_spec sec_analyticAt_zero

lemma secantNumber_div_factorial (n : ℕ) :
    secantNumber n / (n.factorial : ℝ) =
      (PowerSeries.coeff (R := ℂ) n secantEGFℂ).re := by
  rw [secantNumber]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]

lemma secantEGFℂ_eq_oppositeTwoPolePrincipal_add_remainder :
    secantEGFℂ = oppositeTwoPolePrincipal rho (1 : ℂ) + secantRemainder := by
  rw [secantRemainder]
  abel

theorem oppositeTwoPolePrincipalFun_hasFPowerSeriesAt_zero
    {ρ c : ℂ} (hρ : 0 < ‖ρ‖) :
    HasFPowerSeriesAt (oppositeTwoPolePrincipalFun ρ c)
      (PowerSeries.toFMLS (oppositeTwoPolePrincipal ρ c)) (0 : ℂ) := by
  have hpos :
      HasFPowerSeriesAt (Tangent.simplePolePrincipalFun ρ c)
        (PowerSeries.toFMLS (Tangent.simplePolePrincipal ρ c)) (0 : ℂ) :=
    Tangent.simplePolePrincipalFun_hasFPowerSeriesAt_zero (ρ := ρ) (c := c) hρ
  have hneg :
      HasFPowerSeriesAt (Tangent.simplePolePrincipalFun (-ρ) (-c))
        (PowerSeries.toFMLS (Tangent.simplePolePrincipal (-ρ) (-c))) (0 : ℂ) :=
    Tangent.simplePolePrincipalFun_hasFPowerSeriesAt_zero (ρ := -ρ) (c := -c) (by
      simpa using hρ)
  simpa [oppositeTwoPolePrincipalFun, oppositeTwoPolePrincipal, Tangent.toFMLS_add] using
    hpos.add hneg

lemma oppositeTwoPolePrincipalFun_one_eq (z : ℂ) :
    oppositeTwoPolePrincipalFun rho (1 : ℂ) z =
      (rho - z)⁻¹ + (z + rho)⁻¹ := by
  have hneg_inv : (-rho - z)⁻¹ = - (z + rho)⁻¹ := by
    have h : -rho - z = -(z + rho) := by ring
    rw [h, inv_neg]
  simp [oppositeTwoPolePrincipalFun, Tangent.simplePolePrincipalFun, hneg_inv]

lemma secRemRaw_eq_sec_sub_oppositeTwoPolePrincipalFun (z : ℂ) :
    secRemRaw z =
      (Complex.cos z)⁻¹ - oppositeTwoPolePrincipalFun rho (1 : ℂ) z := by
  rw [oppositeTwoPolePrincipalFun_one_eq]
  simp [secRemRaw]
  ring

theorem secRemRaw_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt secRemRaw (PowerSeries.toFMLS secantRemainder) (0 : ℂ) := by
  have hprincipal :
      HasFPowerSeriesAt (oppositeTwoPolePrincipalFun rho (1 : ℂ))
        (PowerSeries.toFMLS (oppositeTwoPolePrincipal rho (1 : ℂ))) (0 : ℂ) :=
    oppositeTwoPolePrincipalFun_hasFPowerSeriesAt_zero (ρ := rho) (c := (1 : ℂ)) rho_norm_pos
  have hsub := secantEGFℂ_hasFPowerSeriesAt_zero.sub hprincipal
  have hsub' :
      HasFPowerSeriesAt
        (fun z : ℂ => (Complex.cos z)⁻¹ - oppositeTwoPolePrincipalFun rho (1 : ℂ) z)
        (PowerSeries.toFMLS secantRemainder) (0 : ℂ) := by
    simpa [secantRemainder, Tangent.toFMLS_sub] using hsub
  exact hsub'.congr (Eventually.of_forall fun z => by
    exact (secRemRaw_eq_sec_sub_oppositeTwoPolePrincipalFun z).symm)

private lemma analyticAt_dslope_zero {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f (0 : ℂ)) :
    AnalyticAt ℂ (dslope f 0) (0 : ℂ) := by
  rcases hf with ⟨p, hp⟩
  exact ⟨p.fslope, by simpa using hp.has_fpower_series_dslope_fslope⟩

lemma secPoleCore_analyticAt_zero :
    AnalyticAt ℂ secPoleCore (0 : ℂ) := by
  have hsinDiv : AnalyticAt ℂ Tangent.sinDiv (0 : ℂ) :=
    Tangent.sinDiv_analyticAt_zero
  have hne : Tangent.sinDiv 0 ≠ 0 := by
    rw [Tangent.sinDiv_zero]
    norm_num
  have hinv : AnalyticAt ℂ (fun u : ℂ => (Tangent.sinDiv u)⁻¹) (0 : ℂ) :=
    hsinDiv.inv hne
  simpa [secPoleCore] using analyticAt_dslope_zero hinv

lemma secPoleCore_eq_inv_sinDiv_sub_inv {w : ℂ} (hw : w ≠ 0) :
    secPoleCore w = w⁻¹ * ((Tangent.sinDiv w)⁻¹ - 1) := by
  rw [secPoleCore, dslope_of_ne (fun u : ℂ => (Tangent.sinDiv u)⁻¹) hw,
    slope_def_module, Tangent.sinDiv_zero]
  simp [smul_eq_mul]

lemma cos_eq_mul_sinDiv_pos {z : ℂ} (hz : z ≠ rho) :
    Complex.cos z = (rho - z) * Tangent.sinDiv (rho - z) := by
  have hw : rho - z ≠ 0 := by
    intro h
    exact hz (eq_of_sub_eq_zero h).symm
  have hcos : Complex.cos z = Complex.sin (rho - z) := by
    have hzsplit : z = rho - (rho - z) := by ring
    have hrewrite : Complex.cos z = Complex.cos (rho - (rho - z)) :=
      congrArg Complex.cos hzsplit
    have htrig : Complex.cos (rho - (rho - z)) = Complex.sin (rho - z) := by
      simpa [rho, rhoReal, Tangent.rho, Tangent.rhoReal] using
        Complex.cos_pi_div_two_sub (rho - z)
    exact hrewrite.trans htrig
  have hsin : Complex.sin (rho - z) = (rho - z) * Tangent.sinDiv (rho - z) := by
    rw [Tangent.sinDiv_of_ne hw]
    field_simp [hw]
  rw [hcos, hsin]

lemma cos_eq_mul_sinDiv_neg {z : ℂ} (hz : z ≠ -rho) :
    Complex.cos z = (z + rho) * Tangent.sinDiv (z + rho) := by
  have hw : z + rho ≠ 0 := by
    intro h
    exact hz (eq_neg_of_add_eq_zero_left h)
  have hcos : Complex.cos z = Complex.sin (z + rho) := by
    have hzsplit : z = -(rho - (z + rho)) := by ring
    have hrewrite : Complex.cos z = Complex.cos (-(rho - (z + rho))) :=
      congrArg Complex.cos hzsplit
    have hneg : Complex.cos (-(rho - (z + rho))) = Complex.cos (rho - (z + rho)) := by
      rw [Complex.cos_neg]
    have htrig : Complex.cos (rho - (z + rho)) = Complex.sin (z + rho) := by
      simpa [rho, rhoReal, Tangent.rho, Tangent.rhoReal] using
        Complex.cos_pi_div_two_sub (z + rho)
    exact hrewrite.trans (hneg.trans htrig)
  have hsin : Complex.sin (z + rho) = (z + rho) * Tangent.sinDiv (z + rho) := by
    rw [Tangent.sinDiv_of_ne hw]
    field_simp [hw]
  rw [hcos, hsin]

lemma secRemRaw_eq_secRemLocalPos {z : ℂ}
    (hz : z ≠ rho) (hdiv : Tangent.sinDiv (rho - z) ≠ 0) :
    secRemRaw z = secRemLocalPos z := by
  have hw : rho - z ≠ 0 := by
    intro h
    exact hz (eq_of_sub_eq_zero h).symm
  rw [secRemRaw, secRemLocalPos, cos_eq_mul_sinDiv_pos hz,
    secPoleCore_eq_inv_sinDiv_sub_inv hw]
  field_simp [hw, hdiv]

lemma secRemRaw_eq_secRemLocalNeg {z : ℂ}
    (hz : z ≠ -rho) (hdiv : Tangent.sinDiv (z + rho) ≠ 0) :
    secRemRaw z = secRemLocalNeg z := by
  have hw : z + rho ≠ 0 := by
    intro h
    exact hz (eq_neg_of_add_eq_zero_left h)
  rw [secRemRaw, secRemLocalNeg, cos_eq_mul_sinDiv_neg hz,
    secPoleCore_eq_inv_sinDiv_sub_inv hw]
  field_simp [hw, hdiv]
  ring

lemma secRemLocalPos_analyticAt_rho :
    AnalyticAt ℂ secRemLocalPos rho := by
  have hshift : AnalyticAt ℂ (fun z : ℂ => rho - z) rho :=
    (analyticAt_const (𝕜 := ℂ) (v := rho) (x := rho)).sub analyticAt_id
  have hcore : AnalyticAt ℂ (fun z : ℂ => secPoleCore (rho - z)) rho :=
    AnalyticAt.comp' (𝕜 := ℂ) (g := secPoleCore) (f := fun z : ℂ => rho - z)
      (x := rho) (by simpa using secPoleCore_analyticAt_zero) hshift
  have hinv_ne : rho + rho ≠ 0 := by
    intro h
    have hmul : (2 : ℂ) * rho = 0 := by
      simpa [two_mul] using h
    have hzero : rho = 0 := by
      rcases mul_eq_zero.mp hmul with htwo | hrho
      · exact (False.elim ((by norm_num : (2 : ℂ) ≠ 0) htwo))
      · exact hrho
    exact (norm_ne_zero_iff.mp (ne_of_gt rho_norm_pos)) hzero
  have hinv : AnalyticAt ℂ (fun z : ℂ => (z + rho)⁻¹) rho :=
    (analyticAt_id.add (analyticAt_const (𝕜 := ℂ) (v := rho) (x := rho))).inv hinv_ne
  simpa [secRemLocalPos] using hcore.sub hinv

lemma secRemLocalNeg_analyticAt_neg_rho :
    AnalyticAt ℂ secRemLocalNeg (-rho) := by
  have hshift : AnalyticAt ℂ (fun z : ℂ => z + rho) (-rho) :=
    analyticAt_id.add (analyticAt_const (𝕜 := ℂ) (v := rho) (x := -rho))
  have hcore : AnalyticAt ℂ (fun z : ℂ => secPoleCore (z + rho)) (-rho) :=
    AnalyticAt.comp' (𝕜 := ℂ) (g := secPoleCore) (f := fun z : ℂ => z + rho)
      (x := -rho) (by simpa using secPoleCore_analyticAt_zero) hshift
  have hinv_ne : rho - (-rho) ≠ 0 := by
    intro h
    have hmul : (2 : ℂ) * rho = 0 := by
      simpa [two_mul] using h
    have hzero : rho = 0 := by
      rcases mul_eq_zero.mp hmul with htwo | hrho
      · exact (False.elim ((by norm_num : (2 : ℂ) ≠ 0) htwo))
      · exact hrho
    exact (norm_ne_zero_iff.mp (ne_of_gt rho_norm_pos)) hzero
  have hinv : AnalyticAt ℂ (fun z : ℂ => (rho - z)⁻¹) (-rho) :=
    ((analyticAt_const (𝕜 := ℂ) (v := rho) (x := -rho)).sub analyticAt_id).inv hinv_ne
  simpa [secRemLocalNeg] using hcore.sub hinv

lemma secantRemainderFun_eventually_eq_secRemRaw_at_zero :
    secRemRaw =ᶠ[𝓝 (0 : ℂ)] secantRemainderFun := by
  have h0rho : (0 : ℂ) ≠ rho := by
    intro h
    have hnorm : ‖rho‖ = 0 := by
      rw [h.symm]
      simp
    exact ne_of_gt rho_norm_pos hnorm
  have h0negrho : (0 : ℂ) ≠ -rho := by
    intro h
    have hnorm : ‖rho‖ = 0 := by
      rw [← norm_neg rho, h.symm]
      simp
    exact ne_of_gt rho_norm_pos hnorm
  filter_upwards [isOpen_ne.mem_nhds h0rho, isOpen_ne.mem_nhds h0negrho] with z hzρ hznegρ
  simp [secantRemainderFun, hzρ, hznegρ]

theorem secantRemainderFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt secantRemainderFun (PowerSeries.toFMLS secantRemainder) (0 : ℂ) :=
  secRemRaw_hasFPowerSeriesAt_zero.congr secantRemainderFun_eventually_eq_secRemRaw_at_zero

lemma secantRemainderFun_eventually_eq_localPos_at_rho :
    secantRemainderFun =ᶠ[𝓝 rho] secRemLocalPos := by
  have hdiv_event :
      ∀ᶠ z in 𝓝 rho, Tangent.sinDiv (rho - z) ≠ 0 := by
    have hshift : ContinuousAt (fun z : ℂ => rho - z) rho :=
      ((continuous_const.sub continuous_id).continuousAt)
    have hcont : ContinuousAt (fun z : ℂ => Tangent.sinDiv (rho - z)) rho := by
      have hcomp :=
        Tangent.sinDiv_analyticAt_zero.continuousAt.comp_of_eq hshift (by simp)
      simpa [Function.comp_def] using hcomp
    have hne : Tangent.sinDiv (rho - rho) ≠ 0 := by
      simp [Tangent.sinDiv_zero]
    exact hcont.eventually_ne hne
  have hne_neg : ∀ᶠ z in 𝓝 rho, z ≠ -rho := by
    have h : rho ≠ -rho := by
      intro hr
      have hmul : (2 : ℂ) * rho = 0 := by
        have hsub : rho - (-rho) = 0 := by
          rw [← hr, sub_self]
        simpa [two_mul, sub_eq_add_neg] using hsub
      have hzero : rho = 0 := by
        rcases mul_eq_zero.mp hmul with htwo | hrho
        · exact (False.elim ((by norm_num : (2 : ℂ) ≠ 0) htwo))
        · exact hrho
      exact (norm_ne_zero_iff.mp (ne_of_gt rho_norm_pos)) hzero
    exact isOpen_ne.mem_nhds h
  filter_upwards [hdiv_event, hne_neg] with z hdiv hne_neg
  by_cases hz : z = rho
  · simp [secantRemainderFun, secRemLocalPos, hz]
  · simp [secantRemainderFun, hz, hne_neg, secRemRaw_eq_secRemLocalPos hz hdiv]

lemma secantRemainderFun_eventually_eq_localNeg_at_neg_rho :
    secantRemainderFun =ᶠ[𝓝 (-rho)] secRemLocalNeg := by
  have hdiv_event :
      ∀ᶠ z in 𝓝 (-rho), Tangent.sinDiv (z + rho) ≠ 0 := by
    have hshift : ContinuousAt (fun z : ℂ => z + rho) (-rho) :=
      ((continuous_id.add continuous_const).continuousAt)
    have hcont : ContinuousAt (fun z : ℂ => Tangent.sinDiv (z + rho)) (-rho) := by
      have hcomp :=
        Tangent.sinDiv_analyticAt_zero.continuousAt.comp_of_eq hshift (by simp)
      simpa [Function.comp_def] using hcomp
    have hne : Tangent.sinDiv ((-rho) + rho) ≠ 0 := by
      simp [Tangent.sinDiv_zero]
    exact hcont.eventually_ne hne
  have hne_pos : ∀ᶠ z in 𝓝 (-rho), z ≠ rho := by
    have h : -rho ≠ rho := by
      intro hr
      have hmul : (2 : ℂ) * rho = 0 := by
        have hsub : rho - (-rho) = 0 := by
          rw [hr, sub_self]
        simpa [two_mul, sub_eq_add_neg] using hsub
      have hzero : rho = 0 := by
        rcases mul_eq_zero.mp hmul with htwo | hrho
        · exact (False.elim ((by norm_num : (2 : ℂ) ≠ 0) htwo))
        · exact hrho
      exact (norm_ne_zero_iff.mp (ne_of_gt rho_norm_pos)) hzero
    exact isOpen_ne.mem_nhds h
  filter_upwards [hdiv_event, hne_pos] with z hdiv hne_pos
  by_cases hz : z = -rho
  · have hne_pos' : -rho ≠ rho := by simpa [hz] using hne_pos
    simp [secantRemainderFun, secRemLocalNeg, hz, hne_pos']
  · simp [secantRemainderFun, hne_pos, hz, secRemRaw_eq_secRemLocalNeg hz hdiv]

lemma secRemRaw_analyticAt_of_not_poles {z : ℂ}
    (hcos : Complex.cos z ≠ 0) (hpos : z ≠ rho) (hneg : z ≠ -rho) :
    AnalyticAt ℂ secRemRaw z := by
  have hsec : AnalyticAt ℂ (fun w : ℂ => (Complex.cos w)⁻¹) z :=
    ((Complex.contDiff_cos (n := (⊤ : WithTop ℕ∞))).contDiffAt.analyticAt).inv hcos
  have hpos_den : rho - z ≠ 0 := by
    intro h
    exact hpos (eq_of_sub_eq_zero h).symm
  have hneg_den : z + rho ≠ 0 := by
    intro h
    exact hneg (eq_neg_of_add_eq_zero_left h)
  have hpos_inv : AnalyticAt ℂ (fun w : ℂ => (rho - w)⁻¹) z :=
    ((analyticAt_const (𝕜 := ℂ) (v := rho) (x := z)).sub analyticAt_id).inv hpos_den
  have hneg_inv : AnalyticAt ℂ (fun w : ℂ => (w + rho)⁻¹) z :=
    (analyticAt_id.add (analyticAt_const (𝕜 := ℂ) (v := rho) (x := z))).inv hneg_den
  simpa [secRemRaw] using (hsec.sub hpos_inv).sub hneg_inv

theorem secantRemainderFun_analyticAt_on_closedBall_three {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) (3 : ℝ)) :
    AnalyticAt ℂ secantRemainderFun z := by
  by_cases hpos : z = rho
  · subst z
    exact secRemLocalPos_analyticAt_rho.congr
      secantRemainderFun_eventually_eq_localPos_at_rho.symm
  · by_cases hneg : z = -rho
    · subst z
      exact secRemLocalNeg_analyticAt_neg_rho.congr
        secantRemainderFun_eventually_eq_localNeg_at_neg_rho.symm
    · have hz_norm : ‖z‖ ≤ 3 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hz
      have hcos : Complex.cos z ≠ 0 := by
        intro hzero
        rcases Tangent.eq_pm_rho_of_cos_eq_zero_of_norm_le_three hz_norm hzero with hzrho | hznegrho
        · exact hpos hzrho
        · exact hneg hznegrho
      have hraw : AnalyticAt ℂ secRemRaw z :=
        secRemRaw_analyticAt_of_not_poles hcos hpos hneg
      refine hraw.congr ?_
      filter_upwards [isOpen_ne.mem_nhds hpos, isOpen_ne.mem_nhds hneg] with w hwpos hwneg
      simp [secantRemainderFun, hwpos, hwneg]

theorem secantRemainderFun_differentiableOn_closedBall_three :
    DifferentiableOn ℂ secantRemainderFun (Metric.closedBall (0 : ℂ) (3 : ℝ)) := by
  intro z hz
  exact (secantRemainderFun_analyticAt_on_closedBall_three hz).differentiableAt.differentiableWithinAt

theorem secantRemainder_radius_gt_two :
    ENNReal.ofReal (2 : ℝ) < (PowerSeries.toFMLS secantRemainder).radius := by
  exact
    SupercriticalSeqGenuine.powerSeries_radius_gt_of_hasFPowerSeriesAt_differentiableOn_larger
      (G := secantRemainder) (gfun := secantRemainderFun) (R := (2 : ℝ)) (S := (3 : ℝ))
      (by norm_num) (by norm_num) secantRemainderFun_hasFPowerSeriesAt_zero
      secantRemainderFun_differentiableOn_closedBall_three

theorem coeff_secantEGFℂ_even_isEquivalent_of_remainder_radius
    (hrem : ENNReal.ofReal (2 : ℝ) < (PowerSeries.toFMLS secantRemainder).radius) :
    (fun k : ℕ => PowerSeries.coeff (R := ℂ) (2 * k) secantEGFℂ) ~[atTop]
      (fun k : ℕ => 2 * (1 : ℂ) * rho⁻¹ ^ (2 * k + 1)) := by
  exact oppositeTwoDominantSimplePole_isEquivalent_even
    secantEGFℂ secantRemainder (ρ := rho) (c := (1 : ℂ)) (R := (2 : ℝ))
    rho_norm_pos rho_norm_lt_two one_ne_zero_complex hrem
    secantEGFℂ_eq_oppositeTwoPolePrincipal_add_remainder

lemma Complex_ofReal_rho_inv_eq_two_div_pi :
    rho⁻¹ = (((2 / Real.pi : ℝ) : ℂ)) := by
  simpa [rho] using Tangent.Complex_ofReal_rho_inv_eq_two_div_pi

private lemma complex_re_isEquivalent_of_ofReal_right {f : ℕ → ℂ} {g : ℕ → ℝ}
    (h : f ~[atTop] fun n => (g n : ℂ)) :
    (fun n => (f n).re) ~[atTop] g := by
  rw [Asymptotics.IsEquivalent] at h ⊢
  rw [Asymptotics.isLittleO_iff] at h ⊢
  intro c hc
  specialize h hc
  filter_upwards [h] with n hn
  have hle : ‖(f n).re - g n‖ ≤ ‖f n - (g n : ℂ)‖ := by
    simpa [Pi.sub_apply, Complex.sub_re] using Complex.abs_re_le_norm (f n - (g n : ℂ))
  exact hle.trans (by simpa [Pi.sub_apply, Complex.norm_real] using hn)

theorem coeff_secantEGFℂ_even_re_isEquivalent_two_div_pi
    (hrem : ENNReal.ofReal (2 : ℝ) < (PowerSeries.toFMLS secantRemainder).radius) :
    (fun k : ℕ => (PowerSeries.coeff (R := ℂ) (2 * k) secantEGFℂ).re)
      ~[atTop]
    (fun k : ℕ => 2 * (2 / Real.pi) ^ (2 * k + 1)) := by
  have h := coeff_secantEGFℂ_even_isEquivalent_of_remainder_radius hrem
  have h' :
      (fun k : ℕ => PowerSeries.coeff (R := ℂ) (2 * k) secantEGFℂ)
        ~[atTop]
      (fun k : ℕ => ((2 * (2 / Real.pi) ^ (2 * k + 1) : ℝ) : ℂ)) := by
    refine h.trans_eventuallyEq (Eventually.of_forall fun k => ?_)
    rw [Complex_ofReal_rho_inv_eq_two_div_pi]
    norm_num [Complex.ofReal_pow]
  exact complex_re_isEquivalent_of_ofReal_right h'

theorem secantNumber_div_factorial_even_isEquivalent_two_div_pi
    (hrem : ENNReal.ofReal (2 : ℝ) < (PowerSeries.toFMLS secantRemainder).radius) :
    (fun k : ℕ => secantNumber (2 * k) / ((2 * k).factorial : ℝ))
      ~[atTop]
    (fun k : ℕ => 2 * (2 / Real.pi) ^ (2 * k + 1)) := by
  have hbridge :
      (fun k : ℕ => secantNumber (2 * k) / ((2 * k).factorial : ℝ))
        =ᶠ[atTop]
      (fun k : ℕ => (PowerSeries.coeff (R := ℂ) (2 * k) secantEGFℂ).re) :=
    Eventually.of_forall fun k => secantNumber_div_factorial (2 * k)
  exact hbridge.trans_isEquivalent
    (coeff_secantEGFℂ_even_re_isEquivalent_two_div_pi hrem)

end Secant
end Meromorphic
end Ch5
end AnalyticCombinatorics
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch5 AnalyticCombinatorics.Ch5.Meromorphic AnalyticCombinatorics.Ch5.Meromorphic.Secant
open Complex Filter Asymptotics
open scoped ENNReal NNReal PowerSeries Topology
theorem solution :
    (fun k : ℕ => secantNumber (2 * k) / ((2 * k).factorial : ℝ))
      ~[atTop]
    (fun k : ℕ => 2 * (2 / Real.pi) ^ (2 * k + 1)) :=
  secantNumber_div_factorial_even_isEquivalent_two_div_pi secantRemainder_radius_gt_two
