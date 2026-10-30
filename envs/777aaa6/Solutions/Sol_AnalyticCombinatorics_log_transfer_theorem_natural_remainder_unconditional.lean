-- Prove2me | solution 1 for AnalyticCombinatorics.log_transfer_theorem_natural_remainder_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-27T04:46:57.971615+00:00
-- url     : https://prove2.me/submissions/b5ef20cc-49de-4481-9730-cd556159a214

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_DeltaDomain
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_LittleOTransfer
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_LogSingularity
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_LogTransfer
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Card

namespace AnalyticCombinatorics end AnalyticCombinatorics

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

/-!
# General-exponent singularity scale

This is the Flajolet--Sedgewick Theorem VI.1 standard scale for general `α`:
`[z^n] (1 - z)^{-α} ~ n^{α-1} / Γ(α)`. The integer case
`Γ(k) = (k - 1)!` is in `SingularityInteger.lean`; the full transfer theorem
with Δ-domains and a little-o Darboux estimate is assembled in
`TransferGeneral.lean` (`transfer_theorem`).

The hypothesis `∀ m : ℕ, α ≠ -m` says `α ∉ {0, -1, -2, ...}`. It holds for
all non-integer real `α` and is the correct non-vacuous hypothesis.
-/

open scoped BigOperators
open Finset Polynomial Filter Asymptotics

lemma ascPochhammer_eval_eq_prod_range_complex (n : ℕ) (r : ℂ) :
    Polynomial.eval r (ascPochhammer ℂ n) = ∏ j ∈ Finset.range n, (r + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ascPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_natCast, ih, Finset.prod_range_succ]

lemma choose_eq_prod_range_complex (α : ℂ) (n : ℕ) :
    Ring.choose (α + n - 1) n = (∏ j ∈ Finset.range n, (α + j)) / (n.factorial : ℂ) := by
  have hmul := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (R := ℂ) α n
  have hfac : (n.factorial : ℂ) * Ring.choose (α + n - 1) n =
      ∏ j ∈ Finset.range n, (α + j) := by
    rw [← Ring.multichoose_eq α n]
    simpa [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval,
      ascPochhammer_eval_eq_prod_range_complex] using hmul
  have hne : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hne]
  simpa [mul_comm] using hfac

lemma GammaSeq_ne_zero_complex {α : ℂ} (hα : ∀ m : ℕ, α ≠ -m)
    {n : ℕ} (hn : n ≠ 0) : Complex.GammaSeq α n ≠ 0 := by
  have hfact : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hncast : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hnpow : (n : ℂ)^α ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl hncast
  have hαn : α + n ≠ 0 := by
    intro h
    exact hα n (eq_neg_of_add_eq_zero_left h)
  have hprod : (∏ j ∈ Finset.range n, (α + j)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j hj hzero
    exact hα j (eq_neg_of_add_eq_zero_left hzero)
  have hGs : Complex.GammaSeq α n =
      (n : ℂ)^α * (n.factorial : ℂ) /
        ((∏ j ∈ Finset.range n, (α + j)) * (α + n)) := by
    simp [Complex.GammaSeq, Finset.prod_range_succ]
  rw [hGs]
  exact div_ne_zero (mul_ne_zero hnpow hfact) (mul_ne_zero hprod hαn)

lemma choose_eq_cpow_div_gammaSeq_complex {α : ℂ} (hα : ∀ m : ℕ, α ≠ -m)
    {n : ℕ} (hn : n ≠ 0) :
    Ring.choose (α + n - 1) n =
      (n : ℂ)^α / ((α + n) * Complex.GammaSeq α n) := by
  have hfact : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hncast : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hnpow : (n : ℂ)^α ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl hncast
  have hαn : α + n ≠ 0 := by
    intro h
    exact hα n (eq_neg_of_add_eq_zero_left h)
  have hprod : (∏ j ∈ Finset.range n, (α + j)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j hj hzero
    exact hα j (eq_neg_of_add_eq_zero_left hzero)
  have hGs : Complex.GammaSeq α n =
      (n : ℂ)^α * (n.factorial : ℂ) /
        ((∏ j ∈ Finset.range n, (α + j)) * (α + n)) := by
    simp [Complex.GammaSeq, Finset.prod_range_succ]
  rw [choose_eq_prod_range_complex, hGs]
  field_simp [hfact, hprod, hαn, hnpow]

lemma choose_ratio_eq_gammaSeq_ratio_complex {α : ℂ} (hα : ∀ m : ℕ, α ≠ -m)
    {n : ℕ} (hn : n ≠ 0) :
    Ring.choose (α + n - 1) n / ((n : ℂ)^(α - 1) / Complex.Gamma α) =
      (Complex.Gamma α / Complex.GammaSeq α n) * ((n : ℂ) / (n + α)) := by
  have hncast : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hnpowα : (n : ℂ)^α ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl hncast
  have hnpowα1 : (n : ℂ)^(α - 1) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl hncast
  have hαn : α + n ≠ 0 := by
    intro h
    exact hα n (eq_neg_of_add_eq_zero_left h)
  have hnα : (n : ℂ) + α ≠ 0 := by
    simpa [add_comm] using hαn
  have hΓ : Complex.Gamma α ≠ 0 := Complex.Gamma_ne_zero hα
  have hGseq : Complex.GammaSeq α n ≠ 0 := GammaSeq_ne_zero_complex hα hn
  rw [choose_eq_cpow_div_gammaSeq_complex hα hn]
  rw [Complex.cpow_sub _ _ hncast, Complex.cpow_one]
  field_simp [hncast, hnpowα, hnpowα1, hαn, hnα, hΓ, hGseq]
  ring

lemma choose_ratio_tendsto_one_complex {α : ℂ} (hα : ∀ m : ℕ, α ≠ -m) :
    Tendsto (fun n : ℕ =>
      Ring.choose (α + n - 1) n / ((n : ℂ)^(α - 1) / Complex.Gamma α))
      atTop (nhds 1) := by
  have hΓ : Complex.Gamma α ≠ 0 := Complex.Gamma_ne_zero hα
  have h_event : (fun n : ℕ =>
      Ring.choose (α + n - 1) n / ((n : ℂ)^(α - 1) / Complex.Gamma α))
      =ᶠ[atTop]
      (fun n : ℕ => (Complex.Gamma α / Complex.GammaSeq α n) * ((n : ℂ) / (n + α))) := by
    exact (eventually_ne_atTop 0).mono fun n hn => choose_ratio_eq_gammaSeq_ratio_complex hα hn
  apply Filter.Tendsto.congr' h_event.symm
  have h₁ : Tendsto (fun n : ℕ => Complex.Gamma α / Complex.GammaSeq α n) atTop (nhds 1) := by
    simpa [div_self hΓ] using
      (tendsto_const_nhds (x := Complex.Gamma α)).div (Complex.GammaSeq_tendsto_Gamma α) hΓ
  have h₂ : Tendsto (fun n : ℕ => (n : ℂ) / (n + α)) atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop α
  simpa using h₁.mul h₂

theorem choose_standard_scale_complex {α : ℂ} (hα : ∀ m : ℕ, α ≠ -m) :
    (fun n : ℕ => Ring.choose (α + n - 1) n) ~[atTop]
      (fun n : ℕ => (n : ℂ)^(α - 1) / Complex.Gamma α) := by
  have hΓ : Complex.Gamma α ≠ 0 := Complex.Gamma_ne_zero hα
  have htarget : ∀ᶠ n : ℕ in atTop, (n : ℂ)^(α - 1) / Complex.Gamma α ≠ 0 := by
    refine (eventually_ne_atTop 0).mono ?_
    intro n hn
    have hncast : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hpow : (n : ℂ)^(α - 1) ≠ 0 := by
      rw [Complex.cpow_ne_zero_iff]
      exact Or.inl hncast
    exact div_ne_zero hpow hΓ
  rw [isEquivalent_iff_tendsto_one htarget]
  exact choose_ratio_tendsto_one_complex hα

open Complex Filter
open scoped Topology

lemma arg_away_iff_re_lt_cos_mul_norm {w : ℂ} (hw : w ≠ 0) {φ : ℝ}
    (hφ0 : 0 ≤ φ) (hφπ : φ < Real.pi) :
    φ < |Complex.arg w| ↔ w.re < Real.cos φ * ‖w‖ := by
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have harg_mem : |Complex.arg w| ∈ Set.Icc (0 : ℝ) Real.pi := by
    exact ⟨abs_nonneg _, Complex.abs_arg_le_pi w⟩
  have hφ_mem : φ ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hφ0, hφπ.le⟩
  rw [← Complex.norm_mul_cos_arg w, ← Real.cos_abs]
  rw [mul_comm (Real.cos φ) ‖w‖]
  constructor
  · intro h
    have hcos : Real.cos |Complex.arg w| < Real.cos φ :=
      (Real.strictAntiOn_cos.lt_iff_gt harg_mem hφ_mem).2 h
    exact mul_lt_mul_of_pos_left hcos hnorm
  · intro h
    have hcos : Real.cos |Complex.arg w| < Real.cos φ :=
      lt_of_mul_lt_mul_left h hnorm.le
    exact (Real.strictAntiOn_cos.lt_iff_gt harg_mem hφ_mem).1 hcos

lemma delta_arg_eq_geom {R φ : ℝ} (hφ0 : 0 ≤ φ) (hφπ : φ < Real.pi) :
    DeltaDomainArg R φ = DeltaDomainGeom R φ := by
  ext z
  unfold DeltaDomainArg DeltaDomainGeom
  constructor
  · intro hz
    rcases hz with ⟨hR, hz_ne, harg⟩
    refine ⟨?_, ?_⟩
    · simpa [Metric.mem_ball, dist_eq_norm] using hR
    · have hw : z - 1 ≠ 0 := by
        simpa [sub_eq_zero] using hz_ne
      exact (arg_away_iff_re_lt_cos_mul_norm hw hφ0 hφπ).mp harg
  · intro hz
    rcases hz with ⟨hR, hgeom⟩
    have hz_ne : z ≠ 1 := by
      intro hz_eq
      subst z
      set_option backward.isDefEq.respectTransparency false in
        norm_num at hgeom
    refine ⟨?_, hz_ne, ?_⟩
    · simpa [Metric.mem_ball, dist_eq_norm] using hR
    · have hw : z - 1 ≠ 0 := by
        simpa [sub_eq_zero] using hz_ne
      exact (arg_away_iff_re_lt_cos_mul_norm hw hφ0 hφπ).mpr hgeom

lemma one_sub_mem_slitPlane_of_mem_delta {R φ : ℝ} {z : ℂ}
    (hφ0 : 0 < φ) (hz : z ∈ DeltaDomainArg R φ) :
    (1 - z) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra hnot
  push Not at hnot
  have harg0 : Complex.arg (z - 1) = 0 := by
    rw [Complex.arg_eq_zero_iff]
    constructor
    · have hre := hnot.1
      simp at hre ⊢
      linarith
    · have him := hnot.2
      simp at him ⊢
      linarith
  have hlt : φ < 0 := by
    simpa [harg0] using hz.2.2
  linarith

lemma analyticOnNhd_one_sub_cpow_deltaDomain {α : ℂ} {R φ : ℝ}
    (hφ0 : 0 < φ) (_hφπ : φ < Real.pi) :
    AnalyticOnNhd ℂ (fun z : ℂ => (1 - z) ^ (-α)) (DeltaDomainArg R φ) := by
  exact (analyticOnNhd_const.sub analyticOnNhd_id).cpow analyticOnNhd_const
    (fun z hz => one_sub_mem_slitPlane_of_mem_delta hφ0 hz)

open Complex

lemma closedBall_subset_deltaDomain {R φ r : ℝ} (hr1 : r < 1) (hrR : r < R)
    (hφ : 0 < φ) (hφ2 : φ < Real.pi / 2) :
    Metric.closedBall (0 : ℂ) r ⊆ DeltaDomainArg R φ := by
  have hφπ : φ < Real.pi := by linarith [hφ2, Real.pi_pos]
  rw [delta_arg_eq_geom hφ.le hφπ]
  intro z hz
  unfold DeltaDomainGeom
  have hz_norm_le : ‖z‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  constructor
  · have hz_norm_lt : ‖z‖ < R := lt_of_le_of_lt hz_norm_le hrR
    simpa [Metric.mem_ball, dist_eq_norm] using hz_norm_lt
  · have hz_re_lt_one : z.re < 1 := by
      exact lt_of_le_of_lt (Complex.re_le_norm z) (lt_of_le_of_lt hz_norm_le hr1)
    have hleft : (z - 1).re < 0 := by
      rw [Complex.sub_re, Complex.one_re]
      linarith
    have hcos_pos : 0 < Real.cos φ := by
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ, Real.pi_pos], hφ2⟩
    have hright : 0 ≤ Real.cos φ * ‖z - 1‖ :=
      mul_nonneg hcos_pos.le (norm_nonneg _)
    exact lt_of_lt_of_le hleft hright

/-!
# Kernel integral estimates

This file proves the reusable real-variable kernel estimate used by the
circle-only transfer argument.
-/

open Complex
open MeasureTheory
open scoped Real

private lemma exp_real_mul_I (θ : ℝ) :
    Complex.exp (θ * Complex.I) =
      (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  have h := Complex.exp_mul_I (θ : ℂ)
  simpa [Complex.ofReal_cos, Complex.ofReal_sin] using h

lemma circleKernel_norm_sq (r θ : ℝ) :
    ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ 2 =
      (1 - r) ^ 2 + 2 * r * (1 - Real.cos θ) := by
  rw [← Complex.normSq_eq_norm_sq]
  rw [exp_real_mul_I]
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, sub_zero,
    zero_sub, zero_mul, mul_zero]
  set_option backward.isDefEq.respectTransparency false in
    ring_nf
    rw [Real.sin_sq]
    ring

private lemma two_div_pi_sq_le_one : (2 : ℝ) / Real.pi ^ 2 ≤ 1 := by
  have hpi2 : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
  have hsq : (2 : ℝ) ^ 2 ≤ Real.pi ^ 2 := by
    exact pow_le_pow_left₀ (by norm_num) hpi2 2
  have htwo_le_sq : (2 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
  exact (div_le_one (sq_pos_of_pos Real.pi_pos)).2 htwo_le_sq

lemma circleKernel_norm_sq_lower (r θ : ℝ) (hθ : |θ| ≤ Real.pi)
    (hr : (1 : ℝ) / 2 ≤ r) :
    (2 / Real.pi ^ 2) * ((1 - r) ^ 2 + θ ^ 2) ≤
      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ 2 := by
  rw [circleKernel_norm_sq]
  have hc_le_one : (2 : ℝ) / Real.pi ^ 2 ≤ 1 := two_div_pi_sq_le_one
  have hs1 : (2 / Real.pi ^ 2) * (1 - r) ^ 2 ≤ (1 - r) ^ 2 := by
    nlinarith [sq_nonneg (1 - r)]
  have hcos_le := Real.cos_le_one_sub_mul_cos_sq hθ
  have hcos : (2 / Real.pi ^ 2) * θ ^ 2 ≤ 1 - Real.cos θ := by
    linarith
  have hcos_nonneg : 0 ≤ 1 - Real.cos θ := by
    nlinarith [Real.cos_le_one θ]
  have htheta_nonneg : 0 ≤ (2 / Real.pi ^ 2) * θ ^ 2 := by positivity
  have hr2 : 1 ≤ 2 * r := by nlinarith
  have hs2 : (2 / Real.pi ^ 2) * θ ^ 2 ≤ 2 * r * (1 - Real.cos θ) := by
    nlinarith [hcos, hcos_nonneg, htheta_nonneg, hr2]
  nlinarith

private lemma rho_mul_rpow_neg_eq (ρ β : ℝ) (hρ : 0 < ρ) :
    ρ * ρ ^ (-β) = ρ ^ (1 - β) := by
  have h := Real.rpow_add hρ 1 (-β)
  rw [Real.rpow_one] at h
  calc
    ρ * ρ ^ (-β) = ρ ^ (1 + -β) := h.symm
    _ = ρ ^ (1 - β) := by ring_nf

private lemma modelContinuous (ρ β : ℝ) (hρ : 0 < ρ) :
    Continuous fun θ : ℝ => (ρ ^ 2 + θ ^ 2) ^ (-β / 2) := by
  refine (continuous_const.add (continuous_id.pow 2)).rpow_const ?_
  intro θ
  left
  change ρ ^ 2 + θ ^ 2 ≠ 0
  nlinarith [sq_pos_of_pos hρ, sq_nonneg θ]

private lemma modelIntervalIntegrable (ρ β a b : ℝ) (hρ : 0 < ρ) :
    IntervalIntegrable (fun θ : ℝ => (ρ ^ 2 + θ ^ 2) ^ (-β / 2)) volume a b := by
  exact (modelContinuous ρ β hρ).intervalIntegrable a b

private lemma rpow_sq (x a : ℝ) (hx : 0 ≤ x) :
    (x ^ 2) ^ a = x ^ (2 * a) := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx]
  norm_num

private lemma rpow_sq_neg_half (x β : ℝ) (hx : 0 ≤ x) :
    (x ^ 2) ^ (-β / 2) = x ^ (-β) := by
  rw [rpow_sq x (-β / 2) hx]
  congr 1
  ring

lemma circleKernel_rpow_le_model (r θ β : ℝ) (hθ : |θ| ≤ Real.pi)
    (hr : (1 : ℝ) / 2 ≤ r) (h1r : 0 < 1 - r) (hβ0 : 0 ≤ β) :
    ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) ≤
      ((2 : ℝ) / Real.pi ^ 2) ^ (-β / 2) *
        (((1 - r) ^ 2 + θ ^ 2) ^ (-β / 2)) := by
  let z : ℂ := (1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)
  let c : ℝ := (2 : ℝ) / Real.pi ^ 2
  let A : ℝ := (1 - r) ^ 2 + θ ^ 2
  have hcpos : 0 < c := by positivity
  have hApos : 0 < A := by
    dsimp [A]
    nlinarith [sq_pos_of_pos h1r, sq_nonneg θ]
  have hbase_pos : 0 < c * A := mul_pos hcpos hApos
  have hlow : c * A ≤ ‖z‖ ^ 2 := by
    dsimp [z, c, A]
    exact circleKernel_norm_sq_lower r θ hθ hr
  have hpow := Real.rpow_le_rpow_of_nonpos hbase_pos hlow (by nlinarith : -β / 2 ≤ 0)
  calc
    ‖z‖ ^ (-β) = (‖z‖ ^ 2) ^ (-β / 2) := by
      rw [rpow_sq_neg_half ‖z‖ β (norm_nonneg z)]
    _ ≤ (c * A) ^ (-β / 2) := hpow
    _ = c ^ (-β / 2) * A ^ (-β / 2) := by
      rw [Real.mul_rpow hcpos.le hApos.le]

private lemma model_le_rho_neg_beta {ρ β θ : ℝ} (hρ : 0 < ρ) (hβ0 : 0 ≤ β) :
    (ρ ^ 2 + θ ^ 2) ^ (-β / 2) ≤ ρ ^ (-β) := by
  have hbase_pos : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hle : ρ ^ 2 ≤ ρ ^ 2 + θ ^ 2 := by nlinarith [sq_nonneg θ]
  have hpow := Real.rpow_le_rpow_of_nonpos hbase_pos hle (by nlinarith : -β / 2 ≤ 0)
  rwa [rpow_sq_neg_half ρ β hρ.le] at hpow

private lemma integral_model_zero_rho_le {ρ β : ℝ} (hρ : 0 < ρ) (hβ0 : 0 ≤ β) :
    ∫ θ in (0 : ℝ)..ρ, (ρ ^ 2 + θ ^ 2) ^ (-β / 2) ≤ ρ ^ (1 - β) := by
  have hmono := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := ρ)
    hρ.le (modelIntervalIntegrable ρ β 0 ρ hρ) intervalIntegrable_const
    (fun θ _ => model_le_rho_neg_beta (ρ := ρ) (β := β) (θ := θ) hρ hβ0)
  calc
    ∫ θ in (0 : ℝ)..ρ, (ρ ^ 2 + θ ^ 2) ^ (-β / 2) ≤
        ∫ _θ in (0 : ℝ)..ρ, ρ ^ (-β) := hmono
    _ = ρ ^ (1 - β) := by
      rw [intervalIntegral.integral_const]
      simp [rho_mul_rpow_neg_eq ρ β hρ]

private lemma model_le_theta_neg_beta {ρ β θ : ℝ} (hθ : 0 < θ) (hβ0 : 0 ≤ β) :
    (ρ ^ 2 + θ ^ 2) ^ (-β / 2) ≤ θ ^ (-β) := by
  have hbase_pos : 0 < θ ^ 2 := sq_pos_of_pos hθ
  have hle : θ ^ 2 ≤ ρ ^ 2 + θ ^ 2 := by nlinarith [sq_nonneg ρ]
  have hpow := Real.rpow_le_rpow_of_nonpos hbase_pos hle (by nlinarith : -β / 2 ≤ 0)
  rwa [rpow_sq_neg_half θ β hθ.le] at hpow

private lemma rpowNegIntervalIntegrable {ρ b β : ℝ} (hρ : 0 < ρ) (hρb : ρ ≤ b) :
    IntervalIntegrable (fun θ : ℝ => θ ^ (-β)) volume ρ b := by
  refine (continuousOn_id.rpow_const ?_).intervalIntegrable
  intro θ hθ
  left
  rw [Set.uIcc_of_le hρb] at hθ
  have hθpos : 0 < θ := lt_of_lt_of_le hρ hθ.1
  exact hθpos.ne'

private lemma integral_rpow_neg_le {ρ β : ℝ} (hρ : 0 < ρ) (hρπ : ρ ≤ Real.pi)
    (hβ : 1 < β) :
    ∫ θ in ρ..Real.pi, θ ^ (-β) ≤ (β - 1)⁻¹ * ρ ^ (1 - β) := by
  have hnot : (-β) ≠ -1 := by linarith
  have hznot : (0 : ℝ) ∉ Set.uIcc ρ Real.pi := by
    rw [Set.uIcc_of_le hρπ]
    intro hmem
    exact (not_lt_of_ge hmem.1) hρ
  rw [integral_rpow (a := ρ) (b := Real.pi) (r := -β) (Or.inr ⟨hnot, hznot⟩)]
  have hden_pos : 0 < β - 1 := by linarith
  have hpi_nonneg : 0 ≤ Real.pi ^ (1 - β) := by positivity
  calc
    (Real.pi ^ (-β + 1) - ρ ^ (-β + 1)) / (-β + 1)
        = (ρ ^ (1 - β) - Real.pi ^ (1 - β)) / (β - 1) := by
          have hden_ne : β - 1 ≠ 0 := by linarith
          have hden_ne' : 1 - β ≠ 0 := by linarith
          rw [show -β + 1 = 1 - β by ring]
          field_simp [hden_ne, hden_ne']
          ring
    _ ≤ ρ ^ (1 - β) / (β - 1) := by
      exact div_le_div_of_nonneg_right (by nlinarith) hden_pos.le
    _ = (β - 1)⁻¹ * ρ ^ (1 - β) := by field_simp

private lemma integral_model_rho_pi_le {ρ β : ℝ} (hρ : 0 < ρ) (hρπ : ρ ≤ Real.pi)
    (hβ : 1 < β) :
    ∫ θ in ρ..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2) ≤
      (β - 1)⁻¹ * ρ ^ (1 - β) := by
  have hβ0 : 0 ≤ β := by linarith
  have hmono := intervalIntegral.integral_mono_on (a := ρ) (b := Real.pi)
    hρπ (modelIntervalIntegrable ρ β ρ Real.pi hρ)
    (rpowNegIntervalIntegrable (ρ := ρ) (b := Real.pi) (β := β) hρ hρπ)
    (fun θ hθ => model_le_theta_neg_beta (ρ := ρ) (β := β) (θ := θ)
      (lt_of_lt_of_le hρ hθ.1) hβ0)
  exact hmono.trans (integral_rpow_neg_le hρ hρπ hβ)

private lemma integral_model_zero_pi_le {ρ β : ℝ} (hρ : 0 < ρ) (hρle : ρ ≤ 1)
    (hβ : 1 < β) :
    ∫ θ in (0 : ℝ)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2) ≤
      (1 + (β - 1)⁻¹) * ρ ^ (1 - β) := by
  have hβ0 : 0 ≤ β := by linarith
  have hρπ : ρ ≤ Real.pi := by
    have h1π : (1 : ℝ) ≤ Real.pi := by linarith [Real.two_le_pi]
    exact hρle.trans h1π
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (modelIntervalIntegrable ρ β 0 ρ hρ)
    (modelIntervalIntegrable ρ β ρ Real.pi hρ)
  calc
    ∫ θ in (0 : ℝ)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2)
        = (∫ θ in (0 : ℝ)..ρ, (ρ ^ 2 + θ ^ 2) ^ (-β / 2)) +
          (∫ θ in ρ..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2)) := hsplit.symm
    _ ≤ ρ ^ (1 - β) + (β - 1)⁻¹ * ρ ^ (1 - β) := by
      exact add_le_add (integral_model_zero_rho_le hρ hβ0)
        (integral_model_rho_pi_le hρ hρπ hβ)
    _ = (1 + (β - 1)⁻¹) * ρ ^ (1 - β) := by ring

private lemma model_even (ρ β θ : ℝ) :
    (ρ ^ 2 + (-θ) ^ 2) ^ (-β / 2) = (ρ ^ 2 + θ ^ 2) ^ (-β / 2) := by
  congr 1
  ring

private lemma integral_model_neg_pi_zero_eq {ρ β : ℝ} :
    ∫ θ in (-Real.pi)..(0 : ℝ), (ρ ^ 2 + θ ^ 2) ^ (-β / 2) =
      ∫ θ in (0 : ℝ)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2) := by
  calc
    ∫ θ in (-Real.pi)..(0 : ℝ), (ρ ^ 2 + θ ^ 2) ^ (-β / 2)
        = ∫ θ in (-Real.pi)..(0 : ℝ), (ρ ^ 2 + (-θ) ^ 2) ^ (-β / 2) := by
          apply intervalIntegral.integral_congr
          intro θ _
          exact (model_even ρ β θ).symm
    _ = ∫ θ in (0 : ℝ)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2) := by
      simpa only [neg_zero, neg_neg] using
        (intervalIntegral.integral_comp_neg
          (f := fun θ : ℝ => (ρ ^ 2 + θ ^ 2) ^ (-β / 2))
          (a := -Real.pi) (b := (0 : ℝ)))

lemma modelKernel_integral_bound {ρ β : ℝ} (hρ : 0 < ρ) (hρle : ρ ≤ 1)
    (hβ : 1 < β) :
    ∫ θ in (-Real.pi)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2) ≤
      (2 + 2 * (β - 1)⁻¹) * ρ ^ (1 - β) := by
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (modelIntervalIntegrable ρ β (-Real.pi) 0 hρ)
    (modelIntervalIntegrable ρ β 0 Real.pi hρ)
  calc
    ∫ θ in (-Real.pi)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2)
        = (∫ θ in (-Real.pi)..(0 : ℝ), (ρ ^ 2 + θ ^ 2) ^ (-β / 2)) +
          (∫ θ in (0 : ℝ)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2)) := hsplit.symm
    _ = 2 * (∫ θ in (0 : ℝ)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2)) := by
      rw [integral_model_neg_pi_zero_eq]
      ring
    _ ≤ 2 * ((1 + (β - 1)⁻¹) * ρ ^ (1 - β)) := by
      exact mul_le_mul_of_nonneg_left (integral_model_zero_pi_le hρ hρle hβ) (by norm_num)
    _ = (2 + 2 * (β - 1)⁻¹) * ρ ^ (1 - β) := by ring

/-!
# O-transfer for Δ-analytic functions, β > 1

This file records the circle-only O-transfer theorem for singular bounds with
exponent `β > 1`.  The proof combines Cauchy coefficient extraction, elementary
Δ-domain geometry, and the reusable circle-kernel integral estimate.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal

noncomputable section

private lemma circle_norm_integral_zero_to_neg_pi (f : ℂ → ℂ) (r : ℝ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap (0 : ℂ) r θ)‖) =
      ∫ θ in (-Real.pi)..Real.pi, ‖f (circleMap (0 : ℂ) r θ)‖ := by
  have hper : Function.Periodic
      (fun θ : ℝ => ‖f (circleMap (0 : ℂ) r θ)‖) (2 * Real.pi) :=
    (periodic_circleMap (0 : ℂ) r).comp (fun z : ℂ => ‖f z‖)
  have h := hper.intervalIntegral_add_eq (-Real.pi) 0
  simpa [two_mul, add_comm, add_left_comm, add_assoc] using h.symm

theorem norm_coeff_le_integral_circle
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : ℝ}
    (hr : 0 < r)
    (hp : HasFPowerSeriesAt f p (0 : ℂ))
    (hd : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) r)) (n : ℕ) :
    ‖p.coeff n‖ ≤
      (2 * Real.pi)⁻¹ * r⁻¹ ^ n *
        ∫ θ in (-Real.pi)..Real.pi, ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖ := by
  have hq : HasFPowerSeriesAt f (cauchyPowerSeries f (0 : ℂ) r) (0 : ℂ) := by
    have hnn : 0 < ((⟨r, hr.le⟩ : ℝ≥0)) := by
      exact_mod_cast hr
    exact (hd.hasFPowerSeriesOnBall hnn).hasFPowerSeriesAt
  have hpq : p = cauchyPowerSeries f (0 : ℂ) r := hp.eq_formalMultilinearSeries hq
  have hshift := circle_norm_integral_zero_to_neg_pi f r
  have hnorm := norm_cauchyPowerSeries_le f (0 : ℂ) r n
  rw [hpq]
  calc
    ‖(cauchyPowerSeries f (0 : ℂ) r).coeff n‖ =
        ‖cauchyPowerSeries f (0 : ℂ) r n‖ := by
      rw [FormalMultilinearSeries.norm_apply_eq_norm_coef]
    _ ≤ ((2 * Real.pi)⁻¹ *
          ∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap (0 : ℂ) r θ)‖) *
        |r|⁻¹ ^ n := hnorm
    _ = (2 * Real.pi)⁻¹ * r⁻¹ ^ n *
        ∫ θ in (-Real.pi)..Real.pi, ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖ := by
      rw [abs_of_pos hr, hshift]
      simp [circleMap_zero]
      ring

private lemma one_add_one_div_pow_le_exp {k : ℕ} (hk : 0 < k) :
    (1 + (1 : ℝ) / k) ^ k ≤ Real.exp 1 := by
  have hle : (-(1 : ℝ)) ≤ (k : ℝ) := by
    have hk_nonneg : (0 : ℝ) ≤ k := by positivity
    linarith
  have h := Real.one_sub_div_pow_le_exp_neg (n := k) (t := (-1 : ℝ)) hle
  simpa [sub_eq_add_neg, neg_div, Real.exp_neg] using h

lemma one_sub_inv_pow_nat_le_four {n : ℕ} (hn : 2 ≤ n) :
    (((1 : ℝ) - 1 / n)⁻¹) ^ n ≤ 4 := by
  by_cases hn2 : n = 2
  · subst n
    norm_num
  by_cases hn3 : n = 3
  · subst n
    norm_num
  have hn4 : 4 ≤ n := by omega
  let k : ℕ := n - 1
  have hkpos : 0 < k := by
    dsimp [k]
    omega
  have hk3 : 3 ≤ k := by
    dsimp [k]
    omega
  have hn_eq : n = k + 1 := by
    dsimp [k]
    omega
  rw [hn_eq]
  have hbase : (((1 : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))⁻¹) =
      1 + (1 : ℝ) / k := by
    have hkreal : (k : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hkpos)
    have hk1real : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hkreal, hk1real]
    norm_num [Nat.cast_add, Nat.cast_one]
    ring
  rw [hbase, pow_succ]
  have hpow : (1 + (1 : ℝ) / k) ^ k ≤ Real.exp 1 :=
    one_add_one_div_pow_le_exp hkpos
  have hfactor : 1 + (1 : ℝ) / k ≤ 4 / 3 := by
    have hkreal : (3 : ℝ) ≤ k := by
      exact_mod_cast hk3
    have hkpos_real : (0 : ℝ) < k := by
      exact_mod_cast hkpos
    have hdiv : (1 : ℝ) / k ≤ 1 / 3 := by
      rw [one_div_le_one_div hkpos_real (by norm_num : (0 : ℝ) < 3)]
      exact hkreal
    linarith
  calc
    (1 + (1 : ℝ) / k) ^ k * (1 + (1 : ℝ) / k)
        ≤ Real.exp 1 * (4 / 3) := by
          exact mul_le_mul hpow hfactor (by positivity) (by positivity)
    _ ≤ 3 * (4 / 3) := by
          exact mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (by norm_num)
    _ = 4 := by norm_num

end

/-!
# The complex logarithm power series `−log(1−z) = ∑ zⁿ⁺¹/(n+1)`

Mathlib has only the *real* `Real.hasSum_pow_div_log_of_abs_lt_one`.  This file supplies the complex
analogue, the keystone bridge for the logarithmic singularity transfer (`LogTransfer`).

Reuses Mathlib's `Complex.logTaylor` remainder bound `norm_log_one_sub_inv_add_logTaylor_neg_le`:
the partial sums `∑_{j<N} zʲ⁺¹/(j+1) = −logTaylor(N+1)(−z)` converge to `log((1−z)⁻¹) = −log(1−z)`, and
the series is geometric-summable.
-/

open Filter Complex
open scoped Topology BigOperators

namespace AnalyticCombinatorics

/-- `logTaylor (N+1) (−z) = −∑_{n<N} zⁿ⁺¹/(n+1)`. -/
lemma logTaylor_neg_eq_neg_sum (N : ℕ) (z : ℂ) :
    Complex.logTaylor (N + 1) (-z)
      = -∑ n ∈ Finset.range N, z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) := by
  induction N with
  | zero => simp [Complex.logTaylor]
  | succ N ih =>
    have hterm : (-1 : ℂ) ^ (N + 1 + 1) * (-z) ^ (N + 1) / ((N + 1 : ℕ) : ℂ)
        = -(z ^ (N + 1) / ((N + 1 : ℕ) : ℂ)) := by
      have hne : ((-1 : ℂ)) ^ (N + 1 + 1) * (-1) ^ (N + 1) = -1 := by
        rw [← pow_add]; exact Odd.neg_one_pow ⟨N + 1, by ring⟩
      have hz1 : ((-z) ^ (N + 1) : ℂ) = (-1) ^ (N + 1) * z ^ (N + 1) := by rw [neg_pow]
      rw [hz1, ← mul_assoc, hne]
      push_cast
      ring
    rw [Complex.logTaylor_succ, Pi.add_apply, ih, hterm, Finset.sum_range_succ, neg_add]

/-- **Complex logarithm series**: for `‖z‖ < 1`, `∑ₙ zⁿ⁺¹/(n+1) = −log(1−z)`. -/
theorem hasSum_pow_succ_div_succ_neg_log {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) (-Complex.log (1 - z)) := by
  have hmz : (0 : ℝ) < 1 - ‖z‖ := by linarith
  have hinv : (0 : ℝ) ≤ (1 - ‖z‖)⁻¹ := le_of_lt (inv_pos.mpr hmz)
  -- summability (dominated by the geometric series)
  have hgeo : Summable (fun n : ℕ => ‖z‖ ^ (n + 1)) := by
    simpa [pow_succ] using (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_right ‖z‖
  have hsummable : Summable (fun n : ℕ => z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) := by
    refine Summable.of_norm_bounded hgeo (fun n => ?_)
    rw [norm_div, norm_pow, Complex.norm_natCast]
    apply div_le_self (by positivity)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)
  -- partial sums → -log(1-z)
  have harg : (1 - z).arg ≠ Real.pi := by
    have h := Complex.slitPlane_arg_ne_pi
      (Complex.mem_slitPlane_of_norm_lt_one (z := -z) (by rwa [norm_neg]))
    rwa [sub_eq_add_neg]
  have hloginv : Complex.log (1 - z)⁻¹ = -Complex.log (1 - z) := Complex.log_inv _ harg
  have htend0 : Tendsto
      (fun N : ℕ => Complex.log (1 - z)⁻¹ + Complex.logTaylor (N + 1) (-z)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hp : Tendsto (fun N : ℕ => ‖z‖ ^ (N + 1)) atTop (𝓝 0) := by
      simpa [pow_succ] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg z) hz).mul_const ‖z‖
    have hmaj : Tendsto (fun N : ℕ => ‖z‖ ^ (N + 1) * (1 - ‖z‖)⁻¹) atTop (𝓝 0) := by
      simpa using hp.mul_const ((1 - ‖z‖)⁻¹)
    refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hmaj
    refine (norm_log_one_sub_inv_add_logTaylor_neg_le N hz).trans ?_
    refine div_le_self (mul_nonneg (by positivity) hinv) ?_
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have htend : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, z ^ (n + 1) / ((n + 1 : ℕ) : ℂ))
      atTop (𝓝 (-Complex.log (1 - z))) := by
    have h1 : Tendsto
        (fun N : ℕ => Complex.log (1 - z)⁻¹
          - ∑ n ∈ Finset.range N, z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) atTop (𝓝 0) := by
      simpa [logTaylor_neg_eq_neg_sum, sub_eq_add_neg] using htend0
    have h2 := (tendsto_const_nhds (α := ℕ) (x := Complex.log (1 - z)⁻¹)).sub h1
    simpa [hloginv] using h2
  -- assemble HasSum
  have hsum := hsummable.hasSum
  have hval : ∑' n : ℕ, z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) = -Complex.log (1 - z) :=
    tendsto_nhds_unique hsum.tendsto_sum_nat htend
  rwa [hval] at hsum

end AnalyticCombinatorics

/-!
# Little-o transfer for Δ-analytic functions, β > 1

This file contains the coefficient-level `o` transfer companion to the
circle-only `O` transfer in `OTransfer.lean`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal

noncomputable section

private lemma circlePoint_mem_delta {R φ r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hrR : r < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2) (θ : ℝ) :
    ((r : ℂ) * Complex.exp (θ * Complex.I)) ∈ DeltaDomainArg R φ := by
  refine closedBall_subset_deltaDomain hr1 hrR hφ0 hφ2 ?_
  rw [Metric.mem_closedBall, dist_eq_norm]
  calc
    ‖((r : ℂ) * Complex.exp (θ * Complex.I)) - 0‖
        = r := by
          simp [Complex.norm_exp_ofReal_mul_I, abs_of_nonneg hr0]
    _ ≤ r := le_rfl

private lemma circleFunction_intervalIntegrable
    {R φ r : ℝ} {f : ℂ → ℂ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hrR : r < R)
    (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ)) :
    IntervalIntegrable
      (fun θ : ℝ => ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖)
      volume (-Real.pi) Real.pi := by
  have hcont_delta : ContinuousOn f (DeltaDomainArg R φ) :=
    han.differentiableOn.continuousOn
  have hcont_circle : ContinuousOn
      (fun θ : ℝ => f ((r : ℂ) * Complex.exp (θ * Complex.I)))
      (Set.uIcc (-Real.pi) Real.pi) := by
    refine hcont_delta.comp ?_ ?_
    · exact (by fun_prop : Continuous fun θ : ℝ =>
        ((r : ℂ) * Complex.exp (θ * Complex.I))).continuousOn
    · intro θ _hθ
      exact circlePoint_mem_delta hr0 hr1 hrR hφ0 hφ2 θ
  exact hcont_circle.norm.intervalIntegrable

private lemma closedUnitAway_subset_delta {R φ δ : ℝ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2) (hδ : 0 < δ) :
    {z : ℂ | ‖z‖ ≤ 1 ∧ δ ≤ ‖(1 : ℂ) - z‖} ⊆ DeltaDomainArg R φ := by
  have hφπ : φ < Real.pi := by linarith [hφ2, Real.pi_pos]
  rw [delta_arg_eq_geom hφ0.le hφπ]
  intro z hz
  rcases hz with ⟨hz1, haway⟩
  refine ⟨?_, ?_⟩
  · have hzR : ‖z‖ < R := lt_of_le_of_lt hz1 hR
    simpa [Metric.mem_ball, dist_eq_norm] using hzR
  · have hleft : (z - 1).re ≤ 0 := by
      rw [Complex.sub_re, Complex.one_re]
      exact sub_nonpos.mpr (Complex.re_le_norm z |>.trans hz1)
    have hcos_pos : 0 < Real.cos φ := by
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ0, Real.pi_pos], hφ2⟩
    have hnorm_pos : 0 < ‖z - 1‖ := by
      rw [← norm_sub_rev]
      exact lt_of_lt_of_le hδ haway
    have hright_pos : 0 < Real.cos φ * ‖z - 1‖ :=
      mul_pos hcos_pos hnorm_pos
    exact lt_of_le_of_lt hleft hright_pos

private lemma isCompact_closedUnitAway (δ : ℝ) :
    IsCompact {z : ℂ | ‖z‖ ≤ 1 ∧ δ ≤ ‖(1 : ℂ) - z‖} := by
  have hclosed : IsClosed {z : ℂ | δ ≤ ‖(1 : ℂ) - z‖} :=
    isClosed_le continuous_const ((continuous_const.sub continuous_id).norm)
  have hset :
      {z : ℂ | ‖z‖ ≤ 1 ∧ δ ≤ ‖(1 : ℂ) - z‖} =
        Metric.closedBall (0 : ℂ) 1 ∩ {z : ℂ | δ ≤ ‖(1 : ℂ) - z‖} := by
    ext z
    simp [Metric.mem_closedBall, dist_eq_norm]
  rw [hset]
  exact (isCompact_closedBall (0 : ℂ) 1).inter_right hclosed

private lemma exists_bound_on_closedUnitAway
    {R φ δ : ℝ} {f : ℂ → ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2) (hδ : 0 < δ)
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ)) :
    ∃ M, 0 ≤ M ∧ ∀ z : ℂ, ‖z‖ ≤ 1 → δ ≤ ‖(1 : ℂ) - z‖ → ‖f z‖ ≤ M := by
  let S : Set ℂ := {z : ℂ | ‖z‖ ≤ 1 ∧ δ ≤ ‖(1 : ℂ) - z‖}
  have hScompact : IsCompact S := isCompact_closedUnitAway δ
  have hSsub : S ⊆ DeltaDomainArg R φ :=
    closedUnitAway_subset_delta hR hφ0 hφ2 hδ
  have hcont : ContinuousOn f S :=
    han.differentiableOn.continuousOn.mono hSsub
  obtain ⟨M₀, hM₀⟩ := hScompact.exists_bound_of_continuousOn hcont
  refine ⟨max M₀ 0, le_max_right _ _, fun z hz1 haway => ?_⟩
  exact (hM₀ z ⟨hz1, haway⟩).trans (le_max_left _ _)

private lemma coeff_norm_le_transferCircleBound
    {R φ : ℝ} {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p (0 : ℂ))
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ)) :
    ∀ᶠ n in atTop, ‖p.coeff n‖ ≤ transferCircleBound f n := by
  refine eventually_atTop.mpr ⟨2, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (by norm_num : (1 : ℕ) ≤ 2) hn
  have hnpos_nat : 0 < n := Nat.lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  let r : ℝ := 1 - (1 : ℝ) / n
  have hrpos : 0 < r := by
    dsimp [r]
    have htwo_le : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hdiv_lt : (1 : ℝ) / n < 1 := by
      rw [div_lt_one hnpos]
      linarith
    linarith
  have hr1 : r < 1 := by
    dsimp [r]
    have hdiv_pos : 0 < (1 : ℝ) / n := div_pos zero_lt_one hnpos
    linarith
  have hrR : r < R := lt_trans hr1 hR
  have hsubset : Metric.closedBall (0 : ℂ) r ⊆ DeltaDomainArg R φ :=
    closedBall_subset_deltaDomain hr1 hrR hφ0 hφ2
  have hd : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) r) :=
    han.differentiableOn.mono hsubset
  have hcauchy := norm_coeff_le_integral_circle (p := p) hrpos hp hd n
  simpa [transferCircleBound, r] using hcauchy

/-! ### Log-weighted kernel estimate for the natural-remainder transfer

The natural-remainder logarithmic transfer needs the contour integral of
`‖1-z‖^{-β}·(1+|log‖1-z‖|)` (the strong-remainder transfer used the un-weighted
`‖1-z‖^{-β}`).  The crude uniform bound `-log(ρ²+θ²) ≤ 2 log(1/ρ)` collapses the
log-weighted model integral onto the banked no-log `modelKernel_integral_bound`,
so no new contour estimate is required beyond a pointwise real inequality. -/

/-- Pointwise log majorant: `1 + |log t| ≤ 4 - 2 log t` for `0 < t ≤ 2`. -/
private lemma one_add_abs_log_le_four_sub {t : ℝ} (ht0 : 0 < t) (ht2 : t ≤ 2) :
    1 + |Real.log t| ≤ 4 - 2 * Real.log t := by
  by_cases h : t ≤ 1
  · have hlog : Real.log t ≤ 0 := Real.log_nonpos ht0.le h
    rw [abs_of_nonpos hlog]; linarith
  · have h' : 1 < t := not_le.mp h
    have hlog : 0 ≤ Real.log t := Real.log_nonneg h'.le
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    have hle1 : Real.log t ≤ 1 := by
      calc Real.log t ≤ Real.log 2 := Real.log_le_log ht0 ht2
        _ ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) h2e
        _ = 1 := Real.log_exp 1
    rw [abs_of_nonneg hlog]; linarith

/-- Continuity of `θ ↦ (ρ²+θ²)^{-β/2}` (`ρ > 0`). -/
private lemma model_rpow_continuous (ρ β : ℝ) (hρ : 0 < ρ) :
    Continuous fun θ : ℝ => (ρ ^ 2 + θ ^ 2) ^ (-β / 2) :=
  (continuous_const.add (continuous_id.pow 2)).rpow_const
    (fun θ => Or.inl (by positivity : (0 : ℝ) < ρ ^ 2 + θ ^ 2).ne')

/-- Continuity of `θ ↦ (ρ²+θ²)^{-β/2}·log(ρ²+θ²)` (`ρ > 0`). -/
private lemma model_log_continuous (ρ β : ℝ) (hρ : 0 < ρ) :
    Continuous fun θ : ℝ => (ρ ^ 2 + θ ^ 2) ^ (-β / 2) * Real.log (ρ ^ 2 + θ ^ 2) :=
  (model_rpow_continuous ρ β hρ).mul
    ((continuous_const.add (continuous_id.pow 2)).log
      (fun θ => (by positivity : (0 : ℝ) < ρ ^ 2 + θ ^ 2).ne'))

/-- **Log-weighted model integral bound** via the crude `-log(ρ²+θ²) ≤ 2 log(1/ρ)`. -/
private lemma modelKernelLog_integral_bound {ρ β K : ℝ}
    (hρ : 0 < ρ) (hρle : ρ ≤ 1) (hβ : 1 < β) (hK : 0 ≤ K) :
    ∫ θ in (-Real.pi)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2) * (K - Real.log (ρ ^ 2 + θ ^ 2)) ≤
      (2 + 2 * (β - 1)⁻¹) * ρ ^ (1 - β) * (K + 2 * Real.log (1 / ρ)) := by
  have hm_int : IntervalIntegrable (fun θ : ℝ => (ρ ^ 2 + θ ^ 2) ^ (-β / 2))
      volume (-Real.pi) Real.pi := (model_rpow_continuous ρ β hρ).intervalIntegrable _ _
  have hmK_int : IntervalIntegrable (fun θ : ℝ => K * (ρ ^ 2 + θ ^ 2) ^ (-β / 2))
      volume (-Real.pi) Real.pi := hm_int.const_mul K
  have hmlog_int : IntervalIntegrable
      (fun θ : ℝ => (ρ ^ 2 + θ ^ 2) ^ (-β / 2) * Real.log (ρ ^ 2 + θ ^ 2))
      volume (-Real.pi) Real.pi := (model_log_continuous ρ β hρ).intervalIntegrable _ _
  have hlog_inv_nonneg : 0 ≤ Real.log (1 / ρ) := by
    rw [one_div, Real.log_inv]; linarith [Real.log_nonpos hρ.le hρle]
  rw [intervalIntegral.integral_congr
    (g := fun θ => K * (ρ ^ 2 + θ ^ 2) ^ (-β / 2)
      - (ρ ^ 2 + θ ^ 2) ^ (-β / 2) * Real.log (ρ ^ 2 + θ ^ 2))
    (fun θ _ => by ring)]
  rw [intervalIntegral.integral_sub hmK_int hmlog_int, intervalIntegral.integral_const_mul]
  have hmbound : ∫ θ in (-Real.pi)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2)
      ≤ (2 + 2 * (β - 1)⁻¹) * ρ ^ (1 - β) := modelKernel_integral_bound hρ hρle hβ
  have hlog_le : -(∫ θ in (-Real.pi)..Real.pi,
        (ρ ^ 2 + θ ^ 2) ^ (-β / 2) * Real.log (ρ ^ 2 + θ ^ 2))
      ≤ 2 * Real.log (1 / ρ) * (∫ θ in (-Real.pi)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2)) := by
    rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
      hmlog_int.neg (hm_int.const_mul _) (fun θ _ => ?_)
    have hmnn : 0 ≤ (ρ ^ 2 + θ ^ 2) ^ (-β / 2) := by positivity
    have hloglb : -Real.log (ρ ^ 2 + θ ^ 2) ≤ 2 * Real.log (1 / ρ) := by
      have h1 : Real.log (ρ ^ 2) ≤ Real.log (ρ ^ 2 + θ ^ 2) :=
        Real.log_le_log (by positivity) (by nlinarith [sq_nonneg θ])
      have h2 : Real.log (ρ ^ 2) = 2 * Real.log ρ := by
        rw [show ρ ^ 2 = ρ ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
      have h3 : Real.log (1 / ρ) = -Real.log ρ := by rw [one_div, Real.log_inv]
      rw [h3]; nlinarith [h1, h2]
    nlinarith [mul_le_mul_of_nonneg_left hloglb hmnn, hmnn]
  have hP : (0 : ℝ) ≤ (2 + 2 * (β - 1)⁻¹) * ρ ^ (1 - β) := by
    have : 0 < β - 1 := by linarith
    have : (0 : ℝ) ≤ ρ ^ (1 - β) := (Real.rpow_pos_of_pos hρ _).le
    positivity
  have hKbound : K * (∫ θ in (-Real.pi)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2))
      ≤ K * ((2 + 2 * (β - 1)⁻¹) * ρ ^ (1 - β)) := mul_le_mul_of_nonneg_left hmbound hK
  have h2logbound : 2 * Real.log (1 / ρ) * (∫ θ in (-Real.pi)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2))
      ≤ 2 * Real.log (1 / ρ) * ((2 + 2 * (β - 1)⁻¹) * ρ ^ (1 - β)) :=
    mul_le_mul_of_nonneg_left hmbound (by linarith [hlog_inv_nonneg])
  have hexp : (2 + 2 * (β - 1)⁻¹) * ρ ^ (1 - β) * (K + 2 * Real.log (1 / ρ))
      = K * ((2 + 2 * (β - 1)⁻¹) * ρ ^ (1 - β))
        + 2 * Real.log (1 / ρ) * ((2 + 2 * (β - 1)⁻¹) * ρ ^ (1 - β)) := by ring
  linarith [hKbound, hlog_le, h2logbound, hexp]

/-- **Log-weighted circle kernel bound.**  For `β > 1` and `n ≥ 2`, the contour integral
of `‖1-z‖^{-β}(1+|log‖1-z‖|)` on the circle of radius `1-1/n` is `≤ C·n^{β-1}·log n`. -/
private lemma circleKernelLog_integral_bound_nat {β : ℝ} (hβ : 1 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      (∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (((1 : ℝ) - (1 : ℝ) / n : ℝ) : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
          (1 + |Real.log ‖(1 : ℂ) - (((1 : ℝ) - (1 : ℝ) / n : ℝ) : ℂ) *
            Complex.exp (θ * Complex.I)‖|))
        ≤ C * (n : ℝ) ^ (β - 1) * Real.log n := by
  have hβ0 : 0 ≤ β := by linarith
  have hπ2pos : (0 : ℝ) < 2 / Real.pi ^ 2 := by positivity
  have hπ2lt1 : 2 / Real.pi ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith [Real.pi_gt_three]
  set K₁ : ℝ := (2 / Real.pi ^ 2) ^ (-β / 2) with hK₁
  set B₀ : ℝ := 2 + 2 * (β - 1)⁻¹ with hB₀
  set K₂ : ℝ := 4 - Real.log (2 / Real.pi ^ 2) with hK₂
  have hβ1pos : (0 : ℝ) < β - 1 := by linarith
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  have hB₀0 : 0 ≤ B₀ := by rw [hB₀]; positivity
  have hK₂pos : 0 < K₂ := by
    rw [hK₂]; have := Real.log_neg hπ2pos hπ2lt1; linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨K₁ * B₀ * (K₂ / Real.log 2 + 2), by positivity, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := Nat.lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set r : ℝ := (1 : ℝ) - (1 : ℝ) / n with hr_def
  have hρeq : (1 : ℝ) - r = 1 / n := by rw [hr_def]; ring
  have hr_half : (1 : ℝ) / 2 ≤ r := by
    have hle : (1 : ℝ) / n ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn2R
    rw [hr_def]; linarith
  have hr1 : r < 1 := by
    have hpos : 0 < (1 : ℝ) / n := by positivity
    rw [hr_def]; linarith
  have h1r : 0 < 1 - r := by rw [hρeq]; positivity
  -- pointwise contour bound
  have hpt : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi,
      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
        (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|)
      ≤ K₁ * (((1 - r) ^ 2 + θ ^ 2) ^ (-β / 2) * (K₂ - Real.log ((1 - r) ^ 2 + θ ^ 2))) := by
    intro θ hθ
    have hθabs : |θ| ≤ Real.pi := abs_le.mpr ⟨hθ.1, hθ.2⟩
    set w : ℝ := ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ with hw
    have hwpos : 0 < w := by
      rw [hw, norm_pos_iff, sub_ne_zero]
      intro hcon
      have hnorm : ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ = 1 := by rw [← hcon]; simp
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ r)] at hnorm
      linarith
    have hwle2 : w ≤ 2 := by
      rw [hw]
      calc ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖
          ≤ ‖(1 : ℂ)‖ + ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ := norm_sub_le _ _
        _ = 1 + r := by
            rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
              Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ r)]; norm_num
        _ ≤ 2 := by linarith
    have hwbound : w ^ (-β) ≤ K₁ * ((1 - r) ^ 2 + θ ^ 2) ^ (-β / 2) :=
      circleKernel_rpow_le_model r θ β hθabs hr_half h1r hβ0
    have hsqlb : (2 / Real.pi ^ 2) * ((1 - r) ^ 2 + θ ^ 2) ≤ w ^ 2 :=
      circleKernel_norm_sq_lower r θ hθabs hr_half
    have hApos : 0 < (1 - r) ^ 2 + θ ^ 2 := by nlinarith [sq_pos_of_pos h1r, sq_nonneg θ]
    have hlogbound : 1 + |Real.log w| ≤ K₂ - Real.log ((1 - r) ^ 2 + θ ^ 2) := by
      have hstep1 : 1 + |Real.log w| ≤ 4 - 2 * Real.log w :=
        one_add_abs_log_le_four_sub hwpos hwle2
      have hlogsq : 2 * Real.log w = Real.log (w ^ 2) := by
        rw [Real.log_pow]; push_cast; ring
      have hmono : Real.log ((2 / Real.pi ^ 2) * ((1 - r) ^ 2 + θ ^ 2)) ≤ Real.log (w ^ 2) :=
        Real.log_le_log (by positivity) hsqlb
      have hsplit : Real.log ((2 / Real.pi ^ 2) * ((1 - r) ^ 2 + θ ^ 2))
          = Real.log (2 / Real.pi ^ 2) + Real.log ((1 - r) ^ 2 + θ ^ 2) :=
        Real.log_mul (by positivity) (by positivity)
      rw [hK₂]; nlinarith [hstep1, hlogsq, hmono, hsplit]
    have hKnn : 0 ≤ K₂ - Real.log ((1 - r) ^ 2 + θ ^ 2) := by
      have h1le : (1 : ℝ) ≤ 1 + |Real.log w| := le_add_of_nonneg_right (abs_nonneg _)
      linarith [hlogbound, h1le]
    have hwbnn : 0 ≤ w ^ (-β) := by positivity
    have hmodnn : 0 ≤ K₁ * ((1 - r) ^ 2 + θ ^ 2) ^ (-β / 2) := by positivity
    calc w ^ (-β) * (1 + |Real.log w|)
        ≤ (K₁ * ((1 - r) ^ 2 + θ ^ 2) ^ (-β / 2)) * (K₂ - Real.log ((1 - r) ^ 2 + θ ^ 2)) :=
          mul_le_mul hwbound hlogbound (by positivity) hmodnn
      _ = K₁ * (((1 - r) ^ 2 + θ ^ 2) ^ (-β / 2) * (K₂ - Real.log ((1 - r) ^ 2 + θ ^ 2))) := by
          ring
  -- integrability of both sides
  have hg : Continuous fun θ : ℝ => ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ :=
    (continuous_const.sub (continuous_const.mul
      (Complex.continuous_exp.comp (continuous_ofReal.mul continuous_const)))).norm
  have hgne : ∀ θ : ℝ, (1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I) ≠ 0 := by
    intro θ hcon
    have hnorm : ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ = 1 := by
      rw [← sub_eq_zero.mp hcon]; simp
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ r)] at hnorm
    linarith
  have hgpos : ∀ θ : ℝ, 0 < ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ :=
    fun θ => norm_pos_iff.mpr (hgne θ)
  have hLHS_int : IntervalIntegrable
      (fun θ : ℝ => ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
        (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|))
      volume (-Real.pi) Real.pi :=
    ((hg.rpow_const (fun θ => Or.inl (hgpos θ).ne')).mul
      (continuous_const.add (hg.log (fun θ => (hgpos θ).ne')).abs)).intervalIntegrable _ _
  have hRHS_int : IntervalIntegrable
      (fun θ : ℝ => K₁ * (((1 - r) ^ 2 + θ ^ 2) ^ (-β / 2)
        * (K₂ - Real.log ((1 - r) ^ 2 + θ ^ 2)))) volume (-Real.pi) Real.pi := by
    have : Continuous fun θ : ℝ => ((1 - r) ^ 2 + θ ^ 2) ^ (-β / 2)
        * (K₂ - Real.log ((1 - r) ^ 2 + θ ^ 2)) := by
      have hbase : Continuous fun θ : ℝ => (1 - r) ^ 2 + θ ^ 2 :=
        continuous_const.add (continuous_id.pow 2)
      exact (hbase.rpow_const (fun θ => Or.inl (by positivity : (0:ℝ) < (1-r)^2+θ^2).ne')).mul
        (continuous_const.sub (hbase.log (fun θ => (by positivity : (0:ℝ) < (1-r)^2+θ^2).ne')))
    exact (this.const_mul K₁).intervalIntegrable _ _
  -- integrate the pointwise bound, then apply the model bound
  have hint_le := intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
    hLHS_int hRHS_int hpt
  rw [intervalIntegral.integral_const_mul] at hint_le
  have hmodel := modelKernelLog_integral_bound (ρ := 1 - r) (β := β) (K := K₂)
    h1r (by rw [hρeq, div_le_one hnpos]; exact_mod_cast hnpos_nat) hβ hK₂pos.le
  have hconv : (1 - r) ^ (1 - β) = (n : ℝ) ^ (β - 1) := by
    rw [hρeq, one_div, Real.inv_rpow hnpos.le, ← Real.rpow_neg hnpos.le]
    congr 1; ring
  have hloginv : Real.log (1 / (1 - r)) = Real.log n := by rw [hρeq, one_div_one_div]
  rw [hconv, hloginv, ← hB₀] at hmodel
  -- chain: LHS ≤ K₁ * (B₀ n^{β-1}(K₂+2log n)) ≤ C n^{β-1} log n
  have hlogn2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2R
  have hnp0 : 0 ≤ (n : ℝ) ^ (β - 1) := (Real.rpow_pos_of_pos hnpos _).le
  have hKstep : K₂ + 2 * Real.log n ≤ (K₂ / Real.log 2 + 2) * Real.log n := by
    have h1 : K₂ = (K₂ / Real.log 2) * Real.log 2 := by field_simp
    have h2 : (K₂ / Real.log 2) * Real.log 2 ≤ (K₂ / Real.log 2) * Real.log n :=
      mul_le_mul_of_nonneg_left hlogn2 (by positivity)
    nlinarith [h1, h2]
  have hcoef : 0 ≤ K₁ * B₀ * (n : ℝ) ^ (β - 1) := mul_nonneg (mul_nonneg hK₁0 hB₀0) hnp0
  have hfinal : K₁ * (B₀ * (n : ℝ) ^ (β - 1) * (K₂ + 2 * Real.log n))
      ≤ K₁ * B₀ * (K₂ / Real.log 2 + 2) * (n : ℝ) ^ (β - 1) * Real.log n := by
    calc K₁ * (B₀ * (n : ℝ) ^ (β - 1) * (K₂ + 2 * Real.log n))
        = K₁ * B₀ * (n : ℝ) ^ (β - 1) * (K₂ + 2 * Real.log n) := by ring
      _ ≤ K₁ * B₀ * (n : ℝ) ^ (β - 1) * ((K₂ / Real.log 2 + 2) * Real.log n) :=
          mul_le_mul_of_nonneg_left hKstep hcoef
      _ = K₁ * B₀ * (K₂ / Real.log 2 + 2) * (n : ℝ) ^ (β - 1) * Real.log n := by ring
  calc ∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
          (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|)
      ≤ K₁ * (∫ θ in (-Real.pi)..Real.pi, ((1 - r) ^ 2 + θ ^ 2) ^ (-β / 2)
          * (K₂ - Real.log ((1 - r) ^ 2 + θ ^ 2))) := hint_le
    _ ≤ K₁ * (B₀ * (n : ℝ) ^ (β - 1) * (K₂ + 2 * Real.log n)) :=
        mul_le_mul_of_nonneg_left hmodel hK₁0
    _ ≤ K₁ * B₀ * (K₂ / Real.log 2 + 2) * (n : ℝ) ^ (β - 1) * Real.log n := hfinal

/-- Integrability of the log-weighted circle kernel integrand. -/
private lemma circleKernelLog_intervalIntegrable {β r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    IntervalIntegrable
      (fun θ : ℝ => ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
        (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|))
      volume (-Real.pi) Real.pi := by
  have hg : Continuous fun θ : ℝ => ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ :=
    (continuous_const.sub (continuous_const.mul
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)))).norm
  have hgne : ∀ θ : ℝ, (1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I) ≠ 0 := by
    intro θ hcon
    have hnorm : ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ = 1 := by
      rw [← sub_eq_zero.mp hcon]; simp
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hr0] at hnorm
    linarith
  have hgpos : ∀ θ : ℝ, 0 < ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ :=
    fun θ => norm_pos_iff.mpr (hgne θ)
  exact ((hg.rpow_const (fun θ => Or.inl (hgpos θ).ne')).mul
    (continuous_const.add (hg.log (fun θ => (hgpos θ).ne')).abs)).intervalIntegrable _ _

/-- Extract a pointwise `(1+|log|)`-weighted bound from the log-weighted little-o hypothesis. -/
private lemma exists_delta_littleO_kernel_bound_log
    {R φ β ε : ℝ} {f : ℂ → ℂ}
    (hf_o : Tendsto (fun z : ℂ => ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β * (Real.log (‖(1 : ℂ) - z‖⁻¹))⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0))
    (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ ∀ z ∈ DeltaDomainArg R φ, ‖(1 : ℂ) - z‖ < δ →
      ‖f z‖ ≤ ε * (‖(1 : ℂ) - z‖ ^ (-β) * (1 + |Real.log ‖(1 : ℂ) - z‖|)) := by
  rw [Metric.tendsto_nhdsWithin_nhds] at hf_o
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := hf_o ε hε
  refine ⟨min δ₀ 1, lt_min hδ₀pos one_pos, fun z hz hnear => ?_⟩
  have hnear0 : ‖(1 : ℂ) - z‖ < δ₀ := lt_of_lt_of_le hnear (min_le_left _ _)
  have hnear1 : ‖(1 : ℂ) - z‖ < 1 := lt_of_lt_of_le hnear (min_le_right _ _)
  have hz_ne : z ≠ 1 := hz.2.1
  have hnorm_pos : 0 < ‖(1 : ℂ) - z‖ := by
    rw [norm_pos_iff]; simpa [sub_eq_zero] using (Ne.symm hz_ne)
  have hlogneg : Real.log ‖(1 : ℂ) - z‖ ≤ 0 := Real.log_nonpos hnorm_pos.le hnear1.le
  have hlogeq : Real.log (‖(1 : ℂ) - z‖⁻¹) = |Real.log ‖(1 : ℂ) - z‖| := by
    rw [Real.log_inv, abs_of_nonpos hlogneg]
  have hloginv_pos : 0 < Real.log (‖(1 : ℂ) - z‖⁻¹) := by
    rw [Real.log_inv]; have := Real.log_neg hnorm_pos hnear1; linarith
  have hdist_z : dist z (1 : ℂ) < δ₀ := by simpa [dist_eq_norm, norm_sub_rev] using hnear0
  have hratio := hδ₀ hz hdist_z
  have hratio_nonneg : 0 ≤ ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β * (Real.log (‖(1 : ℂ) - z‖⁻¹))⁻¹ := by
    positivity
  have hratio_lt : ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β * (Real.log (‖(1 : ℂ) - z‖⁻¹))⁻¹ < ε := by
    have h := hratio
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hratio_nonneg] at h
    exact h
  have hXL : ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β * (Real.log (‖(1 : ℂ) - z‖⁻¹))⁻¹
      = (‖f z‖ * ‖(1 : ℂ) - z‖ ^ β) / Real.log (‖(1 : ℂ) - z‖⁻¹) := by rw [div_eq_mul_inv]
  rw [hXL] at hratio_lt
  have hstep : ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β < ε * Real.log (‖(1 : ℂ) - z‖⁻¹) :=
    (div_lt_iff₀ hloginv_pos).mp hratio_lt
  have hpow_mul : ‖(1 : ℂ) - z‖ ^ β * ‖(1 : ℂ) - z‖ ^ (-β) = 1 := by
    rw [← Real.rpow_add hnorm_pos]; simp
  calc ‖f z‖ = (‖f z‖ * ‖(1 : ℂ) - z‖ ^ β) * ‖(1 : ℂ) - z‖ ^ (-β) := by
        rw [mul_assoc, hpow_mul, mul_one]
    _ ≤ (ε * Real.log (‖(1 : ℂ) - z‖⁻¹)) * ‖(1 : ℂ) - z‖ ^ (-β) :=
        mul_le_mul_of_nonneg_right hstep.le (by positivity)
    _ = ε * (‖(1 : ℂ) - z‖ ^ (-β) * Real.log (‖(1 : ℂ) - z‖⁻¹)) := by ring
    _ ≤ ε * (‖(1 : ℂ) - z‖ ^ (-β) * (1 + |Real.log ‖(1 : ℂ) - z‖|)) := by
        apply mul_le_mul_of_nonneg_left _ hε.le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [hlogeq]; linarith [abs_nonneg (Real.log ‖(1 : ℂ) - z‖)]

/-- **Log-weighted little-o circle transfer.**  Under the natural-remainder hypothesis
`‖f z‖·‖1-z‖^β / log(1/‖1-z‖) → 0`, the Cauchy bound is `o(n^{β-1} log n)`. -/
private lemma transferCircleBoundLog_isLittleO
    {R φ β : ℝ} {f : ℂ → ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hf_o : Tendsto (fun z : ℂ => ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β * (Real.log (‖(1 : ℂ) - z‖⁻¹))⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0))
    (hβ : 1 < β) :
    transferCircleBound f =o[atTop] fun n : ℕ => (n : ℝ) ^ (β - 1) * Real.log n := by
  obtain ⟨C, hC0, hC⟩ := circleKernelLog_integral_bound_nat hβ
  let A : ℝ := (2 * Real.pi)⁻¹ * 4 * C
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  refine IsLittleO.of_bound ?_
  intro η hη
  let ε : ℝ := η / (2 * (A + 1))
  have hA1pos : 0 < A + 1 := by linarith
  have hεpos : 0 < ε := by dsimp [ε]; positivity
  have hhalfpos : 0 < η / 2 := by positivity
  have hdenpos : 0 < 2 * (A + 1) := by positivity
  have hnear_coeff : A * ε ≤ η / 2 := by
    dsimp [ε]
    field_simp [hdenpos.ne']
    nlinarith [hA0, hη]
  obtain ⟨δ, hδpos, hnear⟩ :=
    exists_delta_littleO_kernel_bound_log (R := R) (φ := φ) (β := β) (f := f) hf_o hεpos
  obtain ⟨M, hM0, hM⟩ :=
    exists_bound_on_closedUnitAway (R := R) (φ := φ) (δ := δ) (f := f) hR hφ0 hφ2 hδpos han
  let B : ℝ := (2 * Real.pi)⁻¹ * 4 * (M * (2 * Real.pi))
  have hscale_atTop : Tendsto (fun n : ℕ => (n : ℝ) ^ (β - 1) * Real.log n) atTop atTop :=
    Filter.Tendsto.atTop_mul_atTop₀
      ((tendsto_rpow_atTop (by linarith : (0:ℝ) < β - 1)).comp tendsto_natCast_atTop_atTop)
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have haway_eventually :
      ∀ᶠ n : ℕ in atTop, B ≤ (η / 2) * ((n : ℝ) ^ (β - 1) * Real.log n) := by
    have := hscale_atTop.eventually (eventually_ge_atTop (B / (η / 2)))
    filter_upwards [this] with n hn
    calc B = (η / 2) * (B / (η / 2)) := by field_simp
      _ ≤ (η / 2) * ((n : ℝ) ^ (β - 1) * Real.log n) := mul_le_mul_of_nonneg_left hn hhalfpos.le
  filter_upwards [eventually_atTop.mpr ⟨2, fun n hn => hn⟩, haway_eventually]
    with n hn haway_n
  have hn1 : 1 ≤ n := le_trans (by norm_num : (1 : ℕ) ≤ 2) hn
  have hnpos_nat : 0 < n := Nat.lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  let r : ℝ := 1 - (1 : ℝ) / n
  have hr0 : 0 ≤ r := by
    have : (1 : ℝ) / n ≤ 1 := by rw [div_le_one hnpos]; exact_mod_cast hn1
    dsimp [r]; linarith
  have hrpos : 0 < r := by
    have htwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have : (1 : ℝ) / n < 1 := by rw [div_lt_one hnpos]; linarith
    dsimp [r]; linarith
  have hr1 : r < 1 := by
    have : 0 < (1 : ℝ) / n := by positivity
    dsimp [r]; linarith
  have hrR : r < R := lt_trans hr1 hR
  have hscale_nonneg : 0 ≤ (n : ℝ) ^ (β - 1) * Real.log n := by
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
    positivity
  have hleft_int := circleFunction_intervalIntegrable (f := f) hr0 hr1 hrR hφ0 hφ2 han
  have hkernel_int := circleKernelLog_intervalIntegrable (β := β) (r := r) hr0 hr1
  have hright_int : IntervalIntegrable
      (fun θ : ℝ => ε * (‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
        (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|)) + M)
      volume (-Real.pi) Real.pi := (hkernel_int.const_mul ε).add intervalIntegrable_const
  have hInt_le :
      (∫ θ in (-Real.pi)..Real.pi, ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖) ≤
        ∫ θ in (-Real.pi)..Real.pi,
          ε * (‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
            (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|)) + M := by
    refine intervalIntegral.integral_mono_on (by linarith [Real.pi_pos]) hleft_int hright_int ?_
    intro θ _hθ
    set z : ℂ := (r : ℂ) * Complex.exp (θ * Complex.I) with hz
    have hz_delta : z ∈ DeltaDomainArg R φ := circlePoint_mem_delta hr0 hr1 hrR hφ0 hφ2 θ
    have hknn : 0 ≤ ‖(1 : ℂ) - z‖ ^ (-β) * (1 + |Real.log ‖(1 : ℂ) - z‖|) := by positivity
    by_cases hz_near : ‖(1 : ℂ) - z‖ < δ
    · have hlocal := hnear z hz_delta hz_near
      nlinarith [hlocal, hM0]
    · have hz_away : δ ≤ ‖(1 : ℂ) - z‖ := le_of_not_gt hz_near
      have hz_norm_le : ‖z‖ ≤ 1 := by
        rw [hz, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg hr0]; exact hr1.le
      have hbound : ‖f z‖ ≤ M := hM z hz_norm_le hz_away
      nlinarith [hbound, mul_nonneg hεpos.le hknn]
  have hr_inv4 : r⁻¹ ^ n ≤ 4 := by dsimp [r]; exact one_sub_inv_pow_nat_le_four hn
  have hkernel_bound :
      (∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
          (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|))
        ≤ C * (n : ℝ) ^ (β - 1) * Real.log n := by
    have h := hC n hn
    dsimp [r]; convert h using 3 <;> norm_num
  have hkernel_nonneg :
      0 ≤ ∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
          (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|) := by
    refine intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun θ _ => by positivity)
  have hInt_bound :
      (∫ θ in (-Real.pi)..Real.pi, ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖) ≤
        ε * (C * (n : ℝ) ^ (β - 1) * Real.log n) + M * (2 * Real.pi) := by
    refine hInt_le.trans ?_
    rw [intervalIntegral.integral_add (hkernel_int.const_mul ε) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    have h1 : ε * (∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
          (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|))
        ≤ ε * (C * (n : ℝ) ^ (β - 1) * Real.log n) :=
      mul_le_mul_of_nonneg_left hkernel_bound hεpos.le
    have h2 : (Real.pi - -Real.pi) • M ≤ M * (2 * Real.pi) := by
      rw [smul_eq_mul]; nlinarith [hM0, Real.pi_pos]
    linarith [h1, h2]
  have htransfer_le : transferCircleBound f n ≤ A * ε * ((n : ℝ) ^ (β - 1) * Real.log n) + B := by
    have hbracket_nonneg : 0 ≤ ε * (C * (n : ℝ) ^ (β - 1) * Real.log n) + M * (2 * Real.pi) := by
      have : 0 ≤ C * (n : ℝ) ^ (β - 1) * Real.log n := le_trans hkernel_nonneg hkernel_bound
      positivity
    have hI_nonneg : 0 ≤ ∫ θ in (-Real.pi)..Real.pi,
        ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖ :=
      intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun θ _ => by positivity)
    have hpi_inv : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
    calc transferCircleBound f n
        = (2 * Real.pi)⁻¹ * r⁻¹ ^ n *
            ∫ θ in (-Real.pi)..Real.pi, ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖ := by
          simp [transferCircleBound, r]
      _ ≤ (2 * Real.pi)⁻¹ * r⁻¹ ^ n *
            (ε * (C * (n : ℝ) ^ (β - 1) * Real.log n) + M * (2 * Real.pi)) :=
          mul_le_mul_of_nonneg_left hInt_bound
            (mul_nonneg hpi_inv (pow_nonneg (inv_nonneg.mpr hr0) n))
      _ ≤ (2 * Real.pi)⁻¹ * 4 *
            (ε * (C * (n : ℝ) ^ (β - 1) * Real.log n) + M * (2 * Real.pi)) := by
          have hstep := mul_le_mul_of_nonneg_right hr_inv4 hbracket_nonneg
          nlinarith [hstep, hbracket_nonneg, mul_nonneg hpi_inv hbracket_nonneg, Real.pi_pos,
            mul_nonneg (pow_nonneg (inv_nonneg.mpr hr0) n) hbracket_nonneg]
      _ = A * ε * ((n : ℝ) ^ (β - 1) * Real.log n) + B := by dsimp [A, B]; ring
  have hnear_n : A * ε * ((n : ℝ) ^ (β - 1) * Real.log n)
      ≤ (η / 2) * ((n : ℝ) ^ (β - 1) * Real.log n) :=
    mul_le_mul_of_nonneg_right hnear_coeff hscale_nonneg
  have htransfer_nonneg : 0 ≤ transferCircleBound f n := by
    have hI_nonneg : 0 ≤ ∫ θ in (-Real.pi)..Real.pi,
        ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖ :=
      intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun θ _ => by positivity)
    rw [transferCircleBound]
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (inv_nonneg.mpr hr0) n)) hI_nonneg
  calc ‖transferCircleBound f n‖ = transferCircleBound f n := Real.norm_of_nonneg htransfer_nonneg
    _ ≤ A * ε * ((n : ℝ) ^ (β - 1) * Real.log n) + B := htransfer_le
    _ ≤ (η / 2) * ((n : ℝ) ^ (β - 1) * Real.log n) + (η / 2) * ((n : ℝ) ^ (β - 1) * Real.log n) :=
        add_le_add hnear_n haway_n
    _ = η * ((n : ℝ) ^ (β - 1) * Real.log n) := by ring
    _ = η * ‖(n : ℝ) ^ (β - 1) * Real.log n‖ := by rw [Real.norm_of_nonneg hscale_nonneg]

/-- **Coefficient-level natural-remainder little-o transfer** (`β > 1`):
`‖f z‖·‖1-z‖^β / log(1/‖1-z‖) → 0` ⟹ `‖[zⁿ]f‖ = o(n^{β-1} log n)`. -/
theorem coeff_norm_isLittleO_atTop_of_delta_littleO_log_beta_gt_one
    {R φ β : ℝ} {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p (0 : ℂ))
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hf_o : Tendsto (fun z : ℂ => ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β * (Real.log (‖(1 : ℂ) - z‖⁻¹))⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0))
    (hβ : 1 < β) :
    (fun n : ℕ => ‖p.coeff n‖) =o[atTop] (fun n : ℕ => (n : ℝ) ^ (β - 1) * Real.log n) := by
  have hcircle := transferCircleBoundLog_isLittleO (R := R) (φ := φ) (β := β) (f := f)
    hR hφ0 hφ2 han hf_o hβ
  have hcoeff := coeff_norm_le_transferCircleBound (R := R) (φ := φ) (f := f) (p := p)
    hR hφ0 hφ2 hp han
  refine IsLittleO.of_bound ?_
  intro c hc
  filter_upwards [hcoeff, hcircle.bound hc] with n hncoeff hnbound
  have hcircle_nonneg : 0 ≤ transferCircleBound f n := (norm_nonneg (p.coeff n)).trans hncoeff
  calc ‖(‖p.coeff n‖ : ℝ)‖ = ‖p.coeff n‖ := norm_norm _
    _ ≤ transferCircleBound f n := hncoeff
    _ = ‖transferCircleBound f n‖ := (Real.norm_of_nonneg hcircle_nonneg).symm
    _ ≤ c * ‖(n : ℝ) ^ (β - 1) * Real.log n‖ := hnbound

end

/-!
# Real-valued central-binomial and Catalan asymptotics

This file reflects the complex-valued asymptotic equivalents back to their
natural real-valued forms.
-/

open Filter Asymptotics
open scoped Topology BigOperators

lemma ofReal_isEquivalent_iff {f g : ℕ → ℝ} :
    ((fun n => (f n : ℂ)) ~[atTop] (fun n => (g n : ℂ))) ↔
      f ~[atTop] g := by
  constructor
  · intro h
    rw [Asymptotics.IsEquivalent] at h ⊢
    rw [Asymptotics.isLittleO_iff] at h ⊢
    intro c hc
    specialize h hc
    filter_upwards [h] with n hn
    simpa [Pi.sub_apply, ← Complex.ofReal_sub, Complex.norm_real] using hn
  · intro h
    rw [Asymptotics.IsEquivalent] at h ⊢
    rw [Asymptotics.isLittleO_iff] at h ⊢
    intro c hc
    specialize h hc
    filter_upwards [h] with n hn
    simpa [Pi.sub_apply, ← Complex.ofReal_sub, Complex.norm_real] using hn

private lemma choose_ofReal (α : ℝ) (n : ℕ) :
    Ring.choose (((α : ℂ) + n - 1)) n =
      ((Ring.choose (α + n - 1) n : ℝ) : ℂ) := by
  rw [Ring.choose]
  rw [Ring.choose]
  change Ring.multichoose ((α : ℂ) + n - 1 - n + 1) n =
    (algebraMap ℝ ℂ) (Ring.multichoose ((α + n - 1 : ℝ) - n + 1) n)
  rw [Ring.map_multichoose (algebraMap ℝ ℂ) ((α + n - 1 : ℝ) - n + 1) n]
  congr 1
  norm_num [Complex.ofReal_add, Complex.ofReal_sub]

private lemma natCast_cpow_ofReal (α : ℝ) (n : ℕ) :
    (n : ℂ)^((α : ℂ) - 1) = (((n : ℝ)^(α - 1) : ℝ) : ℂ) := by
  have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  simpa only [Complex.ofReal_natCast, Complex.ofReal_sub, Complex.ofReal_one] using
    (Complex.ofReal_cpow hn (α - 1)).symm

theorem choose_standard_scale_real {α : ℝ} (hα : ∀ m : ℕ, α ≠ -m) :
    (fun n : ℕ => Ring.choose (α + n - 1) n) ~[atTop]
      (fun n : ℕ => (n : ℝ)^(α - 1) / Real.Gamma α) := by
  rw [← ofReal_isEquivalent_iff]
  have hαc : ∀ m : ℕ, (α : ℂ) ≠ -m := by
    intro m hm
    apply hα m
    apply Complex.ofReal_injective
    simpa [Complex.ofReal_neg] using hm
  simpa only [choose_ofReal, natCast_cpow_ofReal, Complex.ofReal_div,
    Complex.Gamma_ofReal] using
    choose_standard_scale_complex (α := (α : ℂ)) hαc

/-!
# Logarithmic singularity scale

This file adds the coefficient scale for the first logarithmic singular factor
over the standard function `(1 - z)^{-α}`.

For real `α > 1`, the exact `n`-th coefficient of
`(1 - z)^{-α} log (1 / (1 - z))` is

`choose (α + n - 1) n * ∑_{j<n} (α + j)^{-1}`,

and it is asymptotic to `(n^(α - 1) / Γ α) * log n`.

The closed form is established directly from the exact parameter derivative of
the binomial coefficients (`logSingularityCoeff_isEquivalent`).  The final
section then proves the **genuine generating-function coefficient identity**
(`logSingularityCoeff_eq_coeff_logSingularityGF`): this closed form is exactly
the `n`-th coefficient of the Cauchy product of the honest power series for
`(1 - z)^{-α}` (Mathlib's `one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero`,
coefficients `Ring.choose (α + n - 1) n`) and for `log (1 / (1 - z))`
(coefficients `n⁻¹`), so the asymptotic is a genuine statement about the
log-singularity generating function rather than an asserted scale.
-/

open Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

private lemma harmonic_real_eq_sum_inv (n : ℕ) :
    (harmonic n : ℝ) =
      ∑ j ∈ Finset.range n, (((j + 1 : ℕ) : ℝ)⁻¹) := by
  simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

private lemma shiftedHarmonic_sub_harmonic_eq_sum (α : ℝ) (n : ℕ) :
    shiftedHarmonic α n - (harmonic n : ℝ) =
      ∑ j ∈ Finset.range n, ((α + j)⁻¹ - (((j + 1 : ℕ) : ℝ)⁻¹)) := by
  rw [shiftedHarmonic, harmonic_real_eq_sum_inv, Finset.sum_sub_distrib]

private theorem harmonic_isEquivalent_log :
    (fun n : ℕ => (harmonic n : ℝ)) ~[atTop]
      (fun n : ℕ => Real.log n) := by
  rw [Asymptotics.IsEquivalent]
  have hdiff :
      Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n)
        atTop (𝓝 Real.eulerMascheroniConstant) :=
    Real.tendsto_harmonic_sub_log
  have hdiffO :
      (fun n : ℕ => (harmonic n : ℝ) - Real.log n) =O[atTop]
        (fun _ : ℕ => (1 : ℝ)) :=
    isBigO_const_of_tendsto hdiff one_ne_zero
  have hlog_atTop :
      Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have honeLittleO :
      (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun n : ℕ => Real.log n) :=
    (isLittleO_one_left_iff ℝ).mpr
      (tendsto_norm_atTop_atTop.comp hlog_atTop)
  exact hdiffO.trans_isLittleO honeLittleO

private theorem harmonic_tendsto_atTop :
    Tendsto (fun n : ℕ => (harmonic n : ℝ)) atTop atTop := by
  have hlog :
      Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdiff :
      Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n)
        atTop (𝓝 Real.eulerMascheroniConstant) :=
    Real.tendsto_harmonic_sub_log
  have hsum := hlog.atTop_add hdiff
  refine hsum.congr' ?_
  exact Eventually.of_forall fun n => by ring

private lemma shifted_harmonic_step_isLittleO (α : ℝ) (hα : 0 < α) :
    (fun n : ℕ => (α + n)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹)) =o[atTop]
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹)) := by
  refine (isLittleO_iff_tendsto ?_).mpr ?_
  · intro n hn
    exfalso
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    exact inv_ne_zero hpos.ne' hn
  · have hratio :
        (fun n : ℕ =>
            ((α + n)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹)) /
              (((n + 1 : ℕ) : ℝ)⁻¹)) =ᶠ[atTop]
          (fun n : ℕ => (1 - α) / (α + n)) := by
      refine Eventually.of_forall fun n => ?_
      have hαn : α + (n : ℝ) ≠ 0 := by positivity
      have hn1 : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp [hαn, hn1]
      rw [Nat.cast_add, Nat.cast_one]
      ring
    refine Tendsto.congr' hratio.symm ?_
    have hlin :
        Tendsto (fun n : ℕ => ((1 - α) + 0 * (n : ℝ)) / (α + 1 * (n : ℝ)))
          atTop (𝓝 (0 / (1 : ℝ))) :=
      tendsto_add_mul_div_add_mul_atTop_nhds (1 - α) α 0 (d := (1 : ℝ)) one_ne_zero
    simpa using hlin

private theorem shiftedHarmonic_sub_harmonic_isLittleO
    (α : ℝ) (hα : 0 < α) :
    (fun n : ℕ => shiftedHarmonic α n - (harmonic n : ℝ)) =o[atTop]
      (fun n : ℕ => (harmonic n : ℝ)) := by
  have hstep := shifted_harmonic_step_isLittleO α hα
  have hsum_atTop :
      Tendsto (fun n : ℕ =>
          ∑ j ∈ Finset.range n, (((j + 1 : ℕ) : ℝ)⁻¹)) atTop atTop := by
    refine harmonic_tendsto_atTop.congr' ?_
    exact Eventually.of_forall fun n => harmonic_real_eq_sum_inv n
  have hsum := hstep.sum_range
    (fun n : ℕ => by
      have hpos : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)) := by positivity
      exact inv_nonneg.mpr hpos.le)
    hsum_atTop
  refine hsum.congr' ?_ ?_
  · exact Eventually.of_forall fun n => by
      exact (shiftedHarmonic_sub_harmonic_eq_sum α n).symm
  · exact Eventually.of_forall fun n => (harmonic_real_eq_sum_inv n).symm

theorem shiftedHarmonic_isEquivalent_log {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => shiftedHarmonic α n) ~[atTop]
      (fun n : ℕ => Real.log n) := by
  have hharm := harmonic_isEquivalent_log
  have hdiff_harm := shiftedHarmonic_sub_harmonic_isLittleO α hα
  have hdiff_log :
      (fun n : ℕ => shiftedHarmonic α n - (harmonic n : ℝ)) =o[atTop]
        (fun n : ℕ => Real.log n) :=
    hdiff_harm.trans_isBigO hharm.isBigO
  have hsum :
      (fun n : ℕ => (harmonic n : ℝ) +
          (shiftedHarmonic α n - (harmonic n : ℝ))) ~[atTop]
        (fun n : ℕ => Real.log n) :=
    hharm.add_isLittleO hdiff_log
  exact hsum.congr_left (Eventually.of_forall fun n => by ring)

private lemma not_neg_nat_of_one_lt {α : ℝ} (hα : 1 < α) :
    ∀ m : ℕ, α ≠ -m := by
  intro m hm
  have hmnonneg : (0 : ℝ) ≤ m := by exact_mod_cast Nat.zero_le m
  linarith

/--
Leading-order β = 1 logarithmic singularity scale, coefficient form.

For real `α > 1`, the exact logarithmic coefficient scale
`choose (α + n - 1) n * ∑_{j<n} (α + j)^{-1}` is equivalent to
`(n^(α - 1) / Γ(α)) * log n`.
-/
theorem logSingularityCoeff_isEquivalent {α : ℝ} (hα : 1 < α) :
    (fun n : ℕ => logSingularityCoeff α n) ~[atTop]
      (fun n : ℕ => ((n : ℝ) ^ (α - 1) / Real.Gamma α) * Real.log n) := by
  have hchoose :=
    choose_standard_scale_real (α := α) (not_neg_nat_of_one_lt hα)
  have hshift := shiftedHarmonic_isEquivalent_log (α := α) (by linarith)
  simpa [logSingularityCoeff] using hchoose.mul hshift

/-!
## Genuine generating-function coefficient identity

The asymptotic above is stated for the *sequence*
`logSingularityCoeff α n = Ring.choose (α + n - 1) n * ∑_{j<n} (α + j)⁻¹`.
The purpose of this section is to prove that this sequence is genuinely the
coefficient sequence of the log-singularity generating function
`(1 - z)^{-α} · log (1 / (1 - z))`, rather than merely an asserted scale.

We work over `ℂ`, where the two factor generating functions have honest
coefficient descriptions:

* `[zⁿ] (1 - z)^{-α} = Ring.choose (α + n - 1) n` — this is exactly the
  `n`-th coefficient of the analytic power series of `fun z ↦ 1 / (1 - z)^α`
  at `0`, banked in Mathlib as
  `Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero`, whose formal
  multilinear series is `.ofScalars ℂ (fun n ↦ Ring.choose (α + n - 1) n)`.
* `[zⁿ] log (1 / (1 - z)) = [zⁿ] (-log (1 - z)) = n⁻¹` for `n ≥ 1` and `0`
  for `n = 0` — this is the standard logarithm expansion
  `∑ n, z^{n+1}/(n+1) = -log (1 - z)` (`Real`/`Complex.hasSum_pow_div_log…`).

We package these as formal power series and prove, by the Cauchy product
(`PowerSeries.coeff_mul`) together with a binomial/partial-fraction identity,
that the `n`-th coefficient of the product equals
`Ring.choose (α + n - 1) n * ∑_{j<n} (α + j)⁻¹`, i.e. `logSingularityCoeff`.
-/

open scoped PowerSeries

/-- Recurrence for the binomial coefficients, from the product formula
`Ring.choose (α + n - 1) n = (∏ j < n, (α + j)) / n!`. -/
theorem binCoeffℂ_succ (α : ℂ) (n : ℕ) :
    ((n : ℂ) + 1) * binCoeffℂ α (n + 1) = (α + n) * binCoeffℂ α n := by
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hfac' : ((n + 1).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n + 1)
  rw [binCoeffℂ, binCoeffℂ, choose_eq_prod_range_complex, choose_eq_prod_range_complex]
  rw [Finset.prod_range_succ]
  have hcast : ((n + 1).factorial : ℂ) = ((n : ℂ) + 1) * (n.factorial : ℂ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hcast]
  field_simp

/-- The Cauchy-product coefficient of the log-singularity generating function,
written as an explicit sum.  The `m = n` term vanishes because
`logCoeffℂ 0 = 0`, so the genuine `[zⁿ]` reduces to the partial-fraction sum
`∑_{m < n} binCoeffℂ α m · (n - m)⁻¹`. -/
theorem coeff_logSingularityGF (α : ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (logSingularityGF α) =
      ∑ m ∈ Finset.range n, binCoeffℂ α m * ((n : ℂ) - m)⁻¹ := by
  rw [logSingularityGF, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_range_succ]
  -- the `m = n` term: `logCoeffℂ (n - n) = logCoeffℂ 0 = 0`
  have hlast : PowerSeries.coeff (R := ℂ) n (oneSubCpowGF α) *
      PowerSeries.coeff (R := ℂ) (n - n) logGF = 0 := by
    rw [Nat.sub_self, logGF, PowerSeries.coeff_mk, logCoeffℂ, if_pos rfl, mul_zero]
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl ?_
  intro m hm
  rw [Finset.mem_range] at hm
  rw [oneSubCpowGF, PowerSeries.coeff_mk, logGF, PowerSeries.coeff_mk, logCoeffℂ]
  have hnm : n - m ≠ 0 := by omega
  rw [if_neg hnm]
  congr 1
  have : ((n - m : ℕ) : ℂ) = (n : ℂ) - m := by
    rw [Nat.cast_sub hm.le]
  rw [this]

/-- Recurrence for the closed-form coefficient:
`(n+1)·T(n+1) = (α+n)·T(n) + binCoeffℂ α n`, where `T = logSingularityCoeffℂ`.
This follows from the binomial recurrence and `H(n+1) = H(n) + (α+n)⁻¹`. -/
theorem logSingularityCoeffℂ_succ (α : ℂ) (hα : ∀ m : ℕ, α ≠ -m) (n : ℕ) :
    ((n : ℂ) + 1) * logSingularityCoeffℂ α (n + 1) =
      (α + n) * logSingularityCoeffℂ α n + binCoeffℂ α n := by
  have hαn : α + (n : ℂ) ≠ 0 := by
    intro h; exact hα n (eq_neg_of_add_eq_zero_left h)
  have hHsucc : shiftedHarmonicℂ α (n + 1) =
      shiftedHarmonicℂ α n + (α + n)⁻¹ := by
    rw [shiftedHarmonicℂ, shiftedHarmonicℂ, Finset.sum_range_succ]
  have hrec := binCoeffℂ_succ α n
  rw [logSingularityCoeffℂ, logSingularityCoeffℂ, hHsucc]
  -- `(n+1)·a_{n+1}·(H_n + (α+n)⁻¹) = (α+n)·a_n·H_n + a_n`, using `(n+1)·a_{n+1}=(α+n)·a_n`
  -- and `(α+n)·(α+n)⁻¹ = 1`.
  have hcancel : (α + (n : ℂ)) * (α + (n : ℂ))⁻¹ = 1 := mul_inv_cancel₀ hαn
  linear_combination (shiftedHarmonicℂ α n + (α + (n : ℂ))⁻¹) * hrec +
    binCoeffℂ α n * hcancel

/-- Recurrence for the Cauchy-product coefficient
`S(n) = ∑_{m < n} binCoeffℂ α m · (n - m)⁻¹`:
`(n+1)·S(n+1) = (α+n)·S(n) + binCoeffℂ α n`.
This is proved by a telescoping identity with `G(m) = m · binCoeffℂ α m · (n+1-m)⁻¹`,
using the binomial recurrence. -/
theorem convCoeff_succ (α : ℂ) (hα : ∀ m : ℕ, α ≠ -m) (n : ℕ) :
    ((n : ℂ) + 1) * (∑ m ∈ Finset.range (n + 1), binCoeffℂ α m * ((n : ℂ) + 1 - m)⁻¹) =
      (α + n) * (∑ m ∈ Finset.range n, binCoeffℂ α m * ((n : ℂ) - m)⁻¹) +
        binCoeffℂ α n := by
  -- Split off the `m = n` term on the left: `binCoeffℂ α n · (n+1-n)⁻¹ = binCoeffℂ α n`.
  rw [Finset.sum_range_succ]
  have hlast : binCoeffℂ α n * ((n : ℂ) + 1 - n)⁻¹ = binCoeffℂ α n := by
    rw [show (n : ℂ) + 1 - n = 1 by ring, inv_one, mul_one]
  rw [hlast, mul_add, mul_comm ((n : ℂ) + 1) (binCoeffℂ α n)]
  -- It remains to show
  --   (n+1)·∑_{m<n} a_m (n+1-m)⁻¹ = (α+n)·∑_{m<n} a_m (n-m)⁻¹ + (a_n·(n+1) - a_n)
  -- i.e. ∑_{m<n} a_m [ (n+1)(n+1-m)⁻¹ - (α+n)(n-m)⁻¹ ] = -n·a_n
  have hkey :
      ((n : ℂ) + 1) * (∑ m ∈ Finset.range n, binCoeffℂ α m * ((n : ℂ) + 1 - m)⁻¹) -
        (α + n) * (∑ m ∈ Finset.range n, binCoeffℂ α m * ((n : ℂ) - m)⁻¹) =
        -((n : ℂ) * binCoeffℂ α n) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    -- Telescoping: each summand equals `G m - G (m+1)` with
    -- `G m = m · binCoeffℂ α m · (n+1-m)⁻¹`.
    have htele : ∀ m ∈ Finset.range n,
        ((n : ℂ) + 1) * (binCoeffℂ α m * ((n : ℂ) + 1 - m)⁻¹) -
          (α + n) * (binCoeffℂ α m * ((n : ℂ) - m)⁻¹) =
        ((m : ℂ) * binCoeffℂ α m * ((n : ℂ) + 1 - m)⁻¹) -
          (((m : ℂ) + 1) * binCoeffℂ α (m + 1) * ((n : ℂ) - m)⁻¹) := by
      intro m hm
      rw [Finset.mem_range] at hm
      have hcast : (n : ℂ) - m = ((n - m : ℕ) : ℂ) := by
        rw [Nat.cast_sub hm.le]
      have hnm : (n : ℂ) - m ≠ 0 := by
        rw [hcast, Ne, Nat.cast_eq_zero]
        omega
      have hcast1 : (n : ℂ) + 1 - m = ((n + 1 - m : ℕ) : ℂ) := by
        rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
      have hn1m : (n : ℂ) + 1 - m ≠ 0 := by
        rw [hcast1, Ne, Nat.cast_eq_zero]
        omega
      -- use the binomial recurrence `(m+1)·a_{m+1} = (α+m)·a_m`
      have hrec := binCoeffℂ_succ α m
      have hD1 : ((n : ℂ) + 1 - m) * ((n : ℂ) + 1 - m)⁻¹ = 1 := mul_inv_cancel₀ hn1m
      have hD0 : ((n : ℂ) - m) * ((n : ℂ) - m)⁻¹ = 1 := mul_inv_cancel₀ hnm
      -- substitute the recurrence into the `a_{m+1}` term
      have hsub : ((m : ℂ) + 1) * binCoeffℂ α (m + 1) * ((n : ℂ) - m)⁻¹ =
          (α + m) * binCoeffℂ α m * ((n : ℂ) - m)⁻¹ := by
        rw [hrec]
      rw [hsub]
      -- now both sides are `a_m · (bracket)`; the bracket identity reduces to
      -- `(n+1-m)·D1⁻¹ = (n-m)·D0⁻¹`, i.e. `1 = 1`.
      have hbr :
          ((n : ℂ) + 1) * ((n : ℂ) + 1 - m)⁻¹ - (α + n) * ((n : ℂ) - m)⁻¹ =
            (m : ℂ) * ((n : ℂ) + 1 - m)⁻¹ - (α + m) * ((n : ℂ) - m)⁻¹ := by
        have e1 : ((n : ℂ) + 1) * ((n : ℂ) + 1 - m)⁻¹ -
              (m : ℂ) * ((n : ℂ) + 1 - m)⁻¹ =
            ((n : ℂ) + 1 - m) * ((n : ℂ) + 1 - m)⁻¹ := by ring
        have e2 : (α + n) * ((n : ℂ) - m)⁻¹ - (α + m) * ((n : ℂ) - m)⁻¹ =
            ((n : ℂ) - m) * ((n : ℂ) - m)⁻¹ := by ring
        have key : ((n : ℂ) + 1) * ((n : ℂ) + 1 - m)⁻¹ -
              (m : ℂ) * ((n : ℂ) + 1 - m)⁻¹ =
            (α + n) * ((n : ℂ) - m)⁻¹ - (α + m) * ((n : ℂ) - m)⁻¹ := by
          rw [e1, e2, hD1, hD0]
        linear_combination key
      linear_combination binCoeffℂ α m * hbr
    rw [Finset.sum_congr rfl htele]
    -- telescoping sum: ∑_{m<n} (G m - G (m+1)) = G 0 - G n
    have := Finset.sum_range_sub'
      (fun m : ℕ => (m : ℂ) * binCoeffℂ α m * ((n : ℂ) + 1 - m)⁻¹) n
    -- align the second term's denominator `(n - m)⁻¹` with `(n+1-(m+1))⁻¹`
    have halign : ∀ m ∈ Finset.range n,
        ((m : ℂ) * binCoeffℂ α m * ((n : ℂ) + 1 - m)⁻¹) -
          (((m : ℂ) + 1) * binCoeffℂ α (m + 1) * ((n : ℂ) - m)⁻¹) =
        (fun m : ℕ => (m : ℂ) * binCoeffℂ α m * ((n : ℂ) + 1 - m)⁻¹) m -
          (fun m : ℕ => (m : ℂ) * binCoeffℂ α m * ((n : ℂ) + 1 - m)⁻¹) (m + 1) := by
      intro m hm
      simp only
      have hden : (n : ℂ) - m = (n : ℂ) + 1 - ((m : ℂ) + 1) := by ring
      rw [hden]
      push_cast
      ring
    rw [Finset.sum_congr rfl halign, this]
    -- G 0 - G n = 0 - n·a_n·1 = -(n·a_n)
    simp only [Nat.cast_zero, zero_mul, zero_sub]
    rw [show (n : ℂ) + 1 - n = 1 by ring, inv_one, mul_one]
  linear_combination hkey

/-- **The closed form is the genuine Cauchy-product coefficient.** The explicit
sum `∑_{m < n} binCoeffℂ α m · (n - m)⁻¹` (the `[zⁿ]` of the product GF) equals
`Ring.choose (α + n - 1) n * ∑_{j < n} (α + j)⁻¹ = logSingularityCoeffℂ α n`.

Both sides satisfy the same first-order recurrence
`(n+1)·x(n+1) = (α+n)·x(n) + binCoeffℂ α n` with `x 0 = 0`, hence agree. -/
theorem sum_partialFraction_eq_logSingularityCoeffℂ (α : ℂ) (hα : ∀ m : ℕ, α ≠ -m)
    (n : ℕ) :
    (∑ m ∈ Finset.range n, binCoeffℂ α m * ((n : ℂ) - m)⁻¹) =
      logSingularityCoeffℂ α n := by
  induction n with
  | zero =>
      simp [logSingularityCoeffℂ, shiftedHarmonicℂ]
  | succ n ih =>
      have hn1 : ((n : ℂ) + 1) ≠ 0 := by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        intro h
        apply_fun Complex.re at h
        simp at h
        linarith
      have hconv := convCoeff_succ α hα n
      rw [ih] at hconv
      have hT := logSingularityCoeffℂ_succ α hα n
      have hcastn : ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 := by push_cast; ring
      have hgoal :
          ((n : ℂ) + 1) *
            (∑ m ∈ Finset.range (n + 1), binCoeffℂ α m * (((n + 1 : ℕ) : ℂ) - m)⁻¹) =
          ((n : ℂ) + 1) * logSingularityCoeffℂ α (n + 1) := by
        rw [hcastn, hconv, hT]
      exact mul_left_cancel₀ hn1 hgoal

/-- **GF ↔ coefficient identity (complex form).** The `n`-th coefficient of the
genuine log-singularity generating function `(1 - z)^{-α} · log (1 / (1 - z))`
equals the closed form `Ring.choose (α + n - 1) n * ∑_{j < n} (α + j)⁻¹`. -/
theorem coeff_logSingularityGF_eq_logSingularityCoeffℂ (α : ℂ) (hα : ∀ m : ℕ, α ≠ -m)
    (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (logSingularityGF α) = logSingularityCoeffℂ α n := by
  rw [coeff_logSingularityGF, sum_partialFraction_eq_logSingularityCoeffℂ α hα n]

/-- The complex closed form restricts to the real `logSingularityCoeff` for real
`α` and `n`: `(logSingularityCoeff α n : ℂ) = logSingularityCoeffℂ α n`. -/
theorem logSingularityCoeff_cast (α : ℝ) (n : ℕ) :
    (logSingularityCoeff α n : ℂ) = logSingularityCoeffℂ (α : ℂ) n := by
  have hchoose : Ring.choose (((α : ℂ) + n - 1)) n =
      ((Ring.choose (α + n - 1) n : ℝ) : ℂ) := by
    rw [Ring.choose, Ring.choose]
    change Ring.multichoose ((α : ℂ) + n - 1 - n + 1) n =
      (algebraMap ℝ ℂ) (Ring.multichoose ((α + n - 1 : ℝ) - n + 1) n)
    rw [Ring.map_multichoose (algebraMap ℝ ℂ) ((α + n - 1 : ℝ) - n + 1) n]
    congr 1
    norm_num [Complex.ofReal_add, Complex.ofReal_sub]
  have hharm : ((shiftedHarmonic α n : ℝ) : ℂ) = shiftedHarmonicℂ (α : ℂ) n := by
    rw [shiftedHarmonic, shiftedHarmonicℂ, Complex.ofReal_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_natCast]
  rw [logSingularityCoeff, logSingularityCoeffℂ, binCoeffℂ, Complex.ofReal_mul,
    ← hchoose, hharm]

/-- **Main faithfulness theorem.** For real `α` that is not a nonpositive
integer, the real coefficient scale `logSingularityCoeff α n` is exactly the
`n`-th coefficient of the genuine log-singularity generating function
`(1 - z)^{-α} · log (1 / (1 - z))` (as a complex formal power series whose
factor coefficients are the honest Taylor coefficients of `(1 - z)^{-α}` and of
`log (1 / (1 - z))`).

This upgrades `logSingularityCoeff_isEquivalent` from a statement about an
asserted scale to a genuine generating-function coefficient asymptotic. -/
theorem logSingularityCoeff_eq_coeff_logSingularityGF {α : ℝ}
    (hα : ∀ m : ℕ, (α : ℂ) ≠ -m) (n : ℕ) :
    (logSingularityCoeff α n : ℂ) =
      PowerSeries.coeff (R := ℂ) n (logSingularityGF (α : ℂ)) := by
  rw [logSingularityCoeff_cast,
    coeff_logSingularityGF_eq_logSingularityCoeffℂ (α : ℂ) hα n]

end

/-!
# Discharging the model-faithfulness hypotheses of the logarithmic transfer

`log_transfer_theorem_strong_remainder` (LogTransfer) carries two model-faithfulness hypotheses for
`logSingularityFun α = (1−z)^{−α}·(−log(1−z))`:

* `hΔ_log` — delta-domain analyticity, and
* `hp_log` — its power series at `0` is `logSingularityGF α`.

This file discharges `hΔ_log` (mechanical, via `AnalyticOnNhd.clog` on the slit plane) and the
algebraic-factor half of `hp_log`.  The remaining piece of `hp_log` is the *complex* Taylor series
`−log(1−z) = ∑ zⁿ⁺¹/(n+1)` (Mathlib has only the real analogue) together with a Cauchy-product
realization — a genuine analytic bridge handled separately.
-/

noncomputable section

open Complex Filter Asymptotics
open scoped Topology BigOperators

/-- Delta-domain analyticity of the logarithmic factor `-log(1-z)` (principal branch). -/
lemma analyticOnNhd_negLog_one_sub_deltaDomain {R φ : ℝ} (hφ0 : 0 < φ) :
    AnalyticOnNhd ℂ (fun z : ℂ => -Complex.log (1 - z)) (DeltaDomainArg R φ) := by
  have hlog : AnalyticOnNhd ℂ (fun z : ℂ => Complex.log (1 - z)) (DeltaDomainArg R φ) :=
    (analyticOnNhd_const.sub analyticOnNhd_id).clog
      (fun z hz => one_sub_mem_slitPlane_of_mem_delta hφ0 hz)
  simpa [smul_eq_mul] using hlog.const_smul (c := (-1 : ℂ))

/-- **Discharges `hΔ_log`**: delta-domain analyticity of the log-singularity model. -/
lemma analyticOnNhd_logSingularityFun_deltaDomain {α : ℂ} {R φ : ℝ}
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi) :
    AnalyticOnNhd ℂ (logSingularityFun α) (DeltaDomainArg R φ) := by
  have hpow : AnalyticOnNhd ℂ (fun z : ℂ => (1 - z) ^ (-α)) (DeltaDomainArg R φ) :=
    analyticOnNhd_one_sub_cpow_deltaDomain (α := α) (R := R) (φ := φ) hφ0 hφπ
  have hlog : AnalyticOnNhd ℂ (fun z : ℂ => -Complex.log (1 - z)) (DeltaDomainArg R φ) :=
    analyticOnNhd_negLog_one_sub_deltaDomain (R := R) (φ := φ) hφ0
  unfold logSingularityFun
  exact hpow.mul hlog

end

/-!
# Model faithfulness `hp_log` for the logarithmic transfer

Discharges the remaining hypothesis of `log_transfer_theorem_strong_remainder`:

  `logSingularityFun_hasFPowerSeriesAt : HasFPowerSeriesAt (logSingularityFun α) (toFMLS (logSingularityGF α)) 0`.

Route (ChatGPT-Pro R27): work directly via `hasFPowerSeriesAt_iff` and a per-`z` `HasSum`, avoiding the
absent `HasFPowerSeriesAt.mul`/FMLS multiplication and the radius computation.  The two factor series
(`oneSubCpowGF` from Mathlib's cpow series, `logGF` from `ComplexLogSeries`) are multiplied by an
ordinary Cauchy product (`hasSum_powerSeries_mul`), whose coefficient is `PowerSeries.coeff_mul`.
-/

open Complex Filter Asymptotics
open scoped Topology BigOperators ENNReal NNReal

namespace AnalyticCombinatorics

lemma logCoeffℂ_eq_inv (n : ℕ) : logCoeffℂ n = (n : ℂ)⁻¹ := by
  cases n <;> simp [logCoeffℂ]

/-- The `logGF` coefficient series is norm-summable on the unit ball. -/
lemma logGF_summable_norm {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n logGF * z ^ n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_geometric_of_lt_one (norm_nonneg z) hz)
  rw [norm_mul, norm_pow, logGF, PowerSeries.coeff_mk, logCoeffℂ_eq_inv]
  rcases n with _ | m
  · simp
  · rw [norm_inv, Complex.norm_natCast]
    calc (((m + 1 : ℕ) : ℝ))⁻¹ * ‖z‖ ^ (m + 1)
        ≤ 1 * ‖z‖ ^ (m + 1) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [inv_le_one_iff₀]; right; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero m)
      _ = ‖z‖ ^ (m + 1) := one_mul _
      _ ≤ ‖z‖ ^ (m + 1) := le_rfl

/-- `logGF` realizes `-log(1-z)` on the unit ball. -/
lemma logGF_hasSum {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n logGF * z ^ n) (-Complex.log (1 - z)) := by
  have hraw := AnalyticCombinatorics.hasSum_pow_succ_div_succ_neg_log (z := z) hz
  have hzero : PowerSeries.coeff (R := ℂ) 0 logGF * z ^ 0 = 0 := by
    simp [logGF, logCoeffℂ]
  have htail : HasSum
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) (n + 1) logGF * z ^ (n + 1))
      (-Complex.log (1 - z)) := by
    have : (fun n : ℕ => PowerSeries.coeff (R := ℂ) (n + 1) logGF * z ^ (n + 1))
        = fun n : ℕ => z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) := by
      funext n
      rw [logGF, PowerSeries.coeff_mk, logCoeffℂ_eq_inv]
      push_cast; ring
    rw [this]; exact hraw
  have hf0 : ∀ x ∉ Set.range Nat.succ,
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n logGF * z ^ n) x = 0 := by
    intro x hx
    rcases x with _ | m
    · simpa using hzero
    · exact absurd ⟨m, rfl⟩ hx
  exact (Function.Injective.hasSum_iff Nat.succ_injective hf0).mp htail

/-- The cpow factor `(1-z)^{-α}` realizes `oneSubCpowGF α` on the unit ball. -/
lemma oneSubCpowGF_hasSum {α z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n (oneSubCpowGF α) * z ^ n)
      ((1 - z) ^ (-α)) := by
  have h := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero α)
  have hzball : z ∈ Metric.eball (0 : ℂ) 1 := by
    rw [mem_emetric_ball_zero_iff, enorm_eq_nnnorm]
    exact_mod_cast hz
  have hsum := h.hasSum hzball
  rw [Complex.cpow_neg, inv_eq_one_div]
  simpa [oneSubCpowGF, PowerSeries.coeff_mk, binCoeffℂ,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm, zero_add] using hsum

/-- The cpow factor series is norm-summable on the unit ball. -/
lemma oneSubCpowGF_summable_norm {α z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n (oneSubCpowGF α) * z ^ n‖) := by
  have h := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero α)
  set p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun n => Ring.choose (α + n - 1) n) with hp
  have hlt : (‖z‖₊ : ℝ≥0∞) < p.radius := lt_of_lt_of_le (by exact_mod_cast hz) h.r_le
  refine (p.summable_norm_mul_pow hlt).congr (fun n => ?_)
  rw [norm_mul, norm_pow, hp, FormalMultilinearSeries.ofScalars_norm,
    oneSubCpowGF, PowerSeries.coeff_mk, binCoeffℂ, coe_nnnorm]

/-- **Cauchy product** for ordinary `PowerSeries ℂ` evaluated at `z`, in `HasSum` form.
Replaces the absent `HasFPowerSeriesAt.mul`. -/
lemma hasSum_powerSeries_mul (F G : PowerSeries ℂ) {z A B : ℂ}
    (hF : HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n F * z ^ n) A)
    (hG : HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n G * z ^ n) B)
    (habsF : Summable (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n F * z ^ n‖))
    (habsG : Summable (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n G * z ^ n‖)) :
    HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n (F * G) * z ^ n) (A * B) := by
  classical
  have hcoeff : ∀ n : ℕ,
      (∑ p ∈ Finset.antidiagonal n,
        (PowerSeries.coeff (R := ℂ) p.1 F * z ^ p.1) *
          (PowerSeries.coeff (R := ℂ) p.2 G * z ^ p.2))
        = PowerSeries.coeff (R := ℂ) n (F * G) * z ^ n := by
    intro n
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.mem_antidiagonal] at hp
    rw [← hp, pow_add]; ring
  have hval : A * B
      = ∑' n : ℕ, PowerSeries.coeff (R := ℂ) n (F * G) * z ^ n := by
    rw [← hF.tsum_eq, ← hG.tsum_eq,
      tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm habsF habsG]
    exact tsum_congr hcoeff
  have hsummable : Summable (fun n : ℕ => PowerSeries.coeff (R := ℂ) n (F * G) * z ^ n) :=
    (summable_sum_mul_antidiagonal_of_summable_norm' habsF habsF.of_norm habsG habsG.of_norm).congr
      hcoeff
  rw [hval]; exact hsummable.hasSum

/-- **Discharges `hp_log`**: `logSingularityFun α` has power series `logSingularityGF α` at `0`. -/
theorem logSingularityFun_hasFPowerSeriesAt (α : ℂ) :
    HasFPowerSeriesAt (logSingularityFun α) (PowerSeries.toFMLS (logSingularityGF α)) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
  have hz_norm : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hprod := hasSum_powerSeries_mul (oneSubCpowGF α) logGF
    (oneSubCpowGF_hasSum (α := α) (z := z) hz_norm)
    (logGF_hasSum (z := z) hz_norm)
    (oneSubCpowGF_summable_norm (α := α) (z := z) hz_norm)
    (logGF_summable_norm (z := z) hz_norm)
  simpa [logSingularityGF, logSingularityFun, PowerSeries.coeff_toFMLS,
    smul_eq_mul, mul_comm] using hprod

end AnalyticCombinatorics

/-!
# Flajolet–Odlyzko logarithmic transfer — natural-remainder form

`LogTransfer.lean` proves the *strong-remainder* logarithmic transfer, whose residual
hypothesis is `f − C·(1−z)^{−α}·(−log(1−z)) = o(|1−z|^{−α})` (one log factor stronger
than the textbook statement).  This file removes that caveat: the **natural** residual

  `f − C·(1−z)^{−α}·(−log(1−z)) = o(|1−z|^{−α} · log(1/|1−z|))`

(encoded via `‖·‖·‖1−z‖^α / log(1/‖1−z‖) → 0`) still yields

  `[zⁿ]f ~ C · n^{α−1}/Γ(α) · log n`.

The new analytic content is the log-weighted Hankel/Cauchy contour estimate
`coeff_norm_isLittleO_atTop_of_delta_littleO_log_beta_gt_one` (in `LittleOTransfer`),
which supplies the error term `o(n^{α−1} log n)` directly — no algebraic absorption.
-/

noncomputable section

open Complex Filter Asymptotics
open scoped Topology BigOperators

/-- **Natural-remainder logarithmic transfer theorem.**  For real `α > 1`, if `f` is
`Δ`-analytic and `f − C·(1−z)^{−α}·(−log(1−z))` is `o(|1−z|^{−α} log(1/|1−z|))` near `1`,
then `[zⁿ]f ~ C·n^{α−1}/Γ(α)·log n`.  Faithfulness (`hp_log`, `hΔ_log`) is supplied
externally; the unconditional form below discharges it. -/
theorem log_transfer_theorem_natural_remainder
    {α : ℝ} {C : ℂ} {R φ : ℝ} {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hα : 1 < α) (hC : C ≠ 0) (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hp_log : HasFPowerSeriesAt (logSingularityFun (α : ℂ))
      (PowerSeries.toFMLS (logSingularityGF (α : ℂ))) 0)
    (hΔ_log : AnalyticOnNhd ℂ (logSingularityFun (α : ℂ)) (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ => ‖f z - C * logSingularityFun (α : ℂ) z‖ * ‖(1 : ℂ) - z‖ ^ α
        * (Real.log (‖(1 : ℂ) - z‖⁻¹))⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ => p.coeff n) ~[atTop]
      (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n : ℝ) : ℂ)) := by
  classical
  set q : FormalMultilinearSeries ℂ ℂ ℂ := PowerSeries.toFMLS (logSingularityGF (α : ℂ)) with hq
  have hαneg : ∀ m : ℕ, (α : ℂ) ≠ -m := by
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
    have : (0 : ℝ) ≤ (m : ℝ) := by positivity
    linarith
  have hqcoeff : ∀ n, q.coeff n = (logSingularityCoeff α n : ℂ) := by
    intro n
    rw [hq, logSingularityCoeff_eq_coeff_logSingularityGF hαneg, PowerSeries.coeff_toFMLS]
  have hmain : (fun n : ℕ => C * q.coeff n)
      ~[atTop] (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n : ℝ) : ℂ)) := by
    have hcomplex : (fun n : ℕ => (logSingularityCoeff α n : ℂ))
        ~[atTop] (fun n : ℕ => (((n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n : ℝ) : ℂ)) := by
      rw [ofReal_isEquivalent_iff]
      simpa [mul_assoc] using logSingularityCoeff_isEquivalent hα
    have hconst : (fun _ : ℕ => C) ~[atTop] (fun _ : ℕ => C) := Asymptotics.IsEquivalent.refl
    have hmul := hconst.mul hcomplex
    simp only [hqcoeff]
    exact hmul
  have hpg : HasFPowerSeriesAt (fun z : ℂ => f z - C • logSingularityFun (α : ℂ) z)
      (p - C • q) 0 := hp.sub (hp_log.const_smul (c := C))
  have hΔg : AnalyticOnNhd ℂ (fun z : ℂ => f z - C • logSingularityFun (α : ℂ) z)
      (DeltaDomainArg R φ) := hΔ.sub (hΔ_log.const_smul (c := C))
  have herr_norm : (fun n : ℕ => ‖(p - C • q).coeff n‖)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 1) * Real.log n) := by
    refine coeff_norm_isLittleO_atTop_of_delta_littleO_log_beta_gt_one
      (R := R) (φ := φ) (β := α)
      (f := fun z : ℂ => f z - C • logSingularityFun (α : ℂ) z) (p := p - C • q)
      hR hφ0 hφ2 hpg hΔg ?_ hα
    simpa [smul_eq_mul] using hsing
  have hΓ : 0 < Real.Gamma α := Real.Gamma_pos_of_pos (by linarith)
  have hCnorm : 0 < ‖C‖ := norm_pos_iff.mpr hC
  have hscale_bigO : (fun n : ℕ => (n : ℝ) ^ (α - 1) * Real.log n)
      =O[atTop] (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n : ℝ) : ℂ)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨Real.Gamma α / ‖C‖, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1R
    have hpow : 0 ≤ (n : ℝ) ^ (α - 1) := (Real.rpow_pos_of_pos (by linarith) _).le
    have hxnn : 0 ≤ (n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n := by positivity
    apply le_of_eq
    rw [Real.norm_of_nonneg (by positivity), norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hxnn]
    field_simp
  have herr_target : (fun n : ℕ => (p - C • q).coeff n)
      =o[atTop] (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n : ℝ) : ℂ)) :=
    (Asymptotics.IsLittleO.of_norm_left herr_norm).trans_isBigO hscale_bigO
  have hsum : (fun n : ℕ => C * q.coeff n + (p - C • q).coeff n)
      ~[atTop] (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n : ℝ) : ℂ)) :=
    hmain.add_isLittleO herr_target
  have hdecomp : (fun n : ℕ => p.coeff n)
      =ᶠ[atTop] (fun n : ℕ => C * q.coeff n + (p - C • q).coeff n) := by
    refine Eventually.of_forall fun n => ?_
    show p.coeff n = C * q.coeff n + (p - C • q).coeff n
    have hcs : (p - C • q).coeff n = p.coeff n - C * q.coeff n := by
      change (p n - (C • q) n) 1 = p n 1 - C * q.coeff n
      rw [FormalMultilinearSeries.smul_apply,
        ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.smul_apply]
      change p.coeff n - C • q.coeff n = p.coeff n - C * q.coeff n
      simp [smul_eq_mul]
    rw [hcs]; ring
  exact hdecomp.trans_isEquivalent hsum

end

open AnalyticCombinatorics
open Complex Filter Asymptotics
open scoped Topology BigOperators
theorem solution
    {α : ℝ} {C : ℂ} {R φ : ℝ} {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hα : 1 < α) (hC : C ≠ 0) (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ => ‖f z - C * logSingularityFun (α : ℂ) z‖ * ‖(1 : ℂ) - z‖ ^ α
        * (Real.log (‖(1 : ℂ) - z‖⁻¹))⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ => p.coeff n) ~[atTop]
      (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n : ℝ) : ℂ)) :=
  log_transfer_theorem_natural_remainder hα hC hR hφ0 hφ2 hp hΔ
    (logSingularityFun_hasFPowerSeriesAt (α : ℂ))
    (analyticOnNhd_logSingularityFun_deltaDomain hφ0 (by linarith [Real.pi_pos] : φ < Real.pi))
    hsing
