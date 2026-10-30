-- Prove2me | solution 1 for transfer_theorem
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-25T12:44:42.501783+00:00
-- url     : https://prove2.me/submissions/1bd52874-14ca-485d-a10d-2f294bae1e60

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_DeltaDomain
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_DeltaGeometry
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_CoeffDescent
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_LittleOTransfer
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
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

theorem coeff_oneDivOneSubCpow_isEquivalent {α : ℂ} (hα : ∀ m : ℕ, α ≠ -m) :
    (fun n : ℕ =>
      ((FormalMultilinearSeries.ofScalars ℂ
        (fun n : ℕ => Ring.choose (α + n - 1) n)).coeff n)) ~[atTop]
      (fun n : ℕ => (n : ℂ)^(α - 1) / Complex.Gamma α) := by
  simpa using choose_standard_scale_complex hα

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

lemma local_disk_norm_comparable {κ : ℝ} {z w : ℂ}
    (hw : w ∈ Metric.ball z (κ * ‖1 - z‖)) :
    (1 - κ) * ‖1 - z‖ ≤ ‖1 - w‖ ∧
      ‖1 - w‖ ≤ (1 + κ) * ‖1 - z‖ := by
  have hdist : ‖w - z‖ < κ * ‖1 - z‖ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  constructor
  · have hrev : ‖1 - z‖ - ‖w - z‖ ≤ ‖1 - w‖ := by
      have h := norm_sub_norm_le (1 - z) (w - z)
      convert h using 1
      ring_nf
    have hpre : (1 - κ) * ‖1 - z‖ ≤ ‖1 - z‖ - ‖w - z‖ := by
      nlinarith [le_of_lt hdist]
    exact hpre.trans hrev
  · have htri : ‖1 - w‖ ≤ ‖1 - z‖ + ‖w - z‖ := by
      calc
        ‖1 - w‖ = ‖(1 - z) + (z - w)‖ := by ring_nf
        _ ≤ ‖1 - z‖ + ‖z - w‖ := norm_add_le _ _
        _ = ‖1 - z‖ + ‖w - z‖ := by simp [norm_sub_rev z w]
    have hpre : ‖1 - z‖ + ‖w - z‖ ≤ (1 + κ) * ‖1 - z‖ := by
      nlinarith [le_of_lt hdist]
    exact htri.trans hpre

lemma local_disk_norm_comparable_half {κ : ℝ} (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    {z w : ℂ} (hw : w ∈ Metric.ball z (κ * ‖1 - z‖)) :
    (1 / 2) * ‖1 - z‖ ≤ ‖1 - w‖ ∧ ‖1 - w‖ ≤ 2 * ‖1 - z‖ := by
  have hcomp := local_disk_norm_comparable hw
  constructor
  · have hleft : (1 / 2 : ℝ) * ‖1 - z‖ ≤ (1 - κ) * ‖1 - z‖ := by
      nlinarith [norm_nonneg (1 - z)]
    exact hleft.trans hcomp.1
  · have hright : (1 + κ) * ‖1 - z‖ ≤ 2 * ‖1 - z‖ := by
      nlinarith [norm_nonneg (1 - z)]
    exact hcomp.2.trans hright

lemma local_disk_subset_deltaDomain {R R' φ φ' κ : ℝ} (_hRR : R' < R)
    (hφ : 0 < φ) (hφlt : φ < φ') (hφ'2 : φ' < Real.pi / 2)
    (hκ0 : 0 ≤ κ) (_hκ1 : κ < 1)
    (hκR : κ * (1 + R') ≤ R - R')
    (hκAngle : κ * (1 + Real.cos φ) ≤ Real.cos φ - Real.cos φ') {z : ℂ}
    (hz : z ∈ DeltaDomainArg R' φ') :
    Metric.ball z (κ * ‖1 - z‖) ⊆ DeltaDomainArg R φ := by
  have hφ' : 0 < φ' := lt_trans hφ hφlt
  have hφπ : φ < Real.pi := by linarith [hφlt, hφ'2, Real.pi_pos]
  have hφ'π : φ' < Real.pi := by linarith [hφ'2, Real.pi_pos]
  have hz_geom : z ∈ DeltaDomainGeom R' φ' := by
    simpa only [delta_arg_eq_geom hφ'.le hφ'π] using hz
  rcases hz_geom with ⟨hzRball, hzangle⟩
  have hzR : ‖z‖ < R' := by
    simpa [Metric.mem_ball, dist_eq_norm] using hzRball
  rw [delta_arg_eq_geom hφ.le hφπ]
  intro w hw
  unfold DeltaDomainGeom
  have hdist : ‖w - z‖ < κ * ‖1 - z‖ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  constructor
  · have h1z_le : ‖1 - z‖ ≤ 1 + R' := by
      calc
        ‖1 - z‖ = ‖(1 : ℂ) + (-z)‖ := by ring_nf
        _ ≤ ‖(1 : ℂ)‖ + ‖-z‖ := norm_add_le _ _
        _ = 1 + ‖z‖ := by simp
        _ ≤ 1 + R' := by linarith
    have hdist_lt : ‖w - z‖ < κ * (1 + R') :=
      lt_of_lt_of_le hdist (mul_le_mul_of_nonneg_left h1z_le hκ0)
    have hw_norm_le : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
      calc
        ‖w‖ = ‖z + (w - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
    have hw_norm_lt : ‖w‖ < R := by
      have hsum : ‖z‖ + ‖w - z‖ < R' + κ * (1 + R') := add_lt_add hzR hdist_lt
      have hpre : ‖w‖ < R' + κ * (1 + R') := lt_of_le_of_lt hw_norm_le hsum
      have hmargin : R' + κ * (1 + R') ≤ R := by linarith
      exact lt_of_lt_of_le hpre hmargin
    simpa [Metric.mem_ball, dist_eq_norm] using hw_norm_lt
  · have hcos_pos : 0 < Real.cos φ := by
      exact Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hφ, Real.pi_pos], by linarith [hφlt, hφ'2]⟩
    have hzangle' : (z - 1).re < Real.cos φ' * ‖1 - z‖ := by
      simpa [norm_sub_rev z 1] using hzangle
    have hre_le : (w - 1).re ≤ (z - 1).re + ‖w - z‖ := by
      calc
        (w - 1).re = ((z - 1) + (w - z)).re := by ring_nf
        _ = (z - 1).re + (w - z).re := by rw [Complex.add_re]
        _ ≤ (z - 1).re + ‖w - z‖ := by linarith [Complex.re_le_norm (w - z)]
    have hpre_lt : (w - 1).re < (Real.cos φ' + κ) * ‖1 - z‖ := by
      calc
        (w - 1).re ≤ (z - 1).re + ‖w - z‖ := hre_le
        _ < Real.cos φ' * ‖1 - z‖ + κ * ‖1 - z‖ := add_lt_add hzangle' hdist
        _ = (Real.cos φ' + κ) * ‖1 - z‖ := by ring
    have hcoeff : Real.cos φ' + κ ≤ Real.cos φ * (1 - κ) := by
      nlinarith [hκAngle]
    have hcoeff_mul : (Real.cos φ' + κ) * ‖1 - z‖ ≤
        Real.cos φ * ((1 - κ) * ‖1 - z‖) := by
      have h := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg (1 - z))
      nlinarith
    have hcomp : (1 - κ) * ‖1 - z‖ ≤ ‖1 - w‖ :=
      (local_disk_norm_comparable hw).1
    have htarget : Real.cos φ * ((1 - κ) * ‖1 - z‖) ≤ Real.cos φ * ‖1 - w‖ :=
      mul_le_mul_of_nonneg_left hcomp hcos_pos.le
    have hfinal : (w - 1).re < Real.cos φ * ‖1 - w‖ :=
      hpre_lt.trans_le (hcoeff_mul.trans htarget)
    simpa [norm_sub_rev w 1] using hfinal

lemma local_disk_subset_deltaDomain_deltaLocalKappa {R R' φ φ' : ℝ} (hR'0 : 0 < R')
    (hRR : R' < R) (hφ : 0 < φ) (hφlt : φ < φ')
    (hφ'2 : φ' < Real.pi / 2) {z : ℂ} (hz : z ∈ DeltaDomainArg R' φ') :
    Metric.ball z (deltaLocalKappa R R' φ φ' * ‖1 - z‖) ⊆ DeltaDomainArg R φ := by
  have hφ' : 0 < φ' := lt_trans hφ hφlt
  have hφπ : φ < Real.pi := by linarith [hφlt, hφ'2, Real.pi_pos]
  have hφ'π : φ' < Real.pi := by linarith [hφ'2, Real.pi_pos]
  have hcos_lt : Real.cos φ' < Real.cos φ := by
    exact (Real.strictAntiOn_cos.lt_iff_gt
      (Set.mem_Icc.mpr ⟨hφ'.le, hφ'π.le⟩)
      (Set.mem_Icc.mpr ⟨hφ.le, hφπ.le⟩)).2 hφlt
  have hcos_pos : 0 < Real.cos φ := by
    exact Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hφ, Real.pi_pos], by linarith [hφlt, hφ'2]⟩
  have hRdiff_pos : 0 < R - R' := by linarith
  have hdenR_pos : 0 < 2 * (1 + R') := by nlinarith
  have hdenA_pos : 0 < 2 * (1 + Real.cos φ) := by nlinarith
  have hκ0 : 0 ≤ deltaLocalKappa R R' φ φ' := by
    unfold deltaLocalKappa
    apply le_min
    · norm_num
    · apply le_min
      · exact div_nonneg hRdiff_pos.le hdenR_pos.le
      · exact div_nonneg (sub_nonneg.mpr hcos_lt.le) hdenA_pos.le
  have hκ1 : deltaLocalKappa R R' φ φ' < 1 := by
    have hle : deltaLocalKappa R R' φ φ' ≤ 1 / 2 := by
      unfold deltaLocalKappa
      exact min_le_left _ _
    linarith
  have hκR : deltaLocalKappa R R' φ φ' * (1 + R') ≤ R - R' := by
    have hle_rad : deltaLocalKappa R R' φ φ' ≤ (R - R') / (2 * (1 + R')) := by
      unfold deltaLocalKappa
      exact (min_le_right _ _).trans (min_le_left _ _)
    have h1R_pos : 0 < 1 + R' := by linarith
    have hmul := mul_le_mul_of_nonneg_right hle_rad h1R_pos.le
    have hrad_mul : ((R - R') / (2 * (1 + R'))) * (1 + R') = (R - R') / 2 := by
      field_simp [h1R_pos.ne']
    calc
      deltaLocalKappa R R' φ φ' * (1 + R')
          ≤ ((R - R') / (2 * (1 + R'))) * (1 + R') := hmul
      _ = (R - R') / 2 := hrad_mul
      _ ≤ R - R' := by linarith
  have hκAngle : deltaLocalKappa R R' φ φ' * (1 + Real.cos φ) ≤
      Real.cos φ - Real.cos φ' := by
    have hle_ang : deltaLocalKappa R R' φ φ' ≤
        (Real.cos φ - Real.cos φ') / (2 * (1 + Real.cos φ)) := by
      unfold deltaLocalKappa
      exact (min_le_right _ _).trans (min_le_right _ _)
    have h1cos_pos : 0 < 1 + Real.cos φ := by linarith
    have hmul := mul_le_mul_of_nonneg_right hle_ang h1cos_pos.le
    have hang_mul : ((Real.cos φ - Real.cos φ') / (2 * (1 + Real.cos φ))) *
        (1 + Real.cos φ) = (Real.cos φ - Real.cos φ') / 2 := by
      field_simp [h1cos_pos.ne']
    calc
      deltaLocalKappa R R' φ φ' * (1 + Real.cos φ)
          ≤ ((Real.cos φ - Real.cos φ') / (2 * (1 + Real.cos φ))) *
              (1 + Real.cos φ) := hmul
      _ = (Real.cos φ - Real.cos φ') / 2 := hang_mul
      _ ≤ Real.cos φ - Real.cos φ' := by linarith
  exact local_disk_subset_deltaDomain hRR hφ hφlt hφ'2 hκ0 hκ1 hκR hκAngle hz

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

private lemma one_div_nat_rpow (β : ℝ) {n : ℕ} (hn : 0 < n) :
    ((1 : ℝ) / n) ^ (1 - β) = (n : ℝ) ^ (β - 1) := by
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  rw [one_div, Real.inv_rpow hn_nonneg]
  rw [show 1 - β = -(β - 1) by ring]
  rw [Real.rpow_neg hn_nonneg]
  simp

private lemma circleKernelIntervalIntegrable (r β : ℝ) (hr : (1 : ℝ) / 2 ≤ r)
    (h1r : 0 < 1 - r) :
    IntervalIntegrable
      (fun θ : ℝ => ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β))
      volume (-Real.pi) Real.pi := by
  refine ((by fun_prop :
      Continuous fun θ : ℝ => ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖)
    |>.continuousOn.rpow_const ?_).intervalIntegrable
  intro θ hθ
  left
  have hθIcc : θ ∈ Set.Icc (-Real.pi) Real.pi := by
    have hneg_le : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
    rw [Set.uIcc_of_le hneg_le] at hθ
    exact hθ
  have hθabs : |θ| ≤ Real.pi := by
    rw [abs_le]
    exact ⟨hθIcc.1, hθIcc.2⟩
  let z : ℂ := (1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)
  have hcpos : 0 < (2 : ℝ) / Real.pi ^ 2 := by positivity
  have hApos : 0 < (1 - r) ^ 2 + θ ^ 2 := by
    nlinarith [sq_pos_of_pos h1r, sq_nonneg θ]
  have hlow : ((2 : ℝ) / Real.pi ^ 2) * ((1 - r) ^ 2 + θ ^ 2) ≤ ‖z‖ ^ 2 := by
    dsimp [z]
    exact circleKernel_norm_sq_lower r θ hθabs hr
  have hnormsq_pos : 0 < ‖z‖ ^ 2 := lt_of_lt_of_le (mul_pos hcpos hApos) hlow
  have hnorm_pos : 0 < ‖z‖ := by nlinarith [norm_nonneg z]
  exact hnorm_pos.ne'

private lemma circleKernel_integral_bound_nat_ge_two {β : ℝ} (hβ : 1 < β) :
    ∀ n : ℕ, 2 ≤ n →
      ∫ θ in (-Real.pi)..Real.pi,
          ‖(1 : ℂ) - ((1 : ℝ) - (1 : ℝ) / n : ℂ) *
              Complex.exp (θ * Complex.I)‖ ^ (-β) ≤
        (((2 : ℝ) / Real.pi ^ 2) ^ (-β / 2) *
          (2 + 2 * (β - 1)⁻¹)) * (n : ℝ) ^ (β - 1) := by
  intro n hn2
  have hβ0 : 0 ≤ β := by linarith
  have hnpos_nat : 0 < n := Nat.lt_of_lt_of_le (by norm_num) hn2
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hρpos : 0 < (1 : ℝ) / n := div_pos zero_lt_one hnpos
  have hρle : (1 : ℝ) / n ≤ 1 := by
    rw [div_le_one hnpos]
    exact_mod_cast (le_trans (by norm_num : (1 : ℕ) ≤ 2) hn2)
  let ρ : ℝ := (1 : ℝ) / n
  let r : ℝ := 1 - ρ
  have hr : (1 : ℝ) / 2 ≤ r := by
    dsimp [r, ρ]
    have htwo_le_n : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hdiv_le : (1 : ℝ) / n ≤ 1 / 2 := by
      rw [one_div_le_one_div hnpos (by norm_num : (0 : ℝ) < 2)]
      exact htwo_le_n
    linarith
  have h1r : 0 < 1 - r := by
    dsimp [r, ρ]
    simpa using hρpos
  have hconst_nonneg : 0 ≤ ((2 : ℝ) / Real.pi ^ 2) ^ (-β / 2) := by positivity
  have hmono := intervalIntegral.integral_mono_on (a := -Real.pi) (b := Real.pi)
    (by linarith [Real.pi_pos])
    (circleKernelIntervalIntegrable r β hr h1r)
    ((modelIntervalIntegrable ρ β (-Real.pi) Real.pi hρpos).const_mul
      (((2 : ℝ) / Real.pi ^ 2) ^ (-β / 2)))
    (fun θ hθ => by
      have hθabs : |θ| ≤ Real.pi := by
        rw [abs_le]
        exact ⟨hθ.1, hθ.2⟩
      have hle := circleKernel_rpow_le_model r θ β hθabs hr h1r hβ0
      simpa [r, ρ, Complex.real_smul] using hle)
  calc
    ∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - ((1 : ℝ) - (1 : ℝ) / n : ℂ) *
            Complex.exp (θ * Complex.I)‖ ^ (-β)
        = ∫ θ in (-Real.pi)..Real.pi,
            ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) := by
          simp [r, ρ]
    _ ≤ ∫ θ in (-Real.pi)..Real.pi,
        ((2 : ℝ) / Real.pi ^ 2) ^ (-β / 2) *
          ((ρ ^ 2 + θ ^ 2) ^ (-β / 2)) := hmono
    _ = ((2 : ℝ) / Real.pi ^ 2) ^ (-β / 2) *
        (∫ θ in (-Real.pi)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2)) := by
          rw [intervalIntegral.integral_const_mul]
    _ ≤ ((2 : ℝ) / Real.pi ^ 2) ^ (-β / 2) *
        ((2 + 2 * (β - 1)⁻¹) * ρ ^ (1 - β)) := by
          exact mul_le_mul_of_nonneg_left (modelKernel_integral_bound hρpos hρle hβ)
            hconst_nonneg
    _ = (((2 : ℝ) / Real.pi ^ 2) ^ (-β / 2) *
          (2 + 2 * (β - 1)⁻¹)) * (n : ℝ) ^ (β - 1) := by
          rw [one_div_nat_rpow β hnpos_nat]
          ring

lemma circleKernel_integral_bound_nat {β : ℝ} (hβ : 1 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      ∫ θ in (-Real.pi)..Real.pi,
          ‖(1 : ℂ) - ((1 : ℝ) - (1 : ℝ) / n) •
              Complex.exp (θ * Complex.I)‖ ^ (-β) ≤
        C * (n : ℝ) ^ (β - 1) := by
  let C0 : ℝ :=
    ((2 : ℝ) / Real.pi ^ 2) ^ (-β / 2) * (2 + 2 * (β - 1)⁻¹)
  let C : ℝ := C0 + 2 * Real.pi
  have hden_pos : 0 < β - 1 := by linarith
  have hC0_nonneg : 0 ≤ C0 := by
    dsimp [C0]
    positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_nonneg, ?_⟩
  intro n hn
  by_cases hn2 : 2 ≤ n
  · have hbase := circleKernel_integral_bound_nat_ge_two hβ n hn2
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    calc
      ∫ θ in (-Real.pi)..Real.pi,
          ‖(1 : ℂ) - ((1 : ℝ) - (1 : ℝ) / n) •
              Complex.exp (θ * Complex.I)‖ ^ (-β)
          = ∫ θ in (-Real.pi)..Real.pi,
              ‖(1 : ℂ) - ((1 : ℝ) - (1 : ℝ) / n : ℂ) *
                  Complex.exp (θ * Complex.I)‖ ^ (-β) := by
            apply intervalIntegral.integral_congr
            intro θ _
            simp [Complex.real_smul]
      _ ≤ C0 * (n : ℝ) ^ (β - 1) := by
        simpa [C0] using hbase
      _ ≤ C * (n : ℝ) ^ (β - 1) := by
        exact mul_le_mul_of_nonneg_right (by dsimp [C]; nlinarith [Real.pi_pos])
          (Real.rpow_nonneg hn_nonneg (β - 1))
  · have hn_eq : n = 1 := by omega
    subst n
    calc
      ∫ θ in (-Real.pi)..Real.pi,
          ‖(1 : ℂ) - ((1 : ℝ) - (1 : ℝ) / (1 : ℕ)) •
              Complex.exp (θ * Complex.I)‖ ^ (-β)
          = ∫ _θ in (-Real.pi)..Real.pi, (1 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro θ _
            set_option backward.isDefEq.respectTransparency false in
              norm_num [Complex.real_smul]
      _ = 2 * Real.pi := by
        rw [intervalIntegral.integral_const]
        simp
        ring
      _ ≤ C * ((1 : ℕ) : ℝ) ^ (β - 1) := by
        simp
        dsimp [C]
        nlinarith [hC0_nonneg, Real.pi_pos]

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
# Coefficient descent and general O-transfer

This file bootstraps the already-proved `β > 1` O-transfer theorem to all real
`β`.  The key bookkeeping device is the scalar one-variable derivative series:
take Mathlib's Frechet derivative series and apply it to `1`.
-/

open Complex Filter Asymptotics
open scoped Topology Real ENNReal BigOperators

noncomputable section

lemma scalarDerivSeries_coeff_smul (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    (scalarDerivSeries p).coeff n = (n + 1) • p.coeff (n + 1) := by
  rw [scalarDerivSeries, FormalMultilinearSeries.coeff,
    ContinuousLinearMap.compFormalMultilinearSeries_apply']
  exact FormalMultilinearSeries.derivSeries_coeff_one p n

lemma scalarDerivSeries_coeff (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    (scalarDerivSeries p).coeff n = (n + 1 : ℂ) * p.coeff (n + 1) := by
  rw [scalarDerivSeries_coeff_smul]
  simp [nsmul_eq_mul]

lemma HasFPowerSeriesOnBall.scalar_deriv
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {x : ℂ} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesOnBall (deriv f) (scalarDerivSeries p) x r := by
  convert (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).comp_hasFPowerSeriesOnBall h.fderiv using 1

lemma HasFPowerSeriesOnBall.scalar_iterated_deriv
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {x : ℂ} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f p x r) (k : ℕ) :
    HasFPowerSeriesOnBall ((deriv^[k]) f) (scalarIteratedDerivSeries k p) x r := by
  induction k with
  | zero => simpa [scalarIteratedDerivSeries] using h
  | succ k ih =>
      simpa [scalarIteratedDerivSeries, Function.iterate_succ_apply'] using ih.scalar_deriv

lemma HasFPowerSeriesAt.scalar_iteratedDeriv
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (h : HasFPowerSeriesAt f p (0 : ℂ)) (k : ℕ) :
    HasFPowerSeriesAt (iteratedDeriv k f) (scalarIteratedDerivSeries k p) (0 : ℂ) := by
  rcases h with ⟨r, hr⟩
  rw [iteratedDeriv_eq_iterate]
  exact (hr.scalar_iterated_deriv k).hasFPowerSeriesAt

lemma scalarIteratedDerivSeries_coeff (p : FormalMultilinearSeries ℂ ℂ ℂ) (k m : ℕ) :
    (scalarIteratedDerivSeries k p).coeff m =
      (∏ j ∈ Finset.range k, (m + 1 + j : ℂ)) * p.coeff (m + k) := by
  induction k generalizing m with
  | zero => simp [scalarIteratedDerivSeries]
  | succ k ih =>
      simp only [scalarIteratedDerivSeries]
      rw [scalarDerivSeries_coeff, ih]
      rw [Finset.prod_range_succ']
      simp_rw [Nat.cast_add, Nat.cast_one]
      ring_nf

lemma complex_nat_prod_norm (k m : ℕ) :
    ‖(∏ j ∈ Finset.range k, (m + 1 + j : ℂ))‖ =
      (∏ j ∈ Finset.range k, (m + 1 + j : ℝ)) := by
  rw [norm_prod]
  refine Finset.prod_congr rfl ?_
  intro j _hj
  have hc : ((m : ℂ) + 1 + (j : ℂ)) = ((m + 1 + j : ℕ) : ℂ) := by
    norm_num [Nat.cast_add]
  have hr : ((m : ℝ) + 1 + (j : ℝ)) = ((m + 1 + j : ℕ) : ℝ) := by
    norm_num [Nat.cast_add]
  rw [hc, hr, Complex.norm_natCast]

lemma scalarIteratedDerivSeries_coeff_norm (p : FormalMultilinearSeries ℂ ℂ ℂ) (k m : ℕ) :
    ‖(scalarIteratedDerivSeries k p).coeff m‖ =
      (∏ j ∈ Finset.range k, (m + 1 + j : ℝ)) * ‖p.coeff (m + k)‖ := by
  rw [scalarIteratedDerivSeries_coeff]
  rw [norm_mul, complex_nat_prod_norm]

lemma desc_prod_ge_pow (k m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) ^ k ≤ ∏ j ∈ Finset.range k, (m + 1 + j : ℝ) := by
  calc
    (m : ℝ) ^ k = ∏ j ∈ Finset.range k, (m : ℝ) := by simp
    _ ≤ ∏ j ∈ Finset.range k, (m + 1 + j : ℝ) := by
      refine Finset.prod_le_prod (fun j hj => by positivity) ?_
      intro j hj
      exact_mod_cast (by omega : m ≤ m + 1 + j)

lemma desc_prod_pos (k m : ℕ) :
    0 < ∏ j ∈ Finset.range k, (m + 1 + j : ℝ) := by
  refine Finset.prod_pos ?_
  intro j hj
  positivity

lemma inv_desc_prod_isBigO (k : ℕ) :
    (fun m : ℕ => (∏ j ∈ Finset.range k, (m + 1 + j : ℝ))⁻¹) =O[atTop]
      (fun m : ℕ => (m : ℝ) ^ (-(k : ℝ))) := by
  refine IsBigO.of_bound 1 ?_
  refine eventually_atTop.mpr ⟨1, fun m hm => ?_⟩
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hpowpos : 0 < (m : ℝ) ^ k := pow_pos hmpos k
  have hle := desc_prod_ge_pow k m hm
  have hinv : (∏ j ∈ Finset.range k, (m + 1 + j : ℝ))⁻¹ ≤ ((m : ℝ) ^ k)⁻¹ := by
    exact inv_anti₀ hpowpos hle
  have htarget : (m : ℝ) ^ (-(k : ℝ)) = ((m : ℝ) ^ k)⁻¹ := by
    rw [Real.rpow_neg hmpos.le (k : ℝ), Real.rpow_natCast]
  have hnonneg : 0 ≤ (∏ j ∈ Finset.range k, (m + 1 + j : ℝ))⁻¹ := by positivity
  rw [Real.norm_of_nonneg hnonneg, htarget]
  simpa using hinv

lemma nat_sub_const_isTheta (k : ℕ) :
    (fun n : ℕ => ((n - k : ℕ) : ℝ)) =Θ[atTop] (fun n : ℕ => (n : ℝ)) := by
  constructor
  · refine IsBigO.of_bound 1 ?_
    refine eventually_atTop.mpr ⟨0, fun n _hn => ?_⟩
    have hle : ((n - k : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.sub_le n k
    simp [hle]
  · refine IsBigO.of_bound 2 ?_
    refine eventually_atTop.mpr ⟨2 * k, fun n hn => ?_⟩
    have hnat : n ≤ 2 * (n - k) := by omega
    have hle : (n : ℝ) ≤ 2 * ((n - k : ℕ) : ℝ) := by
      exact_mod_cast hnat
    simpa [Real.norm_of_nonneg (Nat.cast_nonneg _), mul_comm, mul_assoc] using hle

lemma nat_sub_const_rpow_isBigO (k : ℕ) (e : ℝ) :
    (fun n : ℕ => ((n - k : ℕ) : ℝ) ^ e) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ e) := by
  have hf : ∀ᶠ n : ℕ in atTop, 0 ≤ ((n - k : ℕ) : ℝ) :=
    Eventually.of_forall fun n => Nat.cast_nonneg (n - k)
  have hg : ∀ᶠ n : ℕ in atTop, 0 ≤ (n : ℝ) :=
    Eventually.of_forall fun n => Nat.cast_nonneg n
  by_cases he : 0 ≤ e
  · exact (IsTheta.rpow he hf hg (nat_sub_const_isTheta k)).1
  · have hneg : 0 ≤ -e := by linarith
    have htheta := IsTheta.rpow hneg hf hg (nat_sub_const_isTheta k)
    have hinv := htheta.inv
    have hpow : ∀ n : ℕ, ((n : ℝ) ^ (-e))⁻¹ = (n : ℝ) ^ e := by
      intro n
      rw [← Real.rpow_neg (Nat.cast_nonneg n) (-e), neg_neg]
    simpa only [hpow] using hinv.1

end

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

private lemma circleKernel_intervalIntegrable {β r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    IntervalIntegrable
      (fun θ : ℝ => ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β))
      volume (-Real.pi) Real.pi := by
  refine ((by fun_prop :
      Continuous fun θ : ℝ => ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖)
    |>.continuousOn.rpow_const ?_).intervalIntegrable
  intro θ _hθ
  left
  have hnorm_exp : ‖Complex.exp (θ * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I θ
  have hne : (1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I) ≠ 0 := by
    intro hzero
    have hmul_eq : (r : ℂ) * Complex.exp (θ * Complex.I) = 1 :=
      (sub_eq_zero.mp hzero).symm
    have hnorm : ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ = 1 := by
      rw [hmul_eq, norm_one]
    have habs : |r| = 1 := by
      simpa [norm_mul, hnorm_exp] using hnorm
    have hr_eq_one : r = 1 := by
      simpa [abs_of_nonneg hr0] using habs
    linarith
  exact (norm_pos_iff.mpr hne).ne'

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

private lemma exists_delta_littleO_kernel_bound
    {R φ β ε : ℝ} {f : ℂ → ℂ}
    (hf_o : Tendsto (fun z : ℂ => ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0))
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ DeltaDomainArg R φ, ‖(1 : ℂ) - z‖ < δ →
      ‖f z‖ ≤ ε * ‖(1 : ℂ) - z‖ ^ (-β) := by
  rw [Metric.tendsto_nhdsWithin_nhds] at hf_o
  obtain ⟨δ, hδpos, hδ⟩ := hf_o ε hε
  refine ⟨δ, hδpos, fun z hz hnear => ?_⟩
  have hdist_z : dist z (1 : ℂ) < δ := by
    simpa [dist_eq_norm, norm_sub_rev] using hnear
  have hgdist := hδ hz hdist_z
  have hg_nonneg : 0 ≤ ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β := by positivity
  have hg_lt : ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β < ε := by
    simpa [dist_eq_norm, Real.norm_of_nonneg hg_nonneg] using hgdist
  have hz_ne : z ≠ 1 := hz.2.1
  have hnorm_pos : 0 < ‖(1 : ℂ) - z‖ := by
    rw [norm_pos_iff]
    simpa [sub_eq_zero] using (Ne.symm hz_ne)
  have hpow_mul :
      ‖(1 : ℂ) - z‖ ^ β * ‖(1 : ℂ) - z‖ ^ (-β) = 1 := by
    rw [← Real.rpow_add hnorm_pos β (-β)]
    simp
  calc
    ‖f z‖ = (‖f z‖ * ‖(1 : ℂ) - z‖ ^ β) *
        ‖(1 : ℂ) - z‖ ^ (-β) := by
      rw [mul_assoc, hpow_mul, mul_one]
    _ ≤ ε * ‖(1 : ℂ) - z‖ ^ (-β) :=
      mul_le_mul_of_nonneg_right (le_of_lt hg_lt) (by positivity)

/--
The hard analytic estimate behind the little-o transfer.

It is the Cauchy-circle integral split at radius `1 - 1/n`: the part with
`‖1 - z‖` small uses the little-o hypothesis, the complementary moving arc is
uniformly bounded on a compact subset of the Δ-domain and is `O(1)`, hence
negligible against `n^(β-1)` because `β > 1`.
-/
private lemma transferCircleBound_isLittleO_atTop_of_delta_littleO_beta_gt_one
    {R φ β : ℝ} {f : ℂ → ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hf_o : Tendsto (fun z : ℂ => ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0))
    (hβ : 1 < β) :
    transferCircleBound f =o[atTop] fun n : ℕ => (n : ℝ) ^ (β - 1) := by
  obtain ⟨C, hC0, hC⟩ := circleKernel_integral_bound_nat hβ
  let A : ℝ := (2 * Real.pi)⁻¹ * 4 * C
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  refine IsLittleO.of_bound ?_
  intro η hη
  let ε : ℝ := η / (2 * (A + 1))
  have hA1pos : 0 < A + 1 := by linarith
  have hdenpos : 0 < 2 * (A + 1) := by positivity
  have hεpos : 0 < ε := by
    dsimp [ε]
    positivity
  have hhalfpos : 0 < η / 2 := by positivity
  have hnear_coeff : A * ε ≤ η / 2 := by
    dsimp [ε]
    field_simp [hdenpos.ne']
    nlinarith [hA0, hη]
  obtain ⟨δ, hδpos, hnear⟩ :=
    exists_delta_littleO_kernel_bound (R := R) (φ := φ) (β := β) (f := f)
      hf_o hεpos
  obtain ⟨M, hM0, hM⟩ :=
    exists_bound_on_closedUnitAway (R := R) (φ := φ) (δ := δ) (f := f)
      hR hφ0 hφ2 hδpos han
  let B : ℝ := (2 * Real.pi)⁻¹ * 4 * (M * (2 * Real.pi))
  have hscale_atTop :
      Tendsto (fun n : ℕ => (n : ℝ) ^ (β - 1)) atTop atTop := by
    have hβ1 : 0 < β - 1 := by linarith
    exact (tendsto_rpow_atTop hβ1).comp tendsto_natCast_atTop_atTop
  have hscale_eventually :
      ∀ᶠ n : ℕ in atTop, B / (η / 2) ≤ (n : ℝ) ^ (β - 1) :=
    hscale_atTop.eventually (eventually_ge_atTop (B / (η / 2)))
  have haway_eventually :
      ∀ᶠ n : ℕ in atTop, B ≤ (η / 2) * (n : ℝ) ^ (β - 1) := by
    filter_upwards [hscale_eventually] with n hn
    calc
      B = (η / 2) * (B / (η / 2)) := by
        field_simp [hhalfpos.ne']
      _ ≤ (η / 2) * (n : ℝ) ^ (β - 1) :=
        mul_le_mul_of_nonneg_left hn hhalfpos.le
  filter_upwards [eventually_atTop.mpr ⟨2, fun n hn => hn⟩, haway_eventually]
    with n hn haway_n
  have hn1 : 1 ≤ n := le_trans (by norm_num : (1 : ℕ) ≤ 2) hn
  have hnpos_nat : 0 < n := Nat.lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  let r : ℝ := 1 - (1 : ℝ) / n
  have hr0 : 0 ≤ r := by
    dsimp [r]
    have hdiv : (1 : ℝ) / n ≤ 1 := by
      rw [div_le_one hnpos]
      exact_mod_cast hn1
    linarith
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
  have hleft_int := circleFunction_intervalIntegrable (f := f) hr0 hr1 hrR hφ0 hφ2 han
  have hkernel_int := circleKernel_intervalIntegrable (β := β) hr0 hr1
  have hright_int :
      IntervalIntegrable
        (fun θ : ℝ =>
          ε * ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) + M)
        volume (-Real.pi) Real.pi :=
    (hkernel_int.const_mul ε).add intervalIntegrable_const
  have hInt_le :
      (∫ θ in (-Real.pi)..Real.pi, ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖) ≤
        ∫ θ in (-Real.pi)..Real.pi,
          ε * ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) + M := by
    refine intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
      hleft_int hright_int ?_
    intro θ _hθ
    let z : ℂ := (r : ℂ) * Complex.exp (θ * Complex.I)
    have hz_delta : z ∈ DeltaDomainArg R φ :=
      circlePoint_mem_delta hr0 hr1 hrR hφ0 hφ2 θ
    by_cases hz_near : ‖(1 : ℂ) - z‖ < δ
    · have hlocal : ‖f z‖ ≤ ε * ‖(1 : ℂ) - z‖ ^ (-β) :=
        hnear z hz_delta hz_near
      have hMadd :
          ε * ‖(1 : ℂ) - z‖ ^ (-β) ≤
            ε * ‖(1 : ℂ) - z‖ ^ (-β) + M := by
        linarith
      exact hlocal.trans hMadd
    · have hz_away : δ ≤ ‖(1 : ℂ) - z‖ := le_of_not_gt hz_near
      have hz_norm_le : ‖z‖ ≤ 1 := by
        calc
          ‖z‖ = r := by
            simp [z, Complex.norm_exp_ofReal_mul_I, abs_of_nonneg hr0]
          _ ≤ 1 := hr1.le
      have hbound : ‖f z‖ ≤ M := hM z hz_norm_le hz_away
      have hkernel_nonneg :
          0 ≤ ε * ‖(1 : ℂ) - z‖ ^ (-β) := by positivity
      calc
        ‖f z‖ ≤ M := hbound
        _ ≤ ε * ‖(1 : ℂ) - z‖ ^ (-β) + M := by linarith
  have hInt_bound :
      (∫ θ in (-Real.pi)..Real.pi, ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖) ≤
        ε * (∫ θ in (-Real.pi)..Real.pi,
          ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)) +
          M * (2 * Real.pi) := by
    calc
      (∫ θ in (-Real.pi)..Real.pi, ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖)
          ≤ ∫ θ in (-Real.pi)..Real.pi,
              ε * ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) + M :=
            hInt_le
      _ = ε * (∫ θ in (-Real.pi)..Real.pi,
              ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)) +
            M * (2 * Real.pi) := by
          rw [intervalIntegral.integral_add (hkernel_int.const_mul ε) intervalIntegrable_const]
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
          simp [mul_comm]
          left
          ring
  have hkernel_nonneg_int :
      0 ≤ ∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) := by
    refine intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) ?_
    intro θ _hθ
    positivity
  have hbracket_nonneg :
      0 ≤ ε * (∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)) +
        M * (2 * Real.pi) := by positivity
  have hpow4 : r⁻¹ ^ n ≤ 4 := by
    dsimp [r]
    exact one_sub_inv_pow_nat_le_four hn
  have hkernel_bound :
      (∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)) ≤
        C * (n : ℝ) ^ (β - 1) := by
    dsimp [r]
    have h := hC n hn1
    simpa [Complex.real_smul] using h
  have hscale_nonneg : 0 ≤ (n : ℝ) ^ (β - 1) := by positivity
  have htransfer_le :
      transferCircleBound f n ≤ A * ε * (n : ℝ) ^ (β - 1) + B := by
    calc
      transferCircleBound f n =
          (2 * Real.pi)⁻¹ * r⁻¹ ^ n *
            ∫ θ in (-Real.pi)..Real.pi,
              ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖ := by
            simp [transferCircleBound, r]
      _ ≤ (2 * Real.pi)⁻¹ * r⁻¹ ^ n *
            (ε * (∫ θ in (-Real.pi)..Real.pi,
              ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)) +
              M * (2 * Real.pi)) := by
            exact mul_le_mul_of_nonneg_left hInt_bound
              (mul_nonneg (by positivity) (pow_nonneg (inv_nonneg.mpr hr0) n))
      _ ≤ (2 * Real.pi)⁻¹ * 4 *
            (ε * (∫ θ in (-Real.pi)..Real.pi,
              ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)) +
              M * (2 * Real.pi)) := by
            calc
              (2 * Real.pi)⁻¹ * r⁻¹ ^ n *
                    (ε * (∫ θ in (-Real.pi)..Real.pi,
                      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)) +
                      M * (2 * Real.pi))
                  = (2 * Real.pi)⁻¹ *
                    (r⁻¹ ^ n * (ε * (∫ θ in (-Real.pi)..Real.pi,
                      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)) +
                      M * (2 * Real.pi))) := by
                    ring
              _ ≤ (2 * Real.pi)⁻¹ *
                    (4 * (ε * (∫ θ in (-Real.pi)..Real.pi,
                      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)) +
                      M * (2 * Real.pi))) := by
                    exact mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_right hpow4 hbracket_nonneg)
                      (by positivity)
              _ = (2 * Real.pi)⁻¹ * 4 *
                    (ε * (∫ θ in (-Real.pi)..Real.pi,
                      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)) +
                      M * (2 * Real.pi)) := by
                    ring
      _ ≤ (2 * Real.pi)⁻¹ * 4 *
            (ε * (C * (n : ℝ) ^ (β - 1)) + M * (2 * Real.pi)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact add_le_add
              (mul_le_mul_of_nonneg_left hkernel_bound hεpos.le) le_rfl
      _ = A * ε * (n : ℝ) ^ (β - 1) + B := by
            dsimp [A, B]
            ring
  have hnear_n :
      A * ε * (n : ℝ) ^ (β - 1) ≤ (η / 2) * (n : ℝ) ^ (β - 1) :=
    mul_le_mul_of_nonneg_right hnear_coeff hscale_nonneg
  have htransfer_nonneg : 0 ≤ transferCircleBound f n := by
    have hI_nonneg :
        0 ≤ ∫ θ in (-Real.pi)..Real.pi,
          ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖ := by
      refine intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) ?_
      intro θ _hθ
      positivity
    rw [transferCircleBound]
    exact mul_nonneg
      (mul_nonneg (by positivity) (pow_nonneg (inv_nonneg.mpr hr0) n)) hI_nonneg
  calc
    ‖transferCircleBound f n‖ = transferCircleBound f n :=
      Real.norm_of_nonneg htransfer_nonneg
    _ ≤ A * ε * (n : ℝ) ^ (β - 1) + B := htransfer_le
    _ ≤ (η / 2) * (n : ℝ) ^ (β - 1) +
        (η / 2) * (n : ℝ) ^ (β - 1) :=
      add_le_add hnear_n haway_n
    _ = η * (n : ℝ) ^ (β - 1) := by ring
    _ = η * ‖(n : ℝ) ^ (β - 1)‖ := by
      rw [Real.norm_of_nonneg hscale_nonneg]

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

theorem coeff_norm_isLittleO_atTop_of_delta_littleO_beta_gt_one
    {R φ β : ℝ} {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p (0 : ℂ))
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hf_o : Tendsto (fun z : ℂ => ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0))
    (hβ : 1 < β) :
    (fun n : ℕ => ‖p.coeff n‖) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ (β - 1)) := by
  have hcircle :=
    transferCircleBound_isLittleO_atTop_of_delta_littleO_beta_gt_one
      (R := R) (φ := φ) (β := β) (f := f) hR hφ0 hφ2 han hf_o hβ
  have hcoeff :=
    coeff_norm_le_transferCircleBound (R := R) (φ := φ) (f := f) (p := p)
      hR hφ0 hφ2 hp han
  refine IsLittleO.of_bound ?_
  intro c hc
  filter_upwards [hcoeff, hcircle.bound hc] with n hncoeff hnbound
  have hcircle_nonneg : 0 ≤ transferCircleBound f n :=
    (norm_nonneg (p.coeff n)).trans hncoeff
  calc
    ‖(‖p.coeff n‖ : ℝ)‖ = ‖p.coeff n‖ := norm_norm _
    _ ≤ transferCircleBound f n := hncoeff
    _ = ‖transferCircleBound f n‖ := (Real.norm_of_nonneg hcircle_nonneg).symm
    _ ≤ c * ‖(n : ℝ) ^ (β - 1)‖ := hnbound

end

/-!
# Coefficient descent for little-o transfer

This file bootstraps the `β > 1` little-o transfer theorem to all real `β`.
-/

open Complex Filter Asymptotics
open scoped Topology Real BigOperators

noncomputable section

private lemma deltaLocalKappa_pos' {R R' φ φ' : ℝ} (hR'0 : 0 < R')
    (hRR : R' < R) (hφ : 0 < φ) (hφlt : φ < φ')
    (hφ'2 : φ' < Real.pi / 2) :
    0 < deltaLocalKappa R R' φ φ' := by
  have hφ' : 0 < φ' := lt_trans hφ hφlt
  have hφπ : φ < Real.pi := by linarith [hφlt, hφ'2, Real.pi_pos]
  have hφ'π : φ' < Real.pi := by linarith [hφ'2, Real.pi_pos]
  have hcos_lt : Real.cos φ' < Real.cos φ := by
    exact (Real.strictAntiOn_cos.lt_iff_gt
      (Set.mem_Icc.mpr ⟨hφ'.le, hφ'π.le⟩)
      (Set.mem_Icc.mpr ⟨hφ.le, hφπ.le⟩)).2 hφlt
  have hRdiff_pos : 0 < R - R' := by linarith
  have hdenR_pos : 0 < 2 * (1 + R') := by nlinarith
  have hdenA_pos : 0 < 2 * (1 + Real.cos φ) := by
    have hcos_pos : 0 < Real.cos φ := by
      exact Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hφ, Real.pi_pos], by linarith [hφlt, hφ'2]⟩
    nlinarith
  unfold deltaLocalKappa
  exact lt_min (by norm_num) (lt_min (div_pos hRdiff_pos hdenR_pos)
    (div_pos (by linarith) hdenA_pos))

private lemma deltaLocalKappa_le_half' {R R' φ φ' : ℝ} :
    deltaLocalKappa R R' φ φ' ≤ 1 / 2 := by
  unfold deltaLocalKappa
  exact min_le_left _ _

private lemma rpow_scale_nat_eq' {a x β M B : ℝ} {k : ℕ}
    (ha : 0 < a) (hx : 0 < x) :
    ((k.factorial : ℝ) * (M * B * x ^ (-β)) / ((a * x) ^ k)) =
      ((k.factorial : ℝ) * M * B * a ^ (-(k : ℝ))) * x ^ (-β - k) := by
  have hasplit : a ^ (-(k : ℝ)) = (a ^ k)⁻¹ := by
    rw [Real.rpow_neg ha.le (k : ℝ), Real.rpow_natCast]
  have hxsplit : x ^ (-β - (k : ℝ)) = x ^ (-β) * (x ^ k)⁻¹ := by
    rw [show -β - (k : ℝ) = -β + -(k : ℝ) by ring]
    rw [Real.rpow_add hx]
    rw [Real.rpow_neg hx.le (k : ℝ), Real.rpow_natCast]
  rw [hasplit, hxsplit, div_eq_mul_inv, mul_pow]
  field_simp [ha.ne', hx.ne']

private lemma rpow_neg_le_two_abs_mul' {β x y : ℝ} (hx : 0 < x)
    (hhalf : (1 / 2) * x ≤ y) (hupper : y ≤ 2 * x) :
    y ^ (-β) ≤ 2 ^ |β| * x ^ (-β) := by
  by_cases hβ : 0 ≤ β
  · have hlower_pos : 0 < (1 / 2 : ℝ) * x := by positivity
    have hmono : y ^ (-β) ≤ ((1 / 2 : ℝ) * x) ^ (-β) := by
      exact Real.rpow_le_rpow_of_nonpos hlower_pos hhalf (by linarith)
    have hrewrite : ((1 / 2 : ℝ) * x) ^ (-β) = 2 ^ β * x ^ (-β) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) hx.le]
      rw [Real.rpow_neg_eq_inv_rpow]
      set_option backward.isDefEq.respectTransparency false in
        norm_num
    rw [abs_of_nonneg hβ]
    exact hmono.trans_eq hrewrite
  · have hβlt : β < 0 := lt_of_not_ge hβ
    have hlower_pos : 0 < (1 / 2 : ℝ) * x := by positivity
    have hy0 : 0 ≤ y := le_trans hlower_pos.le hhalf
    have hmono : y ^ (-β) ≤ (2 * x) ^ (-β) := by
      exact Real.rpow_le_rpow hy0 hupper (by linarith)
    have hrewrite : (2 * x) ^ (-β) = 2 ^ (-β) * x ^ (-β) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx.le]
    rw [abs_of_neg hβlt]
    exact hmono.trans_eq hrewrite

private lemma exists_delta_littleO_kernel_bound'
    {R φ β ε : ℝ} {f : ℂ → ℂ}
    (hf_o : Tendsto (fun z : ℂ => ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0))
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ DeltaDomainArg R φ, ‖(1 : ℂ) - z‖ < δ →
      ‖f z‖ ≤ ε * ‖(1 : ℂ) - z‖ ^ (-β) := by
  rw [Metric.tendsto_nhdsWithin_nhds] at hf_o
  obtain ⟨δ, hδpos, hδ⟩ := hf_o ε hε
  refine ⟨δ, hδpos, fun z hz hnear => ?_⟩
  have hdist_z : dist z (1 : ℂ) < δ := by
    simpa [dist_eq_norm, norm_sub_rev] using hnear
  have hgdist := hδ hz hdist_z
  have hg_nonneg : 0 ≤ ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β := by positivity
  have hg_lt : ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β < ε := by
    simpa [dist_eq_norm, Real.norm_of_nonneg hg_nonneg] using hgdist
  have hz_ne : z ≠ 1 := hz.2.1
  have hnorm_pos : 0 < ‖(1 : ℂ) - z‖ := by
    rw [norm_pos_iff]
    simpa [sub_eq_zero] using (Ne.symm hz_ne)
  have hpow_mul :
      ‖(1 : ℂ) - z‖ ^ β * ‖(1 : ℂ) - z‖ ^ (-β) = 1 := by
    rw [← Real.rpow_add hnorm_pos β (-β)]
    simp
  calc
    ‖f z‖ = (‖f z‖ * ‖(1 : ℂ) - z‖ ^ β) *
        ‖(1 : ℂ) - z‖ ^ (-β) := by
      rw [mul_assoc, hpow_mul, mul_one]
    _ ≤ ε * ‖(1 : ℂ) - z‖ ^ (-β) :=
      mul_le_mul_of_nonneg_right (le_of_lt hg_lt) (by positivity)

private theorem iteratedDeriv_norm_le_of_local_delta_littleO_bound
    {R φ β ε κ : ℝ} {f : ℂ → ℂ} {z : ℂ} {k : ℕ}
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hε0 : 0 ≤ ε) (hκpos : 0 < κ) (hκhalf : κ ≤ 1 / 2)
    (hz_ne : z ≠ 1)
    (hlocal : Metric.ball z (κ * ‖(1 : ℂ) - z‖) ⊆ DeltaDomainArg R φ)
    (hnear_bound : ∀ w ∈ Metric.ball z (κ * ‖(1 : ℂ) - z‖),
      ‖f w‖ ≤ ε * ‖(1 : ℂ) - w‖ ^ (-β)) :
    ‖iteratedDeriv k f z‖ ≤
      ((k.factorial : ℝ) * ε * 2 ^ |β| * (κ / 2) ^ (-(k : ℝ))) *
        ‖(1 : ℂ) - z‖ ^ (-β - k) := by
  let x : ℝ := ‖(1 : ℂ) - z‖
  let ρ : ℝ := (κ / 2) * x
  have hxpos : 0 < x := by
    dsimp [x]
    rw [norm_pos_iff]
    simpa [sub_eq_zero] using (Ne.symm hz_ne)
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρ_lt_big : ρ < κ * x := by
    dsimp [ρ]
    nlinarith [hκpos, hxpos]
  have hclosed_sub_big : Metric.closedBall z ρ ⊆ Metric.ball z (κ * x) := by
    intro w hw
    have hdist : dist w z ≤ ρ := by
      simpa [Metric.mem_closedBall] using hw
    have hlt : dist w z < κ * x := lt_of_le_of_lt hdist hρ_lt_big
    simpa [Metric.mem_ball] using hlt
  have hclosed_sub_delta : Metric.closedBall z ρ ⊆ DeltaDomainArg R φ :=
    hclosed_sub_big.trans (by simpa [x] using hlocal)
  have hdiff : DiffContOnCl ℂ f (Metric.ball z ρ) := by
    have hd_closed : DifferentiableOn ℂ f (Metric.closedBall z ρ) :=
      han.differentiableOn.mono hclosed_sub_delta
    exact (hd_closed.mono Metric.closure_ball_subset_closedBall).diffContOnCl
  have hsphere_bound : ∀ w ∈ Metric.sphere z ρ,
      ‖f w‖ ≤ ε * 2 ^ |β| * x ^ (-β) := by
    intro w hw
    have hw_big : w ∈ Metric.ball z (κ * x) := by
      have hdist : dist w z = ρ := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hw
      have hlt : dist w z < κ * x := by
        rw [hdist]
        exact hρ_lt_big
      simpa [Metric.mem_ball] using hlt
    have hfw := hnear_bound w (by simpa [x] using hw_big)
    have hcomp := local_disk_norm_comparable_half hκpos.le hκhalf (by simpa [x] using hw_big)
    have hpow : ‖(1 : ℂ) - w‖ ^ (-β) ≤ 2 ^ |β| * x ^ (-β) := by
      exact rpow_neg_le_two_abs_mul' (β := β) (x := x) (y := ‖(1 : ℂ) - w‖)
        hxpos (by simpa [x] using hcomp.1) (by simpa [x] using hcomp.2)
    calc
      ‖f w‖ ≤ ε * ‖(1 : ℂ) - w‖ ^ (-β) := hfw
      _ ≤ ε * (2 ^ |β| * x ^ (-β)) := mul_le_mul_of_nonneg_left hpow hε0
      _ = ε * 2 ^ |β| * x ^ (-β) := by ring
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (F := ℂ) (c := z) (R := ρ) (C := ε * 2 ^ |β| * x ^ (-β))
    k hρpos hdiff hsphere_bound
  have hscale := rpow_scale_nat_eq' (a := κ / 2) (x := x) (β := β)
    (M := ε) (B := 2 ^ |β|) (k := k) (by positivity) hxpos
  calc
    ‖iteratedDeriv k f z‖ ≤
        (k.factorial : ℝ) * (ε * 2 ^ |β| * x ^ (-β)) / ρ ^ k := hcauchy
    _ = ((k.factorial : ℝ) * ε * 2 ^ |β| * (κ / 2) ^ (-(k : ℝ))) *
        x ^ (-β - k) := by
          simpa [ρ] using hscale
    _ = ((k.factorial : ℝ) * ε * 2 ^ |β| * (κ / 2) ^ (-(k : ℝ))) *
        ‖(1 : ℂ) - z‖ ^ (-β - k) := by simp [x]

theorem iteratedDeriv_littleO_of_delta_littleO
    {R R' φ φ' β : ℝ} {f : ℂ → ℂ} (k : ℕ)
    (hR'1 : 1 < R') (hRR : R' < R) (hφ : 0 < φ) (hφlt : φ < φ')
    (hφ'2 : φ' < Real.pi / 2)
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hf_o : Tendsto (fun z : ℂ => ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    Tendsto (fun z : ℂ =>
      ‖iteratedDeriv k f z‖ * ‖(1 : ℂ) - z‖ ^ (β + k))
      (𝓝[DeltaDomainArg R' φ'] (1 : ℂ)) (𝓝 0) := by
  let κ : ℝ := deltaLocalKappa R R' φ φ'
  have hR'0 : 0 < R' := by linarith
  have hκpos : 0 < κ := by
    dsimp [κ]
    exact deltaLocalKappa_pos' hR'0 hRR hφ hφlt hφ'2
  have hκhalf : κ ≤ 1 / 2 := by
    dsimp [κ]
    exact deltaLocalKappa_le_half'
  let A : ℝ := (k.factorial : ℝ) * 2 ^ |β| * (κ / 2) ^ (-(k : ℝ))
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro η hη
  let ε : ℝ := η / (2 * (A + 1))
  have hA1pos : 0 < A + 1 := by linarith
  have hdenpos : 0 < 2 * (A + 1) := by positivity
  have hεpos : 0 < ε := by
    dsimp [ε]
    positivity
  have hAε_le : A * ε ≤ η / 2 := by
    dsimp [ε]
    field_simp [hdenpos.ne']
    nlinarith [hA0, hη]
  obtain ⟨δ, hδpos, hsmall⟩ :=
    exists_delta_littleO_kernel_bound' (R := R) (φ := φ) (β := β) (f := f)
      hf_o hεpos
  refine ⟨δ / 2, by positivity, fun z hz hdist_z => ?_⟩
  let x : ℝ := ‖(1 : ℂ) - z‖
  have hxpos : 0 < x := by
    dsimp [x]
    rw [norm_pos_iff]
    simpa [sub_eq_zero] using (Ne.symm hz.2.1)
  have hxnear : x < δ / 2 := by
    dsimp [x]
    simpa [dist_eq_norm, norm_sub_rev] using hdist_z
  have hlocal : Metric.ball z (κ * ‖(1 : ℂ) - z‖) ⊆ DeltaDomainArg R φ := by
    dsimp [κ]
    exact local_disk_subset_deltaDomain_deltaLocalKappa hR'0 hRR hφ hφlt hφ'2 hz
  have hnear_bound : ∀ w ∈ Metric.ball z (κ * ‖(1 : ℂ) - z‖),
      ‖f w‖ ≤ ε * ‖(1 : ℂ) - w‖ ^ (-β) := by
    intro w hw
    have hw_delta : w ∈ DeltaDomainArg R φ := hlocal hw
    have hcomp := local_disk_norm_comparable_half hκpos.le hκhalf hw
    have hw_near : ‖(1 : ℂ) - w‖ < δ := by
      have hupper : ‖(1 : ℂ) - w‖ ≤ 2 * x := by
        simpa [x] using hcomp.2
      have hxδ : 2 * x < δ := by linarith
      exact lt_of_le_of_lt hupper hxδ
    exact hsmall w hw_delta hw_near
  have hderiv := iteratedDeriv_norm_le_of_local_delta_littleO_bound
    (R := R) (φ := φ) (β := β) (ε := ε) (κ := κ) (f := f) (z := z) (k := k)
    han hεpos.le hκpos hκhalf hz.2.1 hlocal hnear_bound
  have hderivA :
      ‖iteratedDeriv k f z‖ ≤ A * ε * x ^ (-β - (k : ℝ)) := by
    simpa [A, x, mul_comm, mul_left_comm, mul_assoc] using hderiv
  have hpow_cancel : x ^ (-β - (k : ℝ)) * x ^ (β + (k : ℝ)) = 1 := by
    rw [← Real.rpow_add hxpos]
    ring_nf
    simp
  have htarget_nonneg :
      0 ≤ ‖(1 : ℂ) - z‖ ^ (β + (k : ℝ)) := by positivity
  have hmain :
      ‖iteratedDeriv k f z‖ * ‖(1 : ℂ) - z‖ ^ (β + (k : ℝ)) ≤ η / 2 := by
    calc
      ‖iteratedDeriv k f z‖ * ‖(1 : ℂ) - z‖ ^ (β + (k : ℝ))
          ≤ (A * ε * x ^ (-β - (k : ℝ))) *
              ‖(1 : ℂ) - z‖ ^ (β + (k : ℝ)) := by
            exact mul_le_mul_of_nonneg_right hderivA htarget_nonneg
      _ = A * ε := by
            dsimp [x]
            rw [mul_assoc, hpow_cancel, mul_one]
      _ ≤ η / 2 := hAε_le
  have hnonneg :
      0 ≤ ‖iteratedDeriv k f z‖ * ‖(1 : ℂ) - z‖ ^ (β + (k : ℝ)) := by
    positivity
  have hdist0 :
      dist (‖iteratedDeriv k f z‖ * ‖(1 : ℂ) - z‖ ^ (β + (k : ℝ))) 0 < η := by
    rw [dist_eq_norm, sub_zero, Real.norm_of_nonneg hnonneg]
    exact lt_of_le_of_lt hmain (by linarith)
  simpa using hdist0

private lemma rpow_mul_nat_add_eventually (k : ℕ) (β : ℝ) :
    (fun m : ℕ => (m : ℝ) ^ (-(k : ℝ)) * (m : ℝ) ^ (β + k - 1)) =ᶠ[atTop]
      (fun m : ℕ => (m : ℝ) ^ (β - 1)) := by
  refine eventually_atTop.mpr ⟨1, fun m hm => ?_⟩
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  change (m : ℝ) ^ (-(k : ℝ)) * (m : ℝ) ^ (β + (k : ℝ) - 1) =
    (m : ℝ) ^ (β - 1)
  rw [← Real.rpow_add hmpos]
  congr 1
  ring

lemma tail_isLittleO_of_iterated_coeff_isLittleO
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (k : ℕ) (β : ℝ)
    (hderiv : (fun m : ℕ => ‖(scalarIteratedDerivSeries k p).coeff m‖) =o[atTop]
      (fun m : ℕ => (m : ℝ) ^ (β + k - 1))) :
    (fun m : ℕ => ‖p.coeff (m + k)‖) =o[atTop]
      (fun m : ℕ => (m : ℝ) ^ (β - 1)) := by
  let P : ℕ → ℝ := fun m => ∏ j ∈ Finset.range k, (m + 1 + j : ℝ)
  have heq : (fun m : ℕ => ‖p.coeff (m + k)‖) =ᶠ[atTop]
      (fun m : ℕ => (P m)⁻¹ * ‖(scalarIteratedDerivSeries k p).coeff m‖) := by
    refine eventually_atTop.mpr ⟨0, fun m _hm => ?_⟩
    have hPpos : 0 < P m := by
      dsimp [P]
      exact desc_prod_pos k m
    have hdesc := scalarIteratedDerivSeries_coeff_norm p k m
    dsimp [P]
    calc
      ‖p.coeff (m + k)‖ = ((∏ j ∈ Finset.range k, (m + 1 + j : ℝ))⁻¹ *
          ((∏ j ∈ Finset.range k, (m + 1 + j : ℝ)) * ‖p.coeff (m + k)‖)) := by
            field_simp [hPpos.ne']
      _ = (∏ j ∈ Finset.range k, (m + 1 + j : ℝ))⁻¹ *
          ‖(scalarIteratedDerivSeries k p).coeff m‖ := by rw [hdesc]
  have hinvO : (fun m : ℕ => (P m)⁻¹) =O[atTop]
      (fun m : ℕ => (m : ℝ) ^ (-(k : ℝ))) := by
    simpa [P] using inv_desc_prod_isBigO k
  have hmul : (fun m : ℕ => (P m)⁻¹ * ‖(scalarIteratedDerivSeries k p).coeff m‖) =o[atTop]
      (fun m : ℕ => (m : ℝ) ^ (β - 1)) := by
    have hprod := hinvO.mul_isLittleO hderiv
    exact hprod.trans_eventuallyEq (rpow_mul_nat_add_eventually k β)
  exact heq.trans_isLittleO hmul

lemma isLittleO_of_shift {E : Type*} [Norm E] (a : ℕ → E) (k : ℕ) (e : ℝ)
    (h : (fun m : ℕ => a (m + k)) =o[atTop] (fun m : ℕ => (m : ℝ) ^ e)) :
    a =o[atTop] (fun n : ℕ => (n : ℝ) ^ e) := by
  have hcomp := h.comp_tendsto (Filter.tendsto_sub_atTop_nat k)
  have hcomp' : (fun n : ℕ => a ((n - k) + k)) =o[atTop]
      (fun n : ℕ => ((n - k : ℕ) : ℝ) ^ e) := by
    simpa [Function.comp_apply] using hcomp
  have heq : a =ᶠ[atTop] (fun n : ℕ => a ((n - k) + k)) := by
    refine eventually_atTop.mpr ⟨k, fun n hn => ?_⟩
    simp [Nat.sub_add_cancel hn]
  exact heq.trans_isLittleO (hcomp'.trans_isBigO (nat_sub_const_rpow_isBigO k e))

theorem coeff_norm_isLittleO_atTop_of_delta_littleO
    {R φ β : ℝ} {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p (0 : ℂ))
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hf_o : Tendsto (fun z : ℂ => ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ => ‖p.coeff n‖) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ (β - 1)) := by
  obtain ⟨k, hkraw⟩ := exists_nat_gt (1 - β)
  have hβk : 1 < β + (k : ℝ) := by linarith
  let R' : ℝ := (1 + R) / 2
  have hR'1 : 1 < R' := by dsimp [R']; linarith
  have hRR' : R' < R := by dsimp [R']; linarith
  let φ' : ℝ := (φ + Real.pi / 2) / 2
  have hφ'0 : 0 < φ' := by dsimp [φ']; linarith [hφ0, Real.pi_pos]
  have hφlt : φ < φ' := by dsimp [φ']; linarith [hφ2]
  have hφ'2 : φ' < Real.pi / 2 := by dsimp [φ']; linarith [hφ2]
  have hsubset : DeltaDomainArg R' φ' ⊆ DeltaDomainArg R φ := by
    intro z hz
    exact ⟨lt_trans hz.1 hRR', hz.2.1, lt_trans hφlt hz.2.2⟩
  have hΔ' : AnalyticOnNhd ℂ f (DeltaDomainArg R' φ') := fun z hz => hΔ z (hsubset hz)
  have hp_iter : HasFPowerSeriesAt (iteratedDeriv k f)
      (scalarIteratedDerivSeries k p) (0 : ℂ) := hp.scalar_iteratedDeriv k
  have hΔ_iter : AnalyticOnNhd ℂ (iteratedDeriv k f) (DeltaDomainArg R' φ') := by
    simpa [iteratedDeriv_eq_iterate] using hΔ'.iterated_deriv k
  have hderiv_o : Tendsto (fun z : ℂ =>
      ‖iteratedDeriv k f z‖ * ‖(1 : ℂ) - z‖ ^ (β + k))
      (𝓝[DeltaDomainArg R' φ'] (1 : ℂ)) (𝓝 0) := by
    exact iteratedDeriv_littleO_of_delta_littleO
      (R := R) (R' := R') (φ := φ) (φ' := φ') (β := β) (f := f) k
      hR'1 hRR' hφ0 hφlt hφ'2 hΔ hf_o
  have hderivLittleO :
      (fun m : ℕ => ‖(scalarIteratedDerivSeries k p).coeff m‖) =o[atTop]
        (fun m : ℕ => (m : ℝ) ^ (β + k - 1)) := by
    exact coeff_norm_isLittleO_atTop_of_delta_littleO_beta_gt_one
      (R := R') (φ := φ') (β := β + (k : ℝ))
      (f := iteratedDeriv k f) (p := scalarIteratedDerivSeries k p)
      hR'1 hφ'0 hφ'2 hp_iter hΔ_iter hderiv_o hβk
  have htail := tail_isLittleO_of_iterated_coeff_isLittleO p k β hderivLittleO
  exact isLittleO_of_shift (fun n : ℕ => ‖p.coeff n‖) k (β - 1) htail

end

/-!
# General singularity-analysis transfer theorem

This file assembles the general Darboux little-o transfer estimate with the
standard coefficient scale for `(1 - z)^{-α}`. Unlike the restricted theorem,
there is no lower bound on `α.re`; the only exclusion is that `α` is not a
nonpositive integer, exactly the hypothesis needed for the standard scale.
-/

open Complex Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

private lemma coeff_sub_const_smul (C : ℂ)
    (p q : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    (p - C • q).coeff n = p.coeff n - C * q.coeff n := by
  change (p n - (C • q) n) 1 = p n 1 - C * q.coeff n
  rw [FormalMultilinearSeries.smul_apply]
  rw [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.smul_apply]
  change p.coeff n - C • q.coeff n = p.coeff n - C * q.coeff n
  simp [smul_eq_mul]

private lemma main_term_norm_eventually {α C : ℂ} :
    ∀ᶠ n : ℕ in atTop,
      ‖C * (n : ℂ) ^ (α - 1) / Complex.Gamma α‖ =
        (‖C‖ / ‖Complex.Gamma α‖) * (n : ℝ) ^ (α.re - 1) := by
  refine (eventually_ne_atTop 0).mono ?_
  intro n hn
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hpow : ‖(n : ℂ) ^ (α - 1)‖ = (n : ℝ) ^ ((α - 1).re) := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (x := (n : ℝ)) hnpos (α - 1)
  have hre : (α - 1).re = α.re - 1 := by simp
  calc
    ‖C * (n : ℂ) ^ (α - 1) / Complex.Gamma α‖
        = ‖C‖ * ‖(n : ℂ) ^ (α - 1)‖ / ‖Complex.Gamma α‖ := by
          rw [norm_div, norm_mul]
    _ = ‖C‖ * ((n : ℝ) ^ ((α - 1).re)) / ‖Complex.Gamma α‖ := by rw [hpow]
    _ = (‖C‖ / ‖Complex.Gamma α‖) * (n : ℝ) ^ (α.re - 1) := by
          rw [hre]
          ring

private lemma rpow_scale_isBigO_main_term {α C : ℂ}
    (hC : C ≠ 0) (hα : ∀ m : ℕ, α ≠ -m) :
    (fun n : ℕ => (n : ℝ) ^ (α.re - 1)) =O[atTop]
      (fun n : ℕ => C * (n : ℂ) ^ (α - 1) / Complex.Gamma α) := by
  let K : ℝ := ‖C‖ / ‖Complex.Gamma α‖
  have hΓ : Complex.Gamma α ≠ 0 := Complex.Gamma_ne_zero hα
  have hKpos : 0 < K := by
    exact div_pos (norm_pos_iff.mpr hC) (norm_pos_iff.mpr hΓ)
  have hKne : K ≠ 0 := ne_of_gt hKpos
  refine Asymptotics.isBigO_iff.mpr ⟨K⁻¹, ?_⟩
  filter_upwards [main_term_norm_eventually (α := α) (C := C)] with n hn_norm
  have hscale_nonneg : 0 ≤ (n : ℝ) ^ (α.re - 1) :=
    Real.rpow_nonneg (by exact_mod_cast Nat.zero_le n) _
  calc
    ‖(n : ℝ) ^ (α.re - 1)‖ = (n : ℝ) ^ (α.re - 1) :=
      Real.norm_of_nonneg hscale_nonneg
    _ = K⁻¹ * (K * (n : ℝ) ^ (α.re - 1)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hKne, one_mul]
    _ = K⁻¹ * ‖C * (n : ℂ) ^ (α - 1) / Complex.Gamma α‖ := by
      rw [hn_norm]
    _ ≤ K⁻¹ * ‖C * (n : ℂ) ^ (α - 1) / Complex.Gamma α‖ := le_rfl

end

open Complex Filter Asymptotics
open scoped Topology BigOperators
theorem solution {α C : ℂ} {R φ : ℝ} {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hα : ∀ m : ℕ, α ≠ -m) (hC : C ≠ 0) (hR : 1 < R) (hφ0 : 0 < φ)
    (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ => ‖f z - C * (1 - z) ^ (-α)‖ * ‖(1 : ℂ) - z‖ ^ (α.re))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ => p.coeff n) ~[atTop]
      (fun n : ℕ => C * (n : ℂ) ^ (α - 1) / Complex.Gamma α) := by
  let h : ℂ → ℂ := fun z => (1 - z) ^ (-α)
  let q : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun n : ℕ => Ring.choose (α + n - 1) n)
  have hφπ : φ < Real.pi := by
    nlinarith [Real.pi_pos]
  have hh : HasFPowerSeriesAt h q 0 := by
    have hraw := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero α).hasFPowerSeriesAt
    convert hraw using 1
    ext z
    dsimp [h]
    rw [Complex.cpow_neg, inv_eq_one_div]
  have hΔh : AnalyticOnNhd ℂ h (DeltaDomainArg R φ) := by
    simpa [h] using
      (analyticOnNhd_one_sub_cpow_deltaDomain (α := α) (R := R) (φ := φ) hφ0 hφπ)
  have hpg : HasFPowerSeriesAt (fun z : ℂ => f z - C • h z) (p - C • q) 0 :=
    hp.sub (hh.const_smul (c := C))
  have hΔg : AnalyticOnNhd ℂ (fun z : ℂ => f z - C • h z) (DeltaDomainArg R φ) :=
    hΔ.sub (hΔh.const_smul (c := C))
  have herr_norm : (fun n : ℕ => ‖(p - C • q).coeff n‖) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ (α.re - 1)) := by
    refine coeff_norm_isLittleO_atTop_of_delta_littleO
      (R := R) (φ := φ) (β := α.re) (f := fun z : ℂ => f z - C • h z)
      (p := p - C • q) hR hφ0 hφ2 hpg hΔg ?_
    simpa [h, smul_eq_mul] using hsing
  let main : ℕ → ℂ := fun n => C * q.coeff n
  let err : ℕ → ℂ := fun n => (p - C • q).coeff n
  let target : ℕ → ℂ := fun n => C * (n : ℂ) ^ (α - 1) / Complex.Gamma α
  have hmain : main ~[atTop] target := by
    have hchoose := coeff_oneDivOneSubCpow_isEquivalent (α := α) hα
    have hconst : (fun _ : ℕ => C) ~[atTop] (fun _ : ℕ => C) :=
      Asymptotics.IsEquivalent.refl
    have hmul := hconst.mul hchoose
    simpa [main, target, q, Pi.mul_apply, mul_div_assoc] using hmul
  have herr_scale : err =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α.re - 1)) := by
    exact Asymptotics.IsLittleO.of_norm_left (by simpa [err] using herr_norm)
  have herr_target : err =o[atTop] target := by
    exact herr_scale.trans_isBigO
      (rpow_scale_isBigO_main_term (α := α) (C := C) hC hα)
  have hsum : (main + err) ~[atTop] target := hmain.add_isLittleO herr_target
  have hdecomp : (fun n : ℕ => p.coeff n) =ᶠ[atTop] main + err :=
    Eventually.of_forall fun n => by
      dsimp [main, err]
      rw [coeff_sub_const_smul]
      ring
  exact hdecomp.trans_isEquivalent hsum
