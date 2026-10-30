-- Prove2me | solution 1 for TwoRegularClass.twoRegularClass_counts_div_factorial_thirdOrder
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T13:19:51.525698+00:00
-- url     : https://prove2.me/submissions/f996a504-f635-4722-9ec9-5448e920477d

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_CoeffDescent
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_DeltaDomain
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_DeltaGeometry
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_LittleOTransfer
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_ModelCoeffExplicit
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_ModelCoeffSecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_ModelCoeffThirdOrder
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SubstComp
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_TransferSecondOrderGeneral
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TwoRegular
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledProduct
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSet
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TwoRegularSecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TwoRegularThirdOrder
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledPower
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSetOde
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TwoRegularClass
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSeq
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledCyc
import Definitions.Def_AnalyticCombinatorics_Ch5_Meromorphic_Alignments
import Theorems.Thm_AnalyticCombinatorics_Ch1_CombClass_egf_set
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.Complex.Liouville
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Combinatorics.Enumerative.Composition

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
/-!
# Ch2 §II.1 — Labelled structures and exponential generating functions

Flajolet & Sedgewick, Part A, Chapter II. A *labelled* class is again a graded
family of finite types (we reuse `CombClass`), but is enumerated by its
*exponential* generating function (EGF)

  `A(z) = ∑ₙ Aₙ zⁿ/n!`.

This file defines the EGF and two foundational flagships:
- permutations (`Perm (Fin n)`, `Aₙ = n!`) with EGF `1/(1 - z)`;
- the "set" class (one object of each size) with EGF `e^z`.

The labelled product (the defining feature of EGFs) is developed separately.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

@[simp] lemma coeff_egfSeq (a : ℕ → ℕ) (n : ℕ) :
    coeff n (egfSeq a) = (a n : ℚ) / (n.factorial : ℚ) := by
  rw [egfSeq, coeff_mk]

@[simp] lemma CombClass.coeff_egf (C : CombClass) (n : ℕ) :
    coeff n C.egf = (C.counts n : ℚ) / (n.factorial : ℚ) := by
  rw [CombClass.egf, coeff_egfSeq]

/-! ### Permutations -/

@[simp] lemma CombClass.counts_permutations (n : ℕ) :
    CombClass.permutations.counts n = n.factorial := by
  change Fintype.card (Equiv.Perm (Fin n)) = _
  rw [Fintype.card_perm, Fintype.card_fin]

/-! ### The set class -/

@[simp] lemma CombClass.counts_setClass (n : ℕ) : CombClass.setClass.counts n = 1 := by
  change Fintype.card Unit = _
  simp

end AnalyticCombinatorics.Ch1
end

section
open Filter ENNReal
open scoped PowerSeries Topology NNReal ENNReal

noncomputable section

namespace PowerSeries

@[simp] lemma coeff_toFMLS (f : PowerSeries ℂ) (n : ℕ) :
    (toFMLS f).coeff n = PowerSeries.coeff (R := ℂ) n f := by
  simp [toFMLS]

@[simp] lemma coeff_mapℂ (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (mapℂ f) =
      algebraMap ℚ ℂ (PowerSeries.coeff (R := ℚ) n f) := by
  simp [mapℂ]

@[simp] lemma nnnorm_toFMLS_apply (f : PowerSeries ℂ) (n : ℕ) :
    ‖toFMLS f n‖₊ = ‖PowerSeries.coeff (R := ℂ) n f‖₊ := by
  apply NNReal.eq
  simp [toFMLS]

end PowerSeries
end
end

section
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

lemma zero_mem_deltaDomainArg {R φ : ℝ} (hR : 0 < R) (hφ : φ < Real.pi) :
    (0 : ℂ) ∈ DeltaDomainArg R φ := by
  unfold DeltaDomainArg
  constructor
  · simpa using hR
  constructor
  · norm_num
  · simpa [Complex.arg_neg_one, abs_of_pos Real.pi_pos] using hφ

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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
/-!
# Explicit first-order model coefficient estimate

This file packages the exact Gamma-ratio route for the standard model
coefficient

`[z^n] (1 - z)^(-α) = Ring.choose (α + n - 1) n`.

The algebraic coefficient/Gamma identity is proved here.  The first-order
Gamma-ratio estimate is proved below from Bohr-Mollerup log-convexity.
-/

open Filter Asymptotics
open scoped BigOperators

noncomputable section

lemma choose_ofReal_model (α : ℝ) (n : ℕ) :
    Ring.choose (((α : ℂ) + n - 1)) n =
      ((Ring.choose (α + n - 1) n : ℝ) : ℂ) := by
  rw [Ring.choose]
  rw [Ring.choose]
  change Ring.multichoose ((α : ℂ) + n - 1 - n + 1) n =
    (algebraMap ℝ ℂ) (Ring.multichoose ((α + n - 1 : ℝ) - n + 1) n)
  rw [Ring.map_multichoose (algebraMap ℝ ℂ) ((α + n - 1 : ℝ) - n + 1) n]
  congr 1
  norm_num [Complex.ofReal_add, Complex.ofReal_sub]

private lemma ascPochhammer_eval_eq_prod_range_real (n : ℕ) (r : ℝ) :
    Polynomial.eval r (ascPochhammer ℝ n) = ∏ j ∈ Finset.range n, (r + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ascPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_natCast, ih, Finset.prod_range_succ]

/-- Real product form of the generalized binomial coefficient. -/
lemma choose_eq_prod_range_real (α : ℝ) (n : ℕ) :
    Ring.choose (α + n - 1) n =
      (∏ j ∈ Finset.range n, (α + j)) / (n.factorial : ℝ) := by
  have hmul := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (R := ℝ) α n
  have hfac : (n.factorial : ℝ) * Ring.choose (α + n - 1) n =
      ∏ j ∈ Finset.range n, (α + j) := by
    rw [← Ring.multichoose_eq α n]
    simpa [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval,
      ascPochhammer_eval_eq_prod_range_real] using hmul
  have hne : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hne]
  simpa [mul_comm] using hfac

/-- Iterating `Γ(x+1)=xΓ(x)` along a positive real arithmetic progression. -/
lemma Real.Gamma_add_nat_prod {α : ℝ} (hα : 0 < α) (n : ℕ) :
    Real.Gamma (α + n) = (∏ j ∈ Finset.range n, (α + j)) * Real.Gamma α := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpos : 0 < α + n := by positivity
      have hne : α + n ≠ 0 := ne_of_gt hpos
      calc
        Real.Gamma (α + (n + 1 : ℕ))
            = Real.Gamma ((α + n) + 1) := by
                norm_num [Nat.cast_add, add_assoc, add_comm, add_left_comm]
        _ = (α + n) * Real.Gamma (α + n) := Real.Gamma_add_one hne
        _ = (α + n) * ((∏ j ∈ Finset.range n, (α + j)) * Real.Gamma α) := by
              rw [ih]
        _ = (∏ j ∈ Finset.range (n + 1), (α + j)) * Real.Gamma α := by
              rw [Finset.prod_range_succ]
              ring

/-- Exact Gamma-ratio identity for the real model coefficient. -/
theorem modelCoeff_eq_gamma_ratio {α : ℝ} (hα : 0 < α) (n : ℕ) :
    Ring.choose (α + n - 1) n =
      Real.Gamma (n + α) / (Real.Gamma α * Real.Gamma (n + 1)) := by
  have hchoose := choose_eq_prod_range_real α n
  have hgamma := Real.Gamma_add_nat_prod (α := α) hα n
  have hgamman : Real.Gamma (n + 1 : ℝ) = (n.factorial : ℝ) := by
    simpa using Real.Gamma_nat_eq_factorial n
  have hΓ : Real.Gamma α ≠ 0 := (Real.Gamma_pos_of_pos hα).ne'
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  calc
    Ring.choose (α + n - 1) n
        = (∏ j ∈ Finset.range n, (α + j)) / (n.factorial : ℝ) := hchoose
    _ = ((∏ j ∈ Finset.range n, (α + j)) * Real.Gamma α) /
          (Real.Gamma α * (n.factorial : ℝ)) := by
            field_simp [hΓ, hfac]
    _ = Real.Gamma (n + α) / (Real.Gamma α * Real.Gamma (n + 1)) := by
            rw [← hgamma, hgamman]
            ring_nf

private lemma logGamma_add_one {y : ℝ} (hy : 0 < y) :
    (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
  dsimp [Function.comp_def]
  rw [Real.Gamma_add_one hy.ne']
  rw [Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
  ring

private lemma logGamma_unit_upper
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {n : ℕ} (hn : n ≠ 0) :
    Real.log (Real.Gamma ((n : ℝ) + β))
      ≤ Real.log (Real.Gamma (n : ℝ)) + β * Real.log (n : ℝ) := by
  simpa [Function.comp_def] using
    Real.BohrMollerup.f_add_nat_le
      (f := Real.log ∘ Real.Gamma)
      Real.convexOn_log_Gamma
      (fun {y} hy => logGamma_add_one hy)
      hn hβ0 hβ1

private lemma logGamma_unit_lower
    {β : ℝ} (hβ0 : 0 < β)
    {n : ℕ} (hn : 2 ≤ n) :
    Real.log (Real.Gamma (n : ℝ)) + β * Real.log ((n : ℝ) - 1)
      ≤ Real.log (Real.Gamma ((n : ℝ) + β)) := by
  simpa [Function.comp_def] using
    Real.BohrMollerup.f_add_nat_ge
      (f := Real.log ∘ Real.Gamma)
      Real.convexOn_log_Gamma
      (fun {y} hy => logGamma_add_one hy)
      hn hβ0

private lemma gamma_unit_upper
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {n : ℕ} (hn : n ≠ 0) :
    Real.Gamma ((n : ℝ) + β)
      ≤ Real.Gamma (n : ℝ) * (n : ℝ) ^ β := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hΓn_pos : 0 < Real.Gamma (n : ℝ) := Real.Gamma_pos_of_pos hnpos
  have hΓnb_pos : 0 < Real.Gamma ((n : ℝ) + β) := Real.Gamma_pos_of_pos (by positivity)
  have hrpow_pos : 0 < (n : ℝ) ^ β := Real.rpow_pos_of_pos hnpos β
  rw [← Real.log_le_log_iff hΓnb_pos (mul_pos hΓn_pos hrpow_pos)]
  calc
    Real.log (Real.Gamma ((n : ℝ) + β))
        ≤ Real.log (Real.Gamma (n : ℝ)) + β * Real.log (n : ℝ) :=
          logGamma_unit_upper hβ0 hβ1 hn
    _ = Real.log (Real.Gamma (n : ℝ) * (n : ℝ) ^ β) := by
          rw [Real.log_mul hΓn_pos.ne' hrpow_pos.ne', Real.log_rpow hnpos]

private lemma gamma_unit_lower
    {β : ℝ} (hβ0 : 0 < β)
    {n : ℕ} (hn : 2 ≤ n) :
    Real.Gamma (n : ℝ) * ((n : ℝ) - 1) ^ β
      ≤ Real.Gamma ((n : ℝ) + β) := by
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn1_nat : (1 : ℕ) < n := Nat.lt_of_succ_le hn
  have hn1r : (1 : ℝ) < n := by exact_mod_cast hn1_nat
  have hnm1pos : 0 < (n : ℝ) - 1 := by linarith
  have hΓn_pos : 0 < Real.Gamma (n : ℝ) := Real.Gamma_pos_of_pos hnpos
  have hΓnb_pos : 0 < Real.Gamma ((n : ℝ) + β) := Real.Gamma_pos_of_pos (by positivity)
  have hrpow_pos : 0 < ((n : ℝ) - 1) ^ β := Real.rpow_pos_of_pos hnm1pos β
  rw [← Real.log_le_log_iff (mul_pos hΓn_pos hrpow_pos) hΓnb_pos]
  calc
    Real.log (Real.Gamma (n : ℝ) * ((n : ℝ) - 1) ^ β)
        = Real.log (Real.Gamma (n : ℝ)) + β * Real.log ((n : ℝ) - 1) := by
          rw [Real.log_mul hΓn_pos.ne' hrpow_pos.ne', Real.log_rpow hnm1pos]
    _ ≤ Real.log (Real.Gamma ((n : ℝ) + β)) := logGamma_unit_lower hβ0 hn

private lemma gamma_unit_norm_eq {β : ℝ} {n : ℕ} (hn : 0 < (n : ℝ)) :
    Real.Gamma ((n : ℝ) + β) / Real.Gamma ((n : ℝ) + 1) / ((n : ℝ) ^ (β - 1)) =
      Real.Gamma ((n : ℝ) + β) / (Real.Gamma (n : ℝ) * (n : ℝ) ^ β) := by
  have hΓn_pos : 0 < Real.Gamma (n : ℝ) := Real.Gamma_pos_of_pos hn
  have hpow_pos : 0 < (n : ℝ) ^ (β - 1) := Real.rpow_pos_of_pos hn (β - 1)
  have hpowβ_pos : 0 < (n : ℝ) ^ β := Real.rpow_pos_of_pos hn β
  have hΓn1 : Real.Gamma ((n : ℝ) + 1) = (n : ℝ) * Real.Gamma (n : ℝ) :=
    Real.Gamma_add_one hn.ne'
  have hpow : (n : ℝ) * (n : ℝ) ^ (β - 1) = (n : ℝ) ^ β := by
    calc
      (n : ℝ) * (n : ℝ) ^ (β - 1) =
          (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (β - 1) := by
            rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 : ℝ) + (β - 1)) := by rw [Real.rpow_add hn]
      _ = (n : ℝ) ^ β := by ring_nf
  rw [hΓn1]
  field_simp [hΓn_pos.ne', hn.ne', hpow_pos.ne', hpowβ_pos.ne']
  calc
    Real.Gamma ((n : ℝ) + β) * (n : ℝ) ^ β =
        Real.Gamma ((n : ℝ) + β) * ((n : ℝ) * (n : ℝ) ^ (β - 1)) := by
          rw [hpow]
    _ = (n : ℝ) * Real.Gamma ((n : ℝ) + β) * (n : ℝ) ^ (β - 1) := by ring

private lemma lower_mul_eq {β : ℝ} {n : ℕ} (hn : 2 ≤ n) :
    (1 - (1 : ℝ) / (n : ℝ)) ^ β *
        (Real.Gamma (n : ℝ) * (n : ℝ) ^ β) =
      Real.Gamma (n : ℝ) * ((n : ℝ) - 1) ^ β := by
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn1_nat : (1 : ℕ) < n := Nat.lt_of_succ_le hn
  have hn1r : (1 : ℝ) < n := by exact_mod_cast hn1_nat
  have hnm1_nonneg : 0 ≤ (n : ℝ) - 1 := by linarith
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hnpos
  have hdiv : ((n : ℝ) - 1) / (n : ℝ) = 1 - (1 : ℝ) / (n : ℝ) := by
    field_simp [hnpos.ne']
  have hdivpow : (1 - (1 : ℝ) / (n : ℝ)) ^ β =
      ((n : ℝ) - 1) ^ β / (n : ℝ) ^ β := by
    rw [← hdiv]
    rw [Real.div_rpow hnm1_nonneg hn_nonneg]
  rw [hdivpow]
  have hpowβ_pos : 0 < (n : ℝ) ^ β := Real.rpow_pos_of_pos hnpos β
  field_simp [hpowβ_pos.ne']

private lemma gamma_unit_norm_between
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {n : ℕ} (hn : 2 ≤ n) :
    (1 - (1 : ℝ) / (n : ℝ)) ^ β
      ≤ Real.Gamma ((n : ℝ) + β) / Real.Gamma ((n : ℝ) + 1)
          / ((n : ℝ) ^ (β - 1))
      ∧ Real.Gamma ((n : ℝ) + β) / Real.Gamma ((n : ℝ) + 1)
          / ((n : ℝ) ^ (β - 1)) ≤ 1 := by
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hΓn_pos : 0 < Real.Gamma (n : ℝ) := Real.Gamma_pos_of_pos hnpos
  have hpowβ_pos : 0 < (n : ℝ) ^ β := Real.rpow_pos_of_pos hnpos β
  have hden_pos : 0 < Real.Gamma (n : ℝ) * (n : ℝ) ^ β := mul_pos hΓn_pos hpowβ_pos
  have hR_eq := gamma_unit_norm_eq (β := β) (n := n) hnpos
  constructor
  · rw [hR_eq, le_div_iff₀ hden_pos]
    calc
      (1 - (1 : ℝ) / (n : ℝ)) ^ β * (Real.Gamma (n : ℝ) * (n : ℝ) ^ β)
          = Real.Gamma (n : ℝ) * ((n : ℝ) - 1) ^ β := lower_mul_eq (β := β) hn
      _ ≤ Real.Gamma ((n : ℝ) + β) := gamma_unit_lower hβ0 hn
  · rw [hR_eq, div_le_one hden_pos]
    exact gamma_unit_upper hβ0 hβ1 (Nat.ne_of_gt hnpos_nat)

private lemma one_sub_inv_le_rpow
    {β : ℝ} (hβ1 : β ≤ 1)
    {n : ℕ} (hn : 2 ≤ n) :
    1 - (1 : ℝ) / (n : ℝ)
      ≤ (1 - (1 : ℝ) / (n : ℝ)) ^ β := by
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn1_nat : (1 : ℕ) < n := Nat.lt_of_succ_le hn
  have hn1r : (1 : ℝ) < n := by exact_mod_cast hn1_nat
  have hdivlt : (1 : ℝ) / (n : ℝ) < 1 := (div_lt_one hnpos).mpr hn1r
  have hdiv_nonneg : 0 ≤ (1 : ℝ) / (n : ℝ) := by positivity
  have hx0 : 0 < 1 - (1 : ℝ) / (n : ℝ) := by linarith
  have hx1 : 1 - (1 : ℝ) / (n : ℝ) ≤ 1 := by linarith
  calc
    1 - (1 : ℝ) / (n : ℝ) =
        (1 - (1 : ℝ) / (n : ℝ)) ^ (1 : ℝ) := by
          rw [Real.rpow_one]
    _ ≤ (1 - (1 : ℝ) / (n : ℝ)) ^ β :=
      Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hβ1

private theorem gamma_ratio_unit_rel_error_isBigO
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    (fun n : ℕ =>
      Real.Gamma ((n : ℝ) + β) / Real.Gamma ((n : ℝ) + 1)
        / ((n : ℝ) ^ (β - 1)) - 1)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) := by
  refine IsBigO.of_bound 1 ?_
  refine eventually_atTop.mpr ⟨2, fun n hn => ?_⟩
  have hbetween := gamma_unit_norm_between hβ0 hβ1 hn
  have hlow : 1 - (1 : ℝ) / (n : ℝ)
      ≤ Real.Gamma ((n : ℝ) + β) / Real.Gamma ((n : ℝ) + 1)
          / ((n : ℝ) ^ (β - 1)) :=
    (one_sub_inv_le_rpow hβ1 hn).trans hbetween.1
  have hupper := hbetween.2
  let R : ℝ :=
    Real.Gamma ((n : ℝ) + β) / Real.Gamma ((n : ℝ) + 1)
      / ((n : ℝ) ^ (β - 1))
  have hnonpos : R - 1 ≤ 0 := by simpa [R] using sub_nonpos.mpr hupper
  have hdist : ‖R - 1‖ = 1 - R := by
    rw [Real.norm_of_nonpos hnonpos]
    ring
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hpow_inv : (n : ℝ) ^ (-(1 : ℝ)) = ((n : ℝ)⁻¹) := by
    rw [Real.rpow_neg (le_of_lt hnpos), Real.rpow_one]
  have hle_inv : 1 - R ≤ (n : ℝ)⁻¹ := by
    have hlowR : 1 - (1 : ℝ) / (n : ℝ) ≤ R := by simpa [R] using hlow
    have hlowR' : 1 - (n : ℝ)⁻¹ ≤ R := by simpa [one_div] using hlowR
    linarith
  have hpow_nonneg : 0 ≤ (n : ℝ) ^ (-(1 : ℝ)) := by positivity
  calc
    ‖R - 1‖ = 1 - R := hdist
    _ ≤ (n : ℝ) ^ (-(1 : ℝ)) := by simpa [hpow_inv] using hle_inv
    _ = 1 * ‖(n : ℝ) ^ (-(1 : ℝ))‖ := by
          rw [Real.norm_of_nonneg hpow_nonneg]
          ring

private lemma gammaShiftNorm_succ_eq {β : ℝ} (hβ0 : 0 < β)
    {m n : ℕ} (hn : 0 < n) :
    gammaShiftNorm β (m + 1) n =
      gammaShiftNorm β m n * (1 + (β + (m : ℝ)) / (n : ℝ)) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hΓden_pos : 0 < Real.Gamma ((n : ℝ) + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hpow_m_pos : 0 < (n : ℝ) ^ (β + (m : ℝ) - 1) :=
    Real.rpow_pos_of_pos hnpos _
  have hs_pos : 0 < (n : ℝ) + β + (m : ℝ) := by positivity
  have hΓsucc : Real.Gamma ((n : ℝ) + β + (m + 1 : ℕ)) =
      ((n : ℝ) + β + (m : ℝ)) * Real.Gamma ((n : ℝ) + β + m) := by
    calc
      Real.Gamma ((n : ℝ) + β + (m + 1 : ℕ))
          = Real.Gamma (((n : ℝ) + β + (m : ℝ)) + 1) := by
              norm_num [Nat.cast_add, add_assoc, add_comm, add_left_comm]
      _ = ((n : ℝ) + β + (m : ℝ)) * Real.Gamma ((n : ℝ) + β + m) :=
          Real.Gamma_add_one hs_pos.ne'
  have hpow_succ : (n : ℝ) ^ (β + ((m + 1 : ℕ) : ℝ) - 1) =
      (n : ℝ) ^ (β + (m : ℝ) - 1) * (n : ℝ) := by
    calc
      (n : ℝ) ^ (β + ((m + 1 : ℕ) : ℝ) - 1)
          = (n : ℝ) ^ ((β + (m : ℝ) - 1) + 1) := by
              congr 1
              norm_num [Nat.cast_add]
              ring
      _ = (n : ℝ) ^ (β + (m : ℝ) - 1) * (n : ℝ) ^ (1 : ℝ) := by
          rw [Real.rpow_add hnpos]
      _ = (n : ℝ) ^ (β + (m : ℝ) - 1) * (n : ℝ) := by rw [Real.rpow_one]
  unfold gammaShiftNorm
  rw [hΓsucc, hpow_succ]
  field_simp [hΓden_pos.ne', hpow_m_pos.ne', hnpos.ne']
  ring

private lemma const_div_natCast_isBigO_rpow_neg_one (c : ℝ) :
    (fun n : ℕ => c / (n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) := by
  refine IsBigO.of_bound ‖c‖ ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hpow_inv : (n : ℝ) ^ (-(1 : ℝ)) = ((n : ℝ)⁻¹) := by
    rw [Real.rpow_neg (le_of_lt hnpos), Real.rpow_one]
  calc
    ‖c / (n : ℝ)‖ = ‖c‖ * ‖(n : ℝ) ^ (-(1 : ℝ))‖ := by
      rw [div_eq_mul_inv, norm_mul, hpow_inv]
    _ ≤ ‖c‖ * ‖(n : ℝ) ^ (-(1 : ℝ))‖ := le_rfl

private lemma inv_natCast_rpow_neg_one_isBigO_one :
    (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) =O[atTop]
      (fun _n : ℕ => (1 : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow_inv : (n : ℝ) ^ (-(1 : ℝ)) = ((n : ℝ)⁻¹) := by
    rw [Real.rpow_neg (le_of_lt hnpos), Real.rpow_one]
  have hinv_le : ((n : ℝ)⁻¹) ≤ 1 := inv_le_one_of_one_le₀ hn1
  have hinv_nonneg : 0 ≤ ((n : ℝ)⁻¹) := by positivity
  rw [hpow_inv, Real.norm_of_nonneg hinv_nonneg, Real.norm_of_nonneg zero_le_one]
  simpa using hinv_le

private lemma one_add_const_div_isBigO_one (c : ℝ) :
    (fun n : ℕ => 1 + c / (n : ℝ)) =O[atTop]
      (fun _n : ℕ => (1 : ℝ)) := by
  have hconst : (fun _n : ℕ => (1 : ℝ)) =O[atTop] (fun _n : ℕ => (1 : ℝ)) :=
    isBigO_refl _ _
  have hcdiv := (const_div_natCast_isBigO_rpow_neg_one c).trans
    inv_natCast_rpow_neg_one_isBigO_one
  exact hconst.add hcdiv

private theorem gamma_ratio_shift_rel_error_isBigO
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (m : ℕ) :
    (fun n : ℕ => gammaShiftNorm β m n - 1)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) := by
  induction m with
  | zero =>
      simpa [gammaShiftNorm] using gamma_ratio_unit_rel_error_isBigO hβ0 hβ1
  | succ m ih =>
      let c : ℝ := β + (m : ℝ)
      have hfactor : (fun n : ℕ => 1 + c / (n : ℝ)) =O[atTop]
          (fun _n : ℕ => (1 : ℝ)) := one_add_const_div_isBigO_one c
      have hcdiv : (fun n : ℕ => c / (n : ℝ)) =O[atTop]
          (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) :=
        const_div_natCast_isBigO_rpow_neg_one c
      have hprod0 := ih.mul hfactor
      have hprod : (fun n : ℕ => (gammaShiftNorm β m n - 1) * (1 + c / (n : ℝ)))
          =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) := by
        exact hprod0.congr_right (fun n => by ring)
      have hsum := hprod.add hcdiv
      have heq : (fun n : ℕ => gammaShiftNorm β (m + 1) n - 1) =ᶠ[atTop]
          (fun n : ℕ => (gammaShiftNorm β m n - 1) *
              (1 + c / (n : ℝ)) + c / (n : ℝ)) := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
        rw [gammaShiftNorm_succ_eq hβ0 hnpos]
        dsimp [c]
        ring
      exact heq.trans_isBigO hsum

private theorem gamma_ratio_shift_firstOrder
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (m : ℕ) :
    (fun n : ℕ =>
      Real.Gamma ((n : ℝ) + β + m) / Real.Gamma ((n : ℝ) + 1)
        - (n : ℝ) ^ (β + (m : ℝ) - 1))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (β + (m : ℝ) - 2)) := by
  have hrel := gamma_ratio_shift_rel_error_isBigO hβ0 hβ1 m
  have hp : (fun n : ℕ => (n : ℝ) ^ (β + (m : ℝ) - 1)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (β + (m : ℝ) - 1)) := isBigO_refl _ _
  have hmul : (fun n : ℕ =>
        (n : ℝ) ^ (β + (m : ℝ) - 1) * (gammaShiftNorm β m n - 1))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (β + (m : ℝ) - 2)) := by
    exact IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
      (a := β + (m : ℝ) - 1) (b := -(1 : ℝ)) (c := β + (m : ℝ) - 2)
      hp hrel (by linarith)
  have heq : (fun n : ℕ =>
      Real.Gamma ((n : ℝ) + β + m) / Real.Gamma ((n : ℝ) + 1)
        - (n : ℝ) ^ (β + (m : ℝ) - 1)) =ᶠ[atTop]
      (fun n : ℕ =>
        (n : ℝ) ^ (β + (m : ℝ) - 1) * (gammaShiftNorm β m n - 1)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
    have hp_pos : 0 < (n : ℝ) ^ (β + (m : ℝ) - 1) := Real.rpow_pos_of_pos hnpos _
    unfold gammaShiftNorm
    field_simp [hp_pos.ne']
  exact heq.trans_isBigO hmul

private theorem gamma_ratio_first_order_of_decomp
    {α β : ℝ} (m : ℕ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hα : α = β + (m : ℝ)) :
    (fun n : ℕ => Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1) -
        (n : ℝ) ^ (α - 1))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
  subst α
  simpa [add_assoc, add_comm, add_left_comm] using
    gamma_ratio_shift_firstOrder hβ0 hβ1 m

private theorem gamma_ratio_decomp {α : ℝ} (hα : 0 < α) :
    ∃ (β : ℝ) (m : ℕ), 0 < β ∧ β ≤ 1 ∧ α = β + (m : ℝ) := by
  let m : ℕ := Nat.ceil α - 1
  let β : ℝ := α - (m : ℝ)
  have hceil_pos : 0 < Nat.ceil α := Nat.ceil_pos.mpr hα
  have hm_lt_ceil : m < Nat.ceil α := by
    dsimp [m]
    exact Nat.sub_one_lt (Nat.ne_of_gt hceil_pos)
  have hm_lt_alpha : (m : ℝ) < α := (Nat.lt_ceil).mp hm_lt_ceil
  have hβ0 : 0 < β := by
    dsimp [β]
    linarith
  have hceil_le_alpha : α ≤ (Nat.ceil α : ℝ) := (Nat.ceil_le).mp (le_refl (Nat.ceil α))
  have hm_succ : m + 1 = Nat.ceil α := by
    dsimp [m]
    exact Nat.succ_pred_eq_of_pos hceil_pos
  have hm1_cast : (m : ℝ) + 1 = (Nat.ceil α : ℝ) := by
    rw [← hm_succ]
    norm_num
  have hβ1 : β ≤ 1 := by
    dsimp [β]
    linarith
  refine ⟨β, m, hβ0, hβ1, ?_⟩
  dsimp [β]
  ring

theorem gamma_ratio_first_order {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => Real.Gamma (n + α) / Real.Gamma (n + 1) - (n : ℝ) ^ (α - 1))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
  rcases gamma_ratio_decomp hα with ⟨β, m, hβ0, hβ1, hαeq⟩
  exact gamma_ratio_first_order_of_decomp m hβ0 hβ1 hαeq

/--
Explicit first-order model coefficient estimate:

`[z^n] (1-z)^(-α) - n^(α-1)/Γ(α) = O(n^(α-2))`.
-/
theorem modelCoeff_explicit {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => Ring.choose (α + n - 1) n - (n : ℝ) ^ (α - 1) / Real.Gamma α)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
  have hΓ : Real.Gamma α ≠ 0 := (Real.Gamma_pos_of_pos hα).ne'
  have h :=
    (gamma_ratio_first_order (α := α) hα).const_mul_left (Real.Gamma α)⁻¹
  exact h.congr_left fun n => by
    have hΓn : Real.Gamma (n + 1 : ℝ) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < n + 1)).ne'
    rw [modelCoeff_eq_gamma_ratio (α := α) hα n]
    field_simp [hΓ, hΓn]

end
end

section
/-!
# Second-order model coefficient estimate

This file proves the second coefficient in the Gamma-ratio/model-coefficient
expansion by the recurrence bootstrap route.  It does not use Stirling or
digamma asymptotics.
-/

set_option maxHeartbeats 1200000

open Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

private lemma choose_neg_two (α : ℝ) :
    Ring.choose (-α) 2 = α * (α + 1) / 2 := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose (-α : ℝ) 2
  norm_num [descPochhammer, Polynomial.smeval_mul, Polynomial.smeval_sub,
    Polynomial.smeval_X, Polynomial.smeval_C, Polynomial.smeval_natCast] at h
  nlinarith

private lemma binomial_partialSum_three (α x : ℝ) :
    (binomialSeries ℝ (-α)).partialSum 3 x =
      1 - α * x + (α * (α + 1) / 2) * x ^ 2 := by
  simp [FormalMultilinearSeries.partialSum, binomialSeries, Finset.sum_range_succ,
    choose_neg_two]
  ring_nf

private lemma rpow_neg_sub_quadratic_isBigO (α : ℝ) :
    (fun x : ℝ =>
      (1 + x) ^ (-α) - (1 - α * x + (α * (α + 1) / 2) * x ^ 2))
      =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) := by
  have h :=
    (Real.one_add_rpow_hasFPowerSeriesAt_zero (a := -α)).isBigO_sub_partialSum_pow 3
  exact h.congr_left fun x => by
    rw [binomial_partialSum_three]
    simp

private lemma linear_near_zero_isBigO_one (α : ℝ) :
    (fun x : ℝ => 1 + α * x) =O[𝓝 0] (fun _x : ℝ => (1 : ℝ)) := by
  have ht : Tendsto (fun x : ℝ => 1 + α * x) (𝓝 0) (𝓝 ((fun x : ℝ => 1 + α * x) 0)) :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousAt
  simpa using ht.isBigO_one ℝ

private lemma const_mul_cubic_isBigO_norm_cubic (a : ℝ) :
    (fun x : ℝ => a * x ^ 3) =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) := by
  refine IsBigO.of_bound ‖a‖ ?_
  filter_upwards with x
  calc
    ‖a * x ^ 3‖ = ‖a‖ * ‖x‖ ^ 3 := by
      rw [norm_mul, norm_pow]
    _ ≤ ‖a‖ * ‖‖x‖ ^ 3‖ := by
      rw [Real.norm_of_nonneg (by positivity : 0 ≤ ‖x‖ ^ 3)]

private lemma gammaStep_local_at_zero (α : ℝ) :
    (fun x : ℝ =>
      (1 + α * x) * (1 + x) ^ (-α) - 1 + c1 α * x ^ 2)
      =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) := by
  let q : ℝ → ℝ := fun x => 1 - α * x + (α * (α + 1) / 2) * x ^ 2
  have hrem :
      (fun x : ℝ => (1 + x) ^ (-α) - q x)
        =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) := by
    simpa [q] using rpow_neg_sub_quadratic_isBigO α
  have hlin := linear_near_zero_isBigO_one α
  have hprod0 := hlin.mul hrem
  have hprod :
      (fun x : ℝ => (1 + α * x) * ((1 + x) ^ (-α) - q x))
        =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) := by
    refine hprod0.congr_left ?_ |>.congr_right ?_
    · intro x
      ring_nf
    · intro x
      simp
  have hcubic :
      (fun x : ℝ => (α ^ 2 * (α + 1) / 2) * x ^ 3)
        =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) :=
    const_mul_cubic_isBigO_norm_cubic _
  have hsum := hprod.add hcubic
  exact hsum.congr_left fun x => by
    dsimp [q, c1]
    ring_nf

private lemma inv_norm_cube_eq (n : ℕ) :
    ‖((n : ℝ)⁻¹)‖ ^ 3 = ((n : ℝ)⁻¹) ^ 3 := by
  rw [Real.norm_of_nonneg]
  positivity

private lemma inv_cube_isBigO_inv_sq :
    (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  refine IsBigO.of_bound 1 ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hinv_nonneg : 0 ≤ (n : ℝ)⁻¹ := by positivity
  have hinv_le_one : (n : ℝ)⁻¹ ≤ 1 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact inv_le_one_of_one_le₀ hn1
  rw [Real.norm_of_nonneg (pow_nonneg hinv_nonneg 3),
    Real.norm_of_nonneg (pow_nonneg hinv_nonneg 2)]
  nlinarith [mul_le_mul_of_nonneg_right hinv_le_one (pow_nonneg hinv_nonneg 2)]

private lemma gammaStep_sub_isBigO_inv_cube (α : ℝ) :
    (fun n : ℕ =>
      gammaStep α n - 1 + c1 α * ((n : ℝ)⁻¹) ^ 2)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  have hcomp :=
    (gammaStep_local_at_zero α).comp_tendsto
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine hcomp.congr_left ?_ |>.congr_right ?_
  · intro n
    simp [gammaStep]
  · intro n
    exact inv_norm_cube_eq n

private lemma const_mul_inv_sq_isBigO_inv_sq (a : ℝ) :
    (fun n : ℕ => a * ((n : ℝ)⁻¹) ^ 2)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  exact (isBigO_refl (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) atTop).const_mul_left a

private lemma gammaStep_sub_one_isBigO_inv_sq (α : ℝ) :
    (fun n : ℕ => gammaStep α n - 1)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  have h3 := (gammaStep_sub_isBigO_inv_cube α).trans inv_cube_isBigO_inv_sq
  have hc := const_mul_inv_sq_isBigO_inv_sq (-(c1 α))
  have hsum := h3.add hc
  refine hsum.congr_left ?_
  intro n
  ring_nf

private lemma gammaRatioNorm_succ
    {α : ℝ} (hα : 0 < α) :
    ∀ᶠ n : ℕ in atTop,
      gammaRatioNorm α (n + 1) = gammaRatioNorm α n * gammaStep α n := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
  have hbase_pos : 0 < 1 + (n : ℝ)⁻¹ := by positivity
  have hs_pos : 0 < (n : ℝ) + α := by positivity
  have hΓnum : Real.Gamma (((n + 1 : ℕ) : ℝ) + α) =
      ((n : ℝ) + α) * Real.Gamma ((n : ℝ) + α) := by
    calc
      Real.Gamma (((n + 1 : ℕ) : ℝ) + α)
          = Real.Gamma (((n : ℝ) + α) + 1) := by
              congr 1
              norm_num [Nat.cast_add, add_assoc, add_comm, add_left_comm]
      _ = ((n : ℝ) + α) * Real.Gamma ((n : ℝ) + α) :=
          Real.Gamma_add_one hs_pos.ne'
  have hΓden : Real.Gamma (((n + 1 : ℕ) : ℝ) + 1) =
      ((n : ℝ) + 1) * Real.Gamma ((n : ℝ) + 1) := by
    calc
      Real.Gamma (((n + 1 : ℕ) : ℝ) + 1)
          = Real.Gamma (((n : ℝ) + 1) + 1) := by
              congr 1
              norm_num [Nat.cast_add, add_assoc, add_comm, add_left_comm]
      _ = ((n : ℝ) + 1) * Real.Gamma ((n : ℝ) + 1) := by
          exact Real.Gamma_add_one (by positivity : (n : ℝ) + 1 ≠ 0)
  have hnadd : (n : ℝ) + 1 = (n : ℝ) * (1 + (n : ℝ)⁻¹) := by
    field_simp [hnne]
  have hn1eq : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) * (1 + (n : ℝ)⁻¹) := by
    rw [Nat.cast_add, Nat.cast_one, hnadd]
  have hpow : (((n + 1 : ℕ) : ℝ)) ^ (α - 1) =
      ((n : ℝ) ^ (α - 1)) * (1 + (n : ℝ)⁻¹) ^ (α - 1) := by
    rw [hn1eq]
    rw [Real.mul_rpow (le_of_lt hnpos) (le_of_lt hbase_pos)]
  have hbase_alpha : (1 + (n : ℝ)⁻¹) ^ α =
      (1 + (n : ℝ)⁻¹) ^ (α - 1) * (1 + (n : ℝ)⁻¹) := by
    calc
      (1 + (n : ℝ)⁻¹) ^ α
          = (1 + (n : ℝ)⁻¹) ^ ((α - 1) + 1) := by ring_nf
      _ = (1 + (n : ℝ)⁻¹) ^ (α - 1) *
            (1 + (n : ℝ)⁻¹) ^ (1 : ℝ) := by
          rw [Real.rpow_add hbase_pos]
      _ = (1 + (n : ℝ)⁻¹) ^ (α - 1) * (1 + (n : ℝ)⁻¹) := by
          rw [Real.rpow_one]
  have hΓnum_ne : Real.Gamma ((n : ℝ) + α) ≠ 0 :=
    (Real.Gamma_pos_of_pos hs_pos).ne'
  have hΓden_ne : Real.Gamma ((n : ℝ) + 1) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos (by positivity : 0 < (n : ℝ) + 1)).ne'
  have hpow_n_ne : ((n : ℝ) ^ (α - 1)) ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos _).ne'
  have hbase_pow_ne : (1 + (n : ℝ)⁻¹) ^ (α - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos hbase_pos _).ne'
  have hbase_alpha_ne : (1 + (n : ℝ)⁻¹) ^ α ≠ 0 :=
    (Real.rpow_pos_of_pos hbase_pos _).ne'
  unfold gammaRatioNorm gammaStep
  rw [hΓnum, hΓden, hpow, hnadd, Real.rpow_neg (le_of_lt hbase_pos), hbase_alpha]
  field_simp [hΓnum_ne, hΓden_ne, hpow_n_ne, hbase_pow_ne, hbase_alpha_ne,
    hnne, hbase_pos.ne']

private lemma rpow_neg_one_eq_inv_nat (n : ℕ) :
    (n : ℝ) ^ (-(1 : ℝ)) = (n : ℝ)⁻¹ := by
  rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_one]

private lemma rpow_neg_two_eq_inv_sq_nat (n : ℕ) :
    (n : ℝ) ^ (-(2 : ℝ)) = ((n : ℝ)⁻¹) ^ 2 := by
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  norm_num

private lemma gammaRatioNorm_sub_one_isBigO_inv
    {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => gammaRatioNorm α n - 1)
      =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  set_option backward.isDefEq.respectTransparency false in
    have hA1 := gamma_ratio_first_order hα
    have hp : (fun n : ℕ => (n : ℝ) ^ (1 - α))
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 - α)) := isBigO_refl _ _
    have hmul :
        (fun n : ℕ =>
          (Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1) -
            (n : ℝ) ^ (α - 1)) * (n : ℝ) ^ (1 - α))
          =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) := by
      exact IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
        (a := α - 2) (b := 1 - α) (c := -(1 : ℝ)) hA1 hp (by linarith)
    have heq : (fun n : ℕ => gammaRatioNorm α n - 1) =ᶠ[atTop]
        (fun n : ℕ =>
          (Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1) -
            (n : ℝ) ^ (α - 1)) * (n : ℝ) ^ (1 - α)) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
      have hpow_ne : (n : ℝ) ^ (α - 1) ≠ 0 := (Real.rpow_pos_of_pos hnpos _).ne'
      have hpow_inv : (n : ℝ) ^ (1 - α) = ((n : ℝ) ^ (α - 1))⁻¹ := by
        rw [← Real.rpow_neg (le_of_lt hnpos)]
        congr 1
        ring_nf
      unfold gammaRatioNorm
      rw [hpow_inv]
      field_simp [hpow_ne]
    exact (heq.trans_isBigO hmul).congr_right fun n => by
      rw [rpow_neg_one_eq_inv_nat]

private lemma tail_inv_sq_shift (N : ℕ) :
    (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) ≤
      2 / ((N : ℝ) + 1) := by
  apply Real.tsum_le_of_sum_range_le (fun i => by positivity)
  intro n
  have hreindex : (∑ i ∈ Finset.range n,
      1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2)
      = ∑ k ∈ Finset.Ico (N + 1) (N + 1 + n), 1 / ((k : ℝ)) ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hsub : N + 1 + n - (N + 1) = n := by omega
    rw [hsub]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [show i + N + 1 = N + 1 + i from by omega]
  rw [hreindex]
  have hIco : Finset.Ico (N + 1) (N + 1 + n) = Finset.Ioo N (N + 1 + n) := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  rw [hIco]
  have hbound := sum_Ioo_inv_sq_le (α := ℝ) N (N + 1 + n)
  simp only [one_div]
  exact hbound

private lemma tail_inv_cube_shift (N : ℕ) :
    (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) ≤
      2 / ((N : ℝ) + 1) ^ 2 := by
  have hcube_summ : Summable
      (fun i : ℕ => 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) := by
    have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
    have hshift := (summable_nat_add_iff (N + 1)).mpr h
    refine hshift.congr fun i => ?_
    have he : i + (N + 1) = i + N + 1 := by omega
    rw [he]
  have hsquare_summ : Summable
      (fun i : ℕ => (1 / ((N : ℝ) + 1)) *
        (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2)) := by
    have h : Summable (fun i : ℕ => 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) := by
      have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
      have hshift := (summable_nat_add_iff (N + 1)).mpr hbase
      refine hshift.congr fun i => ?_
      have he : i + (N + 1) = i + N + 1 := by omega
      rw [he]
    exact h.mul_left _
  have hterm : ∀ i : ℕ,
      1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3 ≤
        (1 / ((N : ℝ) + 1)) *
          (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) := by
    intro i
    have hNpos : 0 < (N : ℝ) + 1 := by positivity
    have hkpos : 0 < (((i + N + 1 : ℕ)) : ℝ) := by positivity
    have hle_nat : N + 1 ≤ i + N + 1 := by omega
    have hle : (N : ℝ) + 1 ≤ ((i + N + 1 : ℕ) : ℝ) := by exact_mod_cast hle_nat
    have hinv_le : 1 / (((i + N + 1 : ℕ)) : ℝ) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le hNpos hle
    have hsquare_nonneg : 0 ≤ 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2 := by positivity
    calc
      1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3
          = (1 / (((i + N + 1 : ℕ)) : ℝ)) *
              (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) := by
              field_simp [hkpos.ne']
      _ ≤ (1 / ((N : ℝ) + 1)) *
            (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hinv_le hsquare_nonneg
  have hle := hcube_summ.tsum_le_tsum hterm hsquare_summ
  have hsquare_bound := tail_inv_sq_shift N
  calc
    (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3)
        ≤ ∑' i : ℕ, (1 / ((N : ℝ) + 1)) *
          (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) := hle
    _ = (1 / ((N : ℝ) + 1)) *
          (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) := by
          rw [tsum_mul_left]
    _ ≤ (1 / ((N : ℝ) + 1)) * (2 / ((N : ℝ) + 1)) := by
          exact mul_le_mul_of_nonneg_left hsquare_bound (by positivity)
    _ = 2 / ((N : ℝ) + 1) ^ 2 := by
          field_simp [(by positivity : (N : ℝ) + 1 ≠ 0)]

private lemma summable_of_isBigO_inv_cube {d : ℕ → ℝ}
    (hd : d =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3)) :
    Summable d := by
  rcases hd.exists_pos with ⟨C, hCpos, hC⟩
  have hmajor : Summable (fun n : ℕ => C * (((n : ℝ)⁻¹) ^ 3)) := by
    have h : Summable (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
      have h' : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
      exact h'.congr fun n => by
        rw [one_div, inv_pow]
    exact h.mul_left C
  refine Summable.of_norm_bounded_eventually hmajor ?_
  have hb := hC.bound
  rw [eventually_atTop] at hb
  rcases hb with ⟨N, hN⟩
  rw [Nat.cofinite_eq_atTop, eventually_atTop]
  refine ⟨max N 1, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnonneg : 0 ≤ ((n : ℝ)⁻¹) ^ 3 := by positivity
  have hnorm : ‖((n : ℝ)⁻¹) ^ 3‖ = ((n : ℝ)⁻¹) ^ 3 := by
    rw [Real.norm_of_nonneg hnonneg]
  calc
    ‖d n‖ ≤ C * ‖((n : ℝ)⁻¹) ^ 3‖ := hN n hnN
    _ = C * ((n : ℝ)⁻¹) ^ 3 := by rw [hnorm]

private lemma sum_range_succDiff (u : ℕ → ℝ) (n m : ℕ) :
    (∑ i ∈ Finset.range m, (u (i + n + 1) - u (i + n))) =
      u (n + m) - u n := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : m + n + 1 = n + (m + 1) := by omega
      rw [h1]
      ring_nf

private lemma eq_neg_tsum_succDiff {u : ℕ → ℝ}
    (hu : Tendsto u atTop (𝓝 0))
    (hd_summ : Summable (fun n : ℕ => u (n + 1) - u n)) (n : ℕ) :
    u n = -∑' i : ℕ, (u (i + n + 1) - u (i + n)) := by
  set_option backward.isDefEq.respectTransparency false in
    let d : ℕ → ℝ := fun k => u (k + 1) - u k
    have htail_summ : Summable (fun i : ℕ => d (i + n)) :=
      (summable_nat_add_iff n).mpr hd_summ
    have hleft := htail_summ.tendsto_sum_tsum_nat
    have hleft' :
        Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m, (u (i + n + 1) - u (i + n)))
          atTop (𝓝 (∑' i : ℕ, (u (i + n + 1) - u (i + n)))) := by
      refine hleft.congr' ?_
      filter_upwards with m
      apply Finset.sum_congr rfl
      intro i _hi
      dsimp [d]
    have hright :
        Tendsto (fun m : ℕ => u (n + m) - u n) atTop (𝓝 (0 - u n)) := by
      have hcomp : Tendsto (fun m : ℕ => u (m + n)) atTop (𝓝 0) :=
        hu.comp (tendsto_add_atTop_nat n)
      have hcomp' : Tendsto (fun m : ℕ => u (n + m)) atTop (𝓝 0) := by
        refine hcomp.congr' ?_
        filter_upwards with m
        rw [Nat.add_comm]
      exact hcomp'.sub tendsto_const_nhds
    have hleft'' :
        Tendsto (fun m : ℕ => u (n + m) - u n) atTop
          (𝓝 (∑' i : ℕ, (u (i + n + 1) - u (i + n)))) := by
      refine hleft'.congr' ?_
      filter_upwards with m
      exact sum_range_succDiff u n m
    have hlim := tendsto_nhds_unique hleft'' hright
    rw [hlim]
    ring_nf

private lemma tendsto_zero_of_succDiff_isBigO_inv_cube
    {u : ℕ → ℝ}
    (hu : Tendsto u atTop (𝓝 0))
    (hdiff :
      (fun n : ℕ => u (n + 1) - u n)
        =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3)) :
    u =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  let d : ℕ → ℝ := fun n => u (n + 1) - u n
  rcases hdiff.exists_pos with ⟨C, hCpos, hC⟩
  have hd_summ : Summable d := summable_of_isBigO_inv_cube hdiff
  refine IsBigO.of_bound (2 * C) ?_
  have hCbound := hC.bound
  rw [eventually_atTop] at hCbound
  rcases hCbound with ⟨N, hN⟩
  refine eventually_atTop.mpr ⟨max N 2, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn2
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have htail_eq := eq_neg_tsum_succDiff hu hd_summ n
  have htail_summ : Summable (fun i : ℕ => d (i + n)) :=
    (summable_nat_add_iff n).mpr hd_summ
  have htail_norm_summ : Summable (fun i : ℕ => ‖d (i + n)‖) := by
    rw [summable_norm_iff]
    exact htail_summ
  have hnorm_le := norm_tsum_le_tsum_norm htail_norm_summ
  have hterm_le : ∀ i : ℕ,
      ‖d (i + n)‖ ≤ C * (1 / (((i + n : ℕ)) : ℝ) ^ 3) := by
    intro i
    have hikN : N ≤ i + n := le_trans hnN (by omega)
    have hb := hN (i + n) hikN
    have hnonneg : 0 ≤ (((i + n : ℕ) : ℝ)⁻¹) ^ 3 := by positivity
    have hnorm : ‖(((i + n : ℕ) : ℝ)⁻¹) ^ 3‖ =
        (((i + n : ℕ) : ℝ)⁻¹) ^ 3 := by
      rw [Real.norm_of_nonneg hnonneg]
    calc
      ‖d (i + n)‖ ≤ C * ‖(((i + n : ℕ) : ℝ)⁻¹) ^ 3‖ := hb
      _ = C * (1 / (((i + n : ℕ)) : ℝ) ^ 3) := by
          rw [hnorm, one_div, inv_pow]
  have hmajor_summ : Summable (fun i : ℕ => C * (1 / (((i + n : ℕ)) : ℝ) ^ 3)) := by
    have hbase : Summable (fun i : ℕ => 1 / (((i + n : ℕ)) : ℝ) ^ 3) := by
      have h : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 3) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
      exact (summable_nat_add_iff n).mpr h
    exact hbase.mul_left C
  have htsum_le :
      (∑' i : ℕ, ‖d (i + n)‖) ≤
        ∑' i : ℕ, C * (1 / (((i + n : ℕ)) : ℝ) ^ 3) := by
    exact htail_norm_summ.tsum_le_tsum hterm_le hmajor_summ
  have htail_cube :
      (∑' i : ℕ, 1 / (((i + n : ℕ)) : ℝ) ^ 3) ≤
        2 / (n : ℝ) ^ 2 := by
    have hn_pred : n - 1 + 1 = n := Nat.sub_one_add_one (Nat.ne_of_gt hnpos_nat)
    have h := tail_inv_cube_shift (n - 1)
    have hleft :
        (∑' i : ℕ, 1 / (((i + (n - 1) + 1 : ℕ)) : ℝ) ^ 3) =
          (∑' i : ℕ, 1 / (((i + n : ℕ)) : ℝ) ^ 3) := by
      apply tsum_congr
      intro i
      rw [show i + (n - 1) + 1 = i + n from by omega]
    have hright : 2 / (((n - 1 : ℕ) : ℝ) + 1) ^ 2 = 2 / (n : ℝ) ^ 2 := by
      have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
        exact_mod_cast hn_pred
      rw [hcast]
    rwa [hleft, hright] at h
  have htail_bound :
      (∑' i : ℕ, C * (1 / (((i + n : ℕ)) : ℝ) ^ 3)) ≤
        C * (2 / (n : ℝ) ^ 2) := by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left htail_cube hCpos.le
  have htarget_nonneg : 0 ≤ ((n : ℝ)⁻¹) ^ 2 := by positivity
  have htarget_norm : ‖((n : ℝ)⁻¹) ^ 2‖ = ((n : ℝ)⁻¹) ^ 2 := by
    rw [Real.norm_of_nonneg htarget_nonneg]
  have hpow_rw : 2 * C * ‖((n : ℝ)⁻¹) ^ 2‖ = C * (2 / (n : ℝ) ^ 2) := by
    rw [htarget_norm]
    field_simp [hnpos.ne']
  calc
    ‖u n‖ = ‖∑' i : ℕ, d (i + n)‖ := by
      rw [htail_eq, norm_neg]
    _ ≤ ∑' i : ℕ, ‖d (i + n)‖ := hnorm_le
    _ ≤ ∑' i : ℕ, C * (1 / (((i + n : ℕ)) : ℝ) ^ 3) := htsum_le
    _ ≤ C * (2 / (n : ℝ) ^ 2) := htail_bound
    _ = 2 * C * ‖((n : ℝ)⁻¹) ^ 2‖ := hpow_rw.symm

private lemma inv_sub_inv_succ_sub_inv_sq_isBigO_inv_cube (a : ℝ) :
    (fun n : ℕ =>
      a * ((n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) - ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  refine IsBigO.of_bound ‖a‖ ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn1pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hdiff :
      (n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) - ((n : ℝ)⁻¹) ^ 2 =
        -(1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1))) := by
    field_simp [hnpos.ne', hn1pos.ne']
    norm_num [Nat.cast_add, Nat.cast_one]
  have hden_pos : 0 < (n : ℝ) ^ 2 * ((n : ℝ) + 1) := by positivity
  have habs :
      |(n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) - ((n : ℝ)⁻¹) ^ 2| =
        1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1)) := by
    rw [hdiff, abs_neg, abs_of_nonneg]
    positivity
  have hden_le : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 2 * ((n : ℝ) + 1) := by
    nlinarith [sq_nonneg (n : ℝ), hnpos.le]
  have htail_le :
      1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1)) ≤ 1 / (n : ℝ) ^ 3 := by
    exact one_div_le_one_div_of_le (by positivity : 0 < (n : ℝ) ^ 3) hden_le
  have htarget_nonneg : 0 ≤ ((n : ℝ)⁻¹) ^ 3 := by positivity
  have htarget_norm : ‖((n : ℝ)⁻¹) ^ 3‖ = ((n : ℝ)⁻¹) ^ 3 := by
    rw [Real.norm_of_nonneg htarget_nonneg]
  calc
    ‖a * ((n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) - ((n : ℝ)⁻¹) ^ 2)‖
        = ‖a‖ *
          |(n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) - ((n : ℝ)⁻¹) ^ 2| := by
          rw [norm_mul]
          simp [Real.norm_eq_abs]
    _ = ‖a‖ * (1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1))) := by rw [habs]
    _ ≤ ‖a‖ * (1 / (n : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left htail_le (norm_nonneg a)
    _ = ‖a‖ * ‖((n : ℝ)⁻¹) ^ 3‖ := by
          rw [htarget_norm, one_div, inv_pow]

private lemma gammaSecondError_succDiff_isBigO_inv_cube
    {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => gammaSecondError α (n + 1) - gammaSecondError α n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  set_option backward.isDefEq.respectTransparency false in
    have hY1 := gammaRatioNorm_sub_one_isBigO_inv hα
    have hStep2 := gammaStep_sub_one_isBigO_inv_sq α
    have hStep3 := gammaStep_sub_isBigO_inv_cube α
    have hprod0 := hY1.mul hStep2
    have hprod :
        (fun n : ℕ => (gammaRatioNorm α n - 1) * (gammaStep α n - 1))
          =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
      refine hprod0.congr_right ?_
      intro n
      ring_nf
    have htail := inv_sub_inv_succ_sub_inv_sq_isBigO_inv_cube (c1 α)
    have hsum := (hStep3.add hprod).add htail
    have heq :
        (fun n : ℕ => gammaSecondError α (n + 1) - gammaSecondError α n) =ᶠ[atTop]
          (fun n : ℕ =>
            (gammaStep α n - 1 + c1 α * ((n : ℝ)⁻¹) ^ 2) +
              (gammaRatioNorm α n - 1) * (gammaStep α n - 1) +
              c1 α * ((n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) - ((n : ℝ)⁻¹) ^ 2)) := by
      filter_upwards [gammaRatioNorm_succ hα] with n hrec
      unfold gammaSecondError
      rw [hrec]
      ring_nf
    exact heq.trans_isBigO hsum

private lemma gammaSecondError_tendsto_zero
    {α : ℝ} (hα : 0 < α) :
    Tendsto (gammaSecondError α) atTop (𝓝 0) := by
  have hY := gammaRatioNorm_sub_one_isBigO_inv hα
  have hYlim : Tendsto (fun n : ℕ => gammaRatioNorm α n - 1) atTop (𝓝 0) :=
    hY.trans_tendsto (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hcorr :
      Tendsto (fun n : ℕ => c1 α * (n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (c1 α)
  simpa [gammaSecondError] using hYlim.sub hcorr

private theorem gammaRatioNorm_second_order
    {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => gammaRatioNorm α n - (1 + c1 α * (n : ℝ)⁻¹))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  have hdiff := gammaSecondError_succDiff_isBigO_inv_cube hα
  have hlim := gammaSecondError_tendsto_zero hα
  have h := tendsto_zero_of_succDiff_isBigO_inv_cube hlim hdiff
  exact h.congr_left fun n => by
    unfold gammaSecondError
    ring_nf

theorem gamma_ratio_second_order {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ =>
      Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1) -
        (n : ℝ) ^ (α - 1) * (1 + α * (α - 1) / (2 * (n : ℝ))))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 3)) := by
  have hnorm := gammaRatioNorm_second_order hα
  have hnorm_rpow :
      (fun n : ℕ => gammaRatioNorm α n - (1 + c1 α * (n : ℝ)⁻¹))
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ))) := by
    exact hnorm.congr_right fun n => (rpow_neg_two_eq_inv_sq_nat n).symm
  have hp : (fun n : ℕ => (n : ℝ) ^ (α - 1))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 1)) := isBigO_refl _ _
  have hmul :
      (fun n : ℕ =>
        (n : ℝ) ^ (α - 1) *
          (gammaRatioNorm α n - (1 + c1 α * (n : ℝ)⁻¹)))
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 3)) := by
    exact IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
      (a := α - 1) (b := -(2 : ℝ)) (c := α - 3) hp hnorm_rpow (by linarith)
  have heq :
      (fun n : ℕ =>
        Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1) -
          (n : ℝ) ^ (α - 1) * (1 + α * (α - 1) / (2 * (n : ℝ)))) =ᶠ[atTop]
        (fun n : ℕ =>
          (n : ℝ) ^ (α - 1) *
            (gammaRatioNorm α n - (1 + c1 α * (n : ℝ)⁻¹))) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
    have hpow_ne : (n : ℝ) ^ (α - 1) ≠ 0 := (Real.rpow_pos_of_pos hnpos _).ne'
    unfold gammaRatioNorm c1
    field_simp [hpow_ne, hnpos.ne']
  exact heq.trans_isBigO hmul

theorem modelCoeff_secondOrder {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ =>
      Ring.choose (α + n - 1) n -
        ((n : ℝ) ^ (α - 1) / Real.Gamma α) *
          (1 + α * (α - 1) / (2 * (n : ℝ))))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 3)) := by
  have hΓ : Real.Gamma α ≠ 0 := (Real.Gamma_pos_of_pos hα).ne'
  have h := (gamma_ratio_second_order hα).const_mul_left (Real.Gamma α)⁻¹
  refine h.congr_left ?_
  intro n
  rw [modelCoeff_eq_gamma_ratio hα n]
  field_simp [hΓ]

end
end

section
/-!
# Third-order model coefficient estimate

This file proves the third coefficient in the Gamma-ratio/model-coefficient
expansion by the recurrence bootstrap route.  It does not use Stirling or
digamma asymptotics.
-/

set_option maxHeartbeats 1200000

open Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

private lemma choose_neg_two_p2m2 (α : ℝ) :
    Ring.choose (-α) 2 = α * (α + 1) / 2 := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose (-α : ℝ) 2
  norm_num [descPochhammer, Polynomial.smeval_mul, Polynomial.smeval_sub,
    Polynomial.smeval_X, Polynomial.smeval_C, Polynomial.smeval_natCast] at h
  nlinarith

private lemma choose_neg_three (α : ℝ) :
    Ring.choose (-α) 3 = -α * (α + 1) * (α + 2) / 6 := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose (-α : ℝ) 3
  norm_num [descPochhammer, Polynomial.smeval_mul, Polynomial.smeval_sub,
    Polynomial.smeval_X, Polynomial.smeval_C, Polynomial.smeval_natCast] at h
  nlinarith

private lemma binomial_partialSum_three_p2m2 (α x : ℝ) :
    (binomialSeries ℝ (-α)).partialSum 3 x =
      1 - α * x + (α * (α + 1) / 2) * x ^ 2 := by
  simp [FormalMultilinearSeries.partialSum, binomialSeries, Finset.sum_range_succ,
    choose_neg_two_p2m2]
  ring_nf

private lemma binomial_partialSum_four (α x : ℝ) :
    (binomialSeries ℝ (-α)).partialSum 4 x =
      1 - α * x + (α * (α + 1) / 2) * x ^ 2 -
        (α * (α + 1) * (α + 2) / 6) * x ^ 3 := by
  simp [FormalMultilinearSeries.partialSum, binomialSeries, Finset.sum_range_succ,
    choose_neg_two_p2m2, choose_neg_three]
  ring_nf

private lemma rpow_neg_sub_quadratic_isBigO_p2m2 (α : ℝ) :
    (fun x : ℝ =>
      (1 + x) ^ (-α) - (1 - α * x + (α * (α + 1) / 2) * x ^ 2))
      =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) := by
  have h :=
    (Real.one_add_rpow_hasFPowerSeriesAt_zero (a := -α)).isBigO_sub_partialSum_pow 3
  exact h.congr_left fun x => by
    rw [binomial_partialSum_three_p2m2]
    simp

private lemma rpow_neg_sub_cubic_isBigO (α : ℝ) :
    (fun x : ℝ =>
      (1 + x) ^ (-α) -
        (1 - α * x + (α * (α + 1) / 2) * x ^ 2 -
          (α * (α + 1) * (α + 2) / 6) * x ^ 3))
      =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 4) := by
  have h :=
    (Real.one_add_rpow_hasFPowerSeriesAt_zero (a := -α)).isBigO_sub_partialSum_pow 4
  exact h.congr_left fun x => by
    rw [binomial_partialSum_four]
    simp

private lemma linear_near_zero_isBigO_one_p2m2 (α : ℝ) :
    (fun x : ℝ => 1 + α * x) =O[𝓝 0] (fun _x : ℝ => (1 : ℝ)) := by
  have ht : Tendsto (fun x : ℝ => 1 + α * x) (𝓝 0) (𝓝 ((fun x : ℝ => 1 + α * x) 0)) :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousAt
  simpa using ht.isBigO_one ℝ

private lemma const_mul_cubic_isBigO_norm_cubic_p2m2 (a : ℝ) :
    (fun x : ℝ => a * x ^ 3) =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) := by
  refine IsBigO.of_bound ‖a‖ ?_
  filter_upwards with x
  calc
    ‖a * x ^ 3‖ = ‖a‖ * ‖x‖ ^ 3 := by
      rw [norm_mul, norm_pow]
    _ ≤ ‖a‖ * ‖‖x‖ ^ 3‖ := by
      rw [Real.norm_of_nonneg (by positivity : 0 ≤ ‖x‖ ^ 3)]

private lemma const_mul_quartic_isBigO_norm_quartic (a : ℝ) :
    (fun x : ℝ => a * x ^ 4) =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 4) := by
  refine IsBigO.of_bound ‖a‖ ?_
  filter_upwards with x
  calc
    ‖a * x ^ 4‖ = ‖a‖ * ‖x‖ ^ 4 := by
      rw [norm_mul, norm_pow]
    _ ≤ ‖a‖ * ‖‖x‖ ^ 4‖ := by
      rw [Real.norm_of_nonneg (by positivity : 0 ≤ ‖x‖ ^ 4)]

private lemma gammaStep_local_at_zero_p2m2 (α : ℝ) :
    (fun x : ℝ =>
      (1 + α * x) * (1 + x) ^ (-α) - 1 + c1 α * x ^ 2)
      =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) := by
  let q : ℝ → ℝ := fun x => 1 - α * x + (α * (α + 1) / 2) * x ^ 2
  have hrem :
      (fun x : ℝ => (1 + x) ^ (-α) - q x)
        =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) := by
    simpa [q] using rpow_neg_sub_quadratic_isBigO_p2m2 α
  have hlin := linear_near_zero_isBigO_one_p2m2 α
  have hprod0 := hlin.mul hrem
  have hprod :
      (fun x : ℝ => (1 + α * x) * ((1 + x) ^ (-α) - q x))
        =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) := by
    refine hprod0.congr_left ?_ |>.congr_right ?_
    · intro x
      ring_nf
    · intro x
      simp
  have hcubic :
      (fun x : ℝ => (α ^ 2 * (α + 1) / 2) * x ^ 3)
        =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) :=
    const_mul_cubic_isBigO_norm_cubic_p2m2 _
  have hsum := hprod.add hcubic
  exact hsum.congr_left fun x => by
    dsimp [q, c1]
    ring_nf

private lemma gammaStep_local_third (α : ℝ) :
    (fun x : ℝ =>
      (1 + α * x) * (1 + x) ^ (-α) -
        (1 - c1 α * x ^ 2 + d3 α * x ^ 3))
      =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 4) := by
  let q : ℝ → ℝ := fun x =>
    1 - α * x + (α * (α + 1) / 2) * x ^ 2 -
      (α * (α + 1) * (α + 2) / 6) * x ^ 3
  have hrem :
      (fun x : ℝ => (1 + x) ^ (-α) - q x)
        =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 4) := by
    simpa [q] using rpow_neg_sub_cubic_isBigO α
  have hlin := linear_near_zero_isBigO_one_p2m2 α
  have hprod0 := hlin.mul hrem
  have hprod :
      (fun x : ℝ => (1 + α * x) * ((1 + x) ^ (-α) - q x))
        =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 4) := by
    refine hprod0.congr_left ?_ |>.congr_right ?_
    · intro x
      ring_nf
    · intro x
      simp
  have hquartic :
      (fun x : ℝ => (-(α ^ 2 * (α + 1) * (α + 2) / 6)) * x ^ 4)
        =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 4) :=
    const_mul_quartic_isBigO_norm_quartic _
  have hsum := hprod.add hquartic
  exact hsum.congr_left fun x => by
    dsimp [q, c1, d3]
    ring_nf

private lemma inv_norm_cube_eq_p2m2 (n : ℕ) :
    ‖((n : ℝ)⁻¹)‖ ^ 3 = ((n : ℝ)⁻¹) ^ 3 := by
  rw [Real.norm_of_nonneg]
  positivity

private lemma inv_norm_four_eq (n : ℕ) :
    ‖((n : ℝ)⁻¹)‖ ^ 4 = ((n : ℝ)⁻¹) ^ 4 := by
  rw [Real.norm_of_nonneg]
  positivity

private lemma inv_cube_isBigO_inv_sq_p2m2 :
    (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  refine IsBigO.of_bound 1 ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hinv_nonneg : 0 ≤ (n : ℝ)⁻¹ := by positivity
  have hinv_le_one : (n : ℝ)⁻¹ ≤ 1 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact inv_le_one_of_one_le₀ hn1
  rw [Real.norm_of_nonneg (pow_nonneg hinv_nonneg 3),
    Real.norm_of_nonneg (pow_nonneg hinv_nonneg 2)]
  nlinarith [mul_le_mul_of_nonneg_right hinv_le_one (pow_nonneg hinv_nonneg 2)]

private lemma gammaStep_sub_isBigO_inv_cube_p2m2 (α : ℝ) :
    (fun n : ℕ =>
      gammaStep α n - 1 + c1 α * ((n : ℝ)⁻¹) ^ 2)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  have hcomp :=
    (gammaStep_local_at_zero_p2m2 α).comp_tendsto
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine hcomp.congr_left ?_ |>.congr_right ?_
  · intro n
    simp [gammaStep]
  · intro n
    exact inv_norm_cube_eq_p2m2 n

private lemma gammaStep_sub_third_isBigO_inv_four (α : ℝ) :
    (fun n : ℕ =>
      gammaStep α n -
        (1 - c1 α * ((n : ℝ)⁻¹) ^ 2 +
          d3 α * ((n : ℝ)⁻¹) ^ 3))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4) := by
  have hcomp :=
    (gammaStep_local_third α).comp_tendsto
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine hcomp.congr_left ?_ |>.congr_right ?_
  · intro n
    simp [gammaStep]
  · intro n
    exact inv_norm_four_eq n

private lemma const_mul_inv_sq_isBigO_inv_sq_p2m2 (a : ℝ) :
    (fun n : ℕ => a * ((n : ℝ)⁻¹) ^ 2)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  exact (isBigO_refl (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) atTop).const_mul_left a

private lemma gammaStep_sub_one_isBigO_inv_sq_p2m2 (α : ℝ) :
    (fun n : ℕ => gammaStep α n - 1)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  have h3 := (gammaStep_sub_isBigO_inv_cube_p2m2 α).trans inv_cube_isBigO_inv_sq_p2m2
  have hc := const_mul_inv_sq_isBigO_inv_sq_p2m2 (-(c1 α))
  have hsum := h3.add hc
  refine hsum.congr_left ?_
  intro n
  ring_nf

private lemma gammaRatioNorm_succ_p2m2
    {α : ℝ} (hα : 0 < α) :
    ∀ᶠ n : ℕ in atTop,
      gammaRatioNorm α (n + 1) = gammaRatioNorm α n * gammaStep α n := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
  have hbase_pos : 0 < 1 + (n : ℝ)⁻¹ := by positivity
  have hs_pos : 0 < (n : ℝ) + α := by positivity
  have hΓnum : Real.Gamma (((n + 1 : ℕ) : ℝ) + α) =
      ((n : ℝ) + α) * Real.Gamma ((n : ℝ) + α) := by
    calc
      Real.Gamma (((n + 1 : ℕ) : ℝ) + α)
          = Real.Gamma (((n : ℝ) + α) + 1) := by
              congr 1
              norm_num [Nat.cast_add, add_assoc, add_comm, add_left_comm]
      _ = ((n : ℝ) + α) * Real.Gamma ((n : ℝ) + α) :=
          Real.Gamma_add_one hs_pos.ne'
  have hΓden : Real.Gamma (((n + 1 : ℕ) : ℝ) + 1) =
      ((n : ℝ) + 1) * Real.Gamma ((n : ℝ) + 1) := by
    calc
      Real.Gamma (((n + 1 : ℕ) : ℝ) + 1)
          = Real.Gamma (((n : ℝ) + 1) + 1) := by
              congr 1
              norm_num [Nat.cast_add, add_assoc, add_comm, add_left_comm]
      _ = ((n : ℝ) + 1) * Real.Gamma ((n : ℝ) + 1) := by
          exact Real.Gamma_add_one (by positivity : (n : ℝ) + 1 ≠ 0)
  have hnadd : (n : ℝ) + 1 = (n : ℝ) * (1 + (n : ℝ)⁻¹) := by
    field_simp [hnne]
  have hn1eq : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) * (1 + (n : ℝ)⁻¹) := by
    rw [Nat.cast_add, Nat.cast_one, hnadd]
  have hpow : (((n + 1 : ℕ) : ℝ)) ^ (α - 1) =
      ((n : ℝ) ^ (α - 1)) * (1 + (n : ℝ)⁻¹) ^ (α - 1) := by
    rw [hn1eq]
    rw [Real.mul_rpow (le_of_lt hnpos) (le_of_lt hbase_pos)]
  have hbase_alpha : (1 + (n : ℝ)⁻¹) ^ α =
      (1 + (n : ℝ)⁻¹) ^ (α - 1) * (1 + (n : ℝ)⁻¹) := by
    calc
      (1 + (n : ℝ)⁻¹) ^ α
          = (1 + (n : ℝ)⁻¹) ^ ((α - 1) + 1) := by ring_nf
      _ = (1 + (n : ℝ)⁻¹) ^ (α - 1) *
            (1 + (n : ℝ)⁻¹) ^ (1 : ℝ) := by
          rw [Real.rpow_add hbase_pos]
      _ = (1 + (n : ℝ)⁻¹) ^ (α - 1) * (1 + (n : ℝ)⁻¹) := by
          rw [Real.rpow_one]
  have hΓnum_ne : Real.Gamma ((n : ℝ) + α) ≠ 0 :=
    (Real.Gamma_pos_of_pos hs_pos).ne'
  have hΓden_ne : Real.Gamma ((n : ℝ) + 1) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos (by positivity : 0 < (n : ℝ) + 1)).ne'
  have hpow_n_ne : ((n : ℝ) ^ (α - 1)) ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos _).ne'
  have hbase_pow_ne : (1 + (n : ℝ)⁻¹) ^ (α - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos hbase_pos _).ne'
  have hbase_alpha_ne : (1 + (n : ℝ)⁻¹) ^ α ≠ 0 :=
    (Real.rpow_pos_of_pos hbase_pos _).ne'
  unfold gammaRatioNorm gammaStep
  rw [hΓnum, hΓden, hpow, hnadd, Real.rpow_neg (le_of_lt hbase_pos), hbase_alpha]
  field_simp [hΓnum_ne, hΓden_ne, hpow_n_ne, hbase_pow_ne, hbase_alpha_ne,
    hnne, hbase_pos.ne']

private lemma rpow_neg_one_eq_inv_nat_p2m2 (n : ℕ) :
    (n : ℝ) ^ (-(1 : ℝ)) = (n : ℝ)⁻¹ := by
  rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_one]

private lemma rpow_neg_three_eq_inv_cube_nat (n : ℕ) :
    (n : ℝ) ^ (-(3 : ℝ)) = ((n : ℝ)⁻¹) ^ 3 := by
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  norm_num

private lemma gammaRatioNorm_sub_one_isBigO_inv_p2m2
    {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => gammaRatioNorm α n - 1)
      =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  set_option backward.isDefEq.respectTransparency false in
    have hA1 := gamma_ratio_first_order hα
    have hp : (fun n : ℕ => (n : ℝ) ^ (1 - α))
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 - α)) := isBigO_refl _ _
    have hmul :
        (fun n : ℕ =>
          (Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1) -
            (n : ℝ) ^ (α - 1)) * (n : ℝ) ^ (1 - α))
          =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) := by
      exact IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
        (a := α - 2) (b := 1 - α) (c := -(1 : ℝ)) hA1 hp (by linarith)
    have heq : (fun n : ℕ => gammaRatioNorm α n - 1) =ᶠ[atTop]
        (fun n : ℕ =>
          (Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1) -
            (n : ℝ) ^ (α - 1)) * (n : ℝ) ^ (1 - α)) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
      have hpow_ne : (n : ℝ) ^ (α - 1) ≠ 0 := (Real.rpow_pos_of_pos hnpos _).ne'
      have hpow_inv : (n : ℝ) ^ (1 - α) = ((n : ℝ) ^ (α - 1))⁻¹ := by
        rw [← Real.rpow_neg (le_of_lt hnpos)]
        congr 1
        ring_nf
      unfold gammaRatioNorm
      rw [hpow_inv]
      field_simp [hpow_ne]
    exact (heq.trans_isBigO hmul).congr_right fun n => by
      rw [rpow_neg_one_eq_inv_nat_p2m2]

private lemma tail_inv_sq_shift_p2m2 (N : ℕ) :
    (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) ≤
      2 / ((N : ℝ) + 1) := by
  apply Real.tsum_le_of_sum_range_le (fun i => by positivity)
  intro n
  have hreindex : (∑ i ∈ Finset.range n,
      1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2)
      = ∑ k ∈ Finset.Ico (N + 1) (N + 1 + n), 1 / ((k : ℝ)) ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hsub : N + 1 + n - (N + 1) = n := by omega
    rw [hsub]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [show i + N + 1 = N + 1 + i from by omega]
  rw [hreindex]
  have hIco : Finset.Ico (N + 1) (N + 1 + n) = Finset.Ioo N (N + 1 + n) := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  rw [hIco]
  have hbound := sum_Ioo_inv_sq_le (α := ℝ) N (N + 1 + n)
  simp only [one_div]
  exact hbound

private lemma tail_inv_cube_shift_p2m2 (N : ℕ) :
    (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) ≤
      2 / ((N : ℝ) + 1) ^ 2 := by
  have hcube_summ : Summable
      (fun i : ℕ => 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) := by
    have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
    have hshift := (summable_nat_add_iff (N + 1)).mpr h
    refine hshift.congr fun i => ?_
    have he : i + (N + 1) = i + N + 1 := by omega
    rw [he]
  have hsquare_summ : Summable
      (fun i : ℕ => (1 / ((N : ℝ) + 1)) *
        (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2)) := by
    have h : Summable (fun i : ℕ => 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) := by
      have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
      have hshift := (summable_nat_add_iff (N + 1)).mpr hbase
      refine hshift.congr fun i => ?_
      have he : i + (N + 1) = i + N + 1 := by omega
      rw [he]
    exact h.mul_left _
  have hterm : ∀ i : ℕ,
      1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3 ≤
        (1 / ((N : ℝ) + 1)) *
          (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) := by
    intro i
    have hNpos : 0 < (N : ℝ) + 1 := by positivity
    have hkpos : 0 < (((i + N + 1 : ℕ)) : ℝ) := by positivity
    have hle_nat : N + 1 ≤ i + N + 1 := by omega
    have hle : (N : ℝ) + 1 ≤ ((i + N + 1 : ℕ) : ℝ) := by exact_mod_cast hle_nat
    have hinv_le : 1 / (((i + N + 1 : ℕ)) : ℝ) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le hNpos hle
    have hsquare_nonneg : 0 ≤ 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2 := by positivity
    calc
      1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3
          = (1 / (((i + N + 1 : ℕ)) : ℝ)) *
              (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) := by
              field_simp [hkpos.ne']
      _ ≤ (1 / ((N : ℝ) + 1)) *
            (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hinv_le hsquare_nonneg
  have hle := hcube_summ.tsum_le_tsum hterm hsquare_summ
  have hsquare_bound := tail_inv_sq_shift_p2m2 N
  calc
    (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3)
        ≤ ∑' i : ℕ, (1 / ((N : ℝ) + 1)) *
          (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) := hle
    _ = (1 / ((N : ℝ) + 1)) *
          (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) := by
          rw [tsum_mul_left]
    _ ≤ (1 / ((N : ℝ) + 1)) * (2 / ((N : ℝ) + 1)) := by
          exact mul_le_mul_of_nonneg_left hsquare_bound (by positivity)
    _ = 2 / ((N : ℝ) + 1) ^ 2 := by
          field_simp [(by positivity : (N : ℝ) + 1 ≠ 0)]

private lemma tail_inv_four_shift (N : ℕ) :
    (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 4) ≤
      2 / ((N : ℝ) + 1) ^ 3 := by
  have hfour_summ : Summable
      (fun i : ℕ => 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 4) := by
    have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 4) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 4)
    have hshift := (summable_nat_add_iff (N + 1)).mpr h
    refine hshift.congr fun i => ?_
    have he : i + (N + 1) = i + N + 1 := by omega
    rw [he]
  have hcube_summ : Summable
      (fun i : ℕ => (1 / ((N : ℝ) + 1)) *
        (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3)) := by
    have h : Summable (fun i : ℕ => 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) := by
      have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
      have hshift := (summable_nat_add_iff (N + 1)).mpr hbase
      refine hshift.congr fun i => ?_
      have he : i + (N + 1) = i + N + 1 := by omega
      rw [he]
    exact h.mul_left _
  have hterm : ∀ i : ℕ,
      1 / (((i + N + 1 : ℕ)) : ℝ) ^ 4 ≤
        (1 / ((N : ℝ) + 1)) *
          (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) := by
    intro i
    have hNpos : 0 < (N : ℝ) + 1 := by positivity
    have hkpos : 0 < (((i + N + 1 : ℕ)) : ℝ) := by positivity
    have hle_nat : N + 1 ≤ i + N + 1 := by omega
    have hle : (N : ℝ) + 1 ≤ ((i + N + 1 : ℕ) : ℝ) := by exact_mod_cast hle_nat
    have hinv_le : 1 / (((i + N + 1 : ℕ)) : ℝ) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le hNpos hle
    have hcube_nonneg : 0 ≤ 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3 := by positivity
    calc
      1 / (((i + N + 1 : ℕ)) : ℝ) ^ 4
          = (1 / (((i + N + 1 : ℕ)) : ℝ)) *
              (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) := by
              field_simp [hkpos.ne']
      _ ≤ (1 / ((N : ℝ) + 1)) *
            (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_right hinv_le hcube_nonneg
  have hle := hfour_summ.tsum_le_tsum hterm hcube_summ
  have hcube_bound := tail_inv_cube_shift_p2m2 N
  calc
    (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 4)
        ≤ ∑' i : ℕ, (1 / ((N : ℝ) + 1)) *
          (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) := hle
    _ = (1 / ((N : ℝ) + 1)) *
          (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) := by
          rw [tsum_mul_left]
    _ ≤ (1 / ((N : ℝ) + 1)) * (2 / ((N : ℝ) + 1) ^ 2) := by
          exact mul_le_mul_of_nonneg_left hcube_bound (by positivity)
    _ = 2 / ((N : ℝ) + 1) ^ 3 := by
          field_simp [(by positivity : (N : ℝ) + 1 ≠ 0)]

private lemma summable_of_isBigO_inv_cube_p2m2 {d : ℕ → ℝ}
    (hd : d =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3)) :
    Summable d := by
  rcases hd.exists_pos with ⟨C, hCpos, hC⟩
  have hmajor : Summable (fun n : ℕ => C * (((n : ℝ)⁻¹) ^ 3)) := by
    have h : Summable (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
      have h' : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
      exact h'.congr fun n => by
        rw [one_div, inv_pow]
    exact h.mul_left C
  refine Summable.of_norm_bounded_eventually hmajor ?_
  have hb := hC.bound
  rw [eventually_atTop] at hb
  rcases hb with ⟨N, hN⟩
  rw [Nat.cofinite_eq_atTop, eventually_atTop]
  refine ⟨max N 1, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnonneg : 0 ≤ ((n : ℝ)⁻¹) ^ 3 := by positivity
  have hnorm : ‖((n : ℝ)⁻¹) ^ 3‖ = ((n : ℝ)⁻¹) ^ 3 := by
    rw [Real.norm_of_nonneg hnonneg]
  calc
    ‖d n‖ ≤ C * ‖((n : ℝ)⁻¹) ^ 3‖ := hN n hnN
    _ = C * ((n : ℝ)⁻¹) ^ 3 := by rw [hnorm]

private lemma summable_of_isBigO_inv_four {d : ℕ → ℝ}
    (hd : d =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4)) :
    Summable d := by
  rcases hd.exists_pos with ⟨C, hCpos, hC⟩
  have hmajor : Summable (fun n : ℕ => C * (((n : ℝ)⁻¹) ^ 4)) := by
    have h : Summable (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4) := by
      have h' : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 4) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 4)
      exact h'.congr fun n => by
        rw [one_div, inv_pow]
    exact h.mul_left C
  refine Summable.of_norm_bounded_eventually hmajor ?_
  have hb := hC.bound
  rw [eventually_atTop] at hb
  rcases hb with ⟨N, hN⟩
  rw [Nat.cofinite_eq_atTop, eventually_atTop]
  refine ⟨max N 1, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnonneg : 0 ≤ ((n : ℝ)⁻¹) ^ 4 := by positivity
  have hnorm : ‖((n : ℝ)⁻¹) ^ 4‖ = ((n : ℝ)⁻¹) ^ 4 := by
    rw [Real.norm_of_nonneg hnonneg]
  calc
    ‖d n‖ ≤ C * ‖((n : ℝ)⁻¹) ^ 4‖ := hN n hnN
    _ = C * ((n : ℝ)⁻¹) ^ 4 := by rw [hnorm]

private lemma sum_range_succDiff_p2m2 (u : ℕ → ℝ) (n m : ℕ) :
    (∑ i ∈ Finset.range m, (u (i + n + 1) - u (i + n))) =
      u (n + m) - u n := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : m + n + 1 = n + (m + 1) := by omega
      rw [h1]
      ring_nf

private lemma eq_neg_tsum_succDiff_p2m2 {u : ℕ → ℝ}
    (hu : Tendsto u atTop (𝓝 0))
    (hd_summ : Summable (fun n : ℕ => u (n + 1) - u n)) (n : ℕ) :
    u n = -∑' i : ℕ, (u (i + n + 1) - u (i + n)) := by
  set_option backward.isDefEq.respectTransparency false in
    let d : ℕ → ℝ := fun k => u (k + 1) - u k
    have htail_summ : Summable (fun i : ℕ => d (i + n)) :=
      (summable_nat_add_iff n).mpr hd_summ
    have hleft := htail_summ.tendsto_sum_tsum_nat
    have hleft' :
        Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m, (u (i + n + 1) - u (i + n)))
          atTop (𝓝 (∑' i : ℕ, (u (i + n + 1) - u (i + n)))) := by
      refine hleft.congr' ?_
      filter_upwards with m
      apply Finset.sum_congr rfl
      intro i _hi
      dsimp [d]
    have hright :
        Tendsto (fun m : ℕ => u (n + m) - u n) atTop (𝓝 (0 - u n)) := by
      have hcomp : Tendsto (fun m : ℕ => u (m + n)) atTop (𝓝 0) :=
        hu.comp (tendsto_add_atTop_nat n)
      have hcomp' : Tendsto (fun m : ℕ => u (n + m)) atTop (𝓝 0) := by
        refine hcomp.congr' ?_
        filter_upwards with m
        rw [Nat.add_comm]
      exact hcomp'.sub tendsto_const_nhds
    have hleft'' :
        Tendsto (fun m : ℕ => u (n + m) - u n) atTop
          (𝓝 (∑' i : ℕ, (u (i + n + 1) - u (i + n)))) := by
      refine hleft'.congr' ?_
      filter_upwards with m
      exact sum_range_succDiff_p2m2 u n m
    have hlim := tendsto_nhds_unique hleft'' hright
    rw [hlim]
    ring_nf

private lemma tendsto_zero_of_succDiff_isBigO_inv_cube_p2m2
    {u : ℕ → ℝ}
    (hu : Tendsto u atTop (𝓝 0))
    (hdiff :
      (fun n : ℕ => u (n + 1) - u n)
        =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3)) :
    u =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  let d : ℕ → ℝ := fun n => u (n + 1) - u n
  rcases hdiff.exists_pos with ⟨C, hCpos, hC⟩
  have hd_summ : Summable d := summable_of_isBigO_inv_cube_p2m2 hdiff
  refine IsBigO.of_bound (2 * C) ?_
  have hCbound := hC.bound
  rw [eventually_atTop] at hCbound
  rcases hCbound with ⟨N, hN⟩
  refine eventually_atTop.mpr ⟨max N 2, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn2
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have htail_eq := eq_neg_tsum_succDiff_p2m2 hu hd_summ n
  have htail_summ : Summable (fun i : ℕ => d (i + n)) :=
    (summable_nat_add_iff n).mpr hd_summ
  have htail_norm_summ : Summable (fun i : ℕ => ‖d (i + n)‖) := by
    rw [summable_norm_iff]
    exact htail_summ
  have hnorm_le := norm_tsum_le_tsum_norm htail_norm_summ
  have hterm_le : ∀ i : ℕ,
      ‖d (i + n)‖ ≤ C * (1 / (((i + n : ℕ)) : ℝ) ^ 3) := by
    intro i
    have hikN : N ≤ i + n := le_trans hnN (by omega)
    have hb := hN (i + n) hikN
    have hnonneg : 0 ≤ (((i + n : ℕ) : ℝ)⁻¹) ^ 3 := by positivity
    have hnorm : ‖(((i + n : ℕ) : ℝ)⁻¹) ^ 3‖ =
        (((i + n : ℕ) : ℝ)⁻¹) ^ 3 := by
      rw [Real.norm_of_nonneg hnonneg]
    calc
      ‖d (i + n)‖ ≤ C * ‖(((i + n : ℕ) : ℝ)⁻¹) ^ 3‖ := hb
      _ = C * (1 / (((i + n : ℕ)) : ℝ) ^ 3) := by
          rw [hnorm, one_div, inv_pow]
  have hmajor_summ : Summable (fun i : ℕ => C * (1 / (((i + n : ℕ)) : ℝ) ^ 3)) := by
    have hbase : Summable (fun i : ℕ => 1 / (((i + n : ℕ)) : ℝ) ^ 3) := by
      have h : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 3) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
      exact (summable_nat_add_iff n).mpr h
    exact hbase.mul_left C
  have htsum_le :
      (∑' i : ℕ, ‖d (i + n)‖) ≤
        ∑' i : ℕ, C * (1 / (((i + n : ℕ)) : ℝ) ^ 3) := by
    exact htail_norm_summ.tsum_le_tsum hterm_le hmajor_summ
  have htail_cube :
      (∑' i : ℕ, 1 / (((i + n : ℕ)) : ℝ) ^ 3) ≤
        2 / (n : ℝ) ^ 2 := by
    have hn_pred : n - 1 + 1 = n := Nat.sub_one_add_one (Nat.ne_of_gt hnpos_nat)
    have h := tail_inv_cube_shift_p2m2 (n - 1)
    have hleft :
        (∑' i : ℕ, 1 / (((i + (n - 1) + 1 : ℕ)) : ℝ) ^ 3) =
          (∑' i : ℕ, 1 / (((i + n : ℕ)) : ℝ) ^ 3) := by
      apply tsum_congr
      intro i
      rw [show i + (n - 1) + 1 = i + n from by omega]
    have hright : 2 / (((n - 1 : ℕ) : ℝ) + 1) ^ 2 = 2 / (n : ℝ) ^ 2 := by
      have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
        exact_mod_cast hn_pred
      rw [hcast]
    rwa [hleft, hright] at h
  have htail_bound :
      (∑' i : ℕ, C * (1 / (((i + n : ℕ)) : ℝ) ^ 3)) ≤
        C * (2 / (n : ℝ) ^ 2) := by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left htail_cube hCpos.le
  have htarget_nonneg : 0 ≤ ((n : ℝ)⁻¹) ^ 2 := by positivity
  have htarget_norm : ‖((n : ℝ)⁻¹) ^ 2‖ = ((n : ℝ)⁻¹) ^ 2 := by
    rw [Real.norm_of_nonneg htarget_nonneg]
  have hpow_rw : 2 * C * ‖((n : ℝ)⁻¹) ^ 2‖ = C * (2 / (n : ℝ) ^ 2) := by
    rw [htarget_norm]
    field_simp [hnpos.ne']
  calc
    ‖u n‖ = ‖∑' i : ℕ, d (i + n)‖ := by
      rw [htail_eq, norm_neg]
    _ ≤ ∑' i : ℕ, ‖d (i + n)‖ := hnorm_le
    _ ≤ ∑' i : ℕ, C * (1 / (((i + n : ℕ)) : ℝ) ^ 3) := htsum_le
    _ ≤ C * (2 / (n : ℝ) ^ 2) := htail_bound
    _ = 2 * C * ‖((n : ℝ)⁻¹) ^ 2‖ := hpow_rw.symm

private lemma tendsto_zero_of_succDiff_isBigO_inv_four
    {u : ℕ → ℝ}
    (hu : Tendsto u atTop (𝓝 0))
    (hdiff :
      (fun n : ℕ => u (n + 1) - u n)
        =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4)) :
    u =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  let d : ℕ → ℝ := fun n => u (n + 1) - u n
  rcases hdiff.exists_pos with ⟨C, hCpos, hC⟩
  have hd_summ : Summable d := summable_of_isBigO_inv_four hdiff
  refine IsBigO.of_bound (2 * C) ?_
  have hCbound := hC.bound
  rw [eventually_atTop] at hCbound
  rcases hCbound with ⟨N, hN⟩
  refine eventually_atTop.mpr ⟨max N 2, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn2
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have htail_eq := eq_neg_tsum_succDiff_p2m2 hu hd_summ n
  have htail_summ : Summable (fun i : ℕ => d (i + n)) :=
    (summable_nat_add_iff n).mpr hd_summ
  have htail_norm_summ : Summable (fun i : ℕ => ‖d (i + n)‖) := by
    rw [summable_norm_iff]
    exact htail_summ
  have hnorm_le := norm_tsum_le_tsum_norm htail_norm_summ
  have hterm_le : ∀ i : ℕ,
      ‖d (i + n)‖ ≤ C * (1 / (((i + n : ℕ)) : ℝ) ^ 4) := by
    intro i
    have hikN : N ≤ i + n := le_trans hnN (by omega)
    have hb := hN (i + n) hikN
    have hnonneg : 0 ≤ (((i + n : ℕ) : ℝ)⁻¹) ^ 4 := by positivity
    have hnorm : ‖(((i + n : ℕ) : ℝ)⁻¹) ^ 4‖ =
        (((i + n : ℕ) : ℝ)⁻¹) ^ 4 := by
      rw [Real.norm_of_nonneg hnonneg]
    calc
      ‖d (i + n)‖ ≤ C * ‖(((i + n : ℕ) : ℝ)⁻¹) ^ 4‖ := hb
      _ = C * (1 / (((i + n : ℕ)) : ℝ) ^ 4) := by
          rw [hnorm, one_div, inv_pow]
  have hmajor_summ : Summable (fun i : ℕ => C * (1 / (((i + n : ℕ)) : ℝ) ^ 4)) := by
    have hbase : Summable (fun i : ℕ => 1 / (((i + n : ℕ)) : ℝ) ^ 4) := by
      have h : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 4) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 4)
      exact (summable_nat_add_iff n).mpr h
    exact hbase.mul_left C
  have htsum_le :
      (∑' i : ℕ, ‖d (i + n)‖) ≤
        ∑' i : ℕ, C * (1 / (((i + n : ℕ)) : ℝ) ^ 4) := by
    exact htail_norm_summ.tsum_le_tsum hterm_le hmajor_summ
  have htail_four :
      (∑' i : ℕ, 1 / (((i + n : ℕ)) : ℝ) ^ 4) ≤
        2 / (n : ℝ) ^ 3 := by
    have hn_pred : n - 1 + 1 = n := Nat.sub_one_add_one (Nat.ne_of_gt hnpos_nat)
    have h := tail_inv_four_shift (n - 1)
    have hleft :
        (∑' i : ℕ, 1 / (((i + (n - 1) + 1 : ℕ)) : ℝ) ^ 4) =
          (∑' i : ℕ, 1 / (((i + n : ℕ)) : ℝ) ^ 4) := by
      apply tsum_congr
      intro i
      rw [show i + (n - 1) + 1 = i + n from by omega]
    have hright : 2 / (((n - 1 : ℕ) : ℝ) + 1) ^ 3 = 2 / (n : ℝ) ^ 3 := by
      have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
        exact_mod_cast hn_pred
      rw [hcast]
    rwa [hleft, hright] at h
  have htail_bound :
      (∑' i : ℕ, C * (1 / (((i + n : ℕ)) : ℝ) ^ 4)) ≤
        C * (2 / (n : ℝ) ^ 3) := by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left htail_four hCpos.le
  have htarget_nonneg : 0 ≤ ((n : ℝ)⁻¹) ^ 3 := by positivity
  have htarget_norm : ‖((n : ℝ)⁻¹) ^ 3‖ = ((n : ℝ)⁻¹) ^ 3 := by
    rw [Real.norm_of_nonneg htarget_nonneg]
  have hpow_rw : 2 * C * ‖((n : ℝ)⁻¹) ^ 3‖ = C * (2 / (n : ℝ) ^ 3) := by
    rw [htarget_norm]
    field_simp [hnpos.ne']
  calc
    ‖u n‖ = ‖∑' i : ℕ, d (i + n)‖ := by
      rw [htail_eq, norm_neg]
    _ ≤ ∑' i : ℕ, ‖d (i + n)‖ := hnorm_le
    _ ≤ ∑' i : ℕ, C * (1 / (((i + n : ℕ)) : ℝ) ^ 4) := htsum_le
    _ ≤ C * (2 / (n : ℝ) ^ 3) := htail_bound
    _ = 2 * C * ‖((n : ℝ)⁻¹) ^ 3‖ := hpow_rw.symm

private lemma inv_sub_inv_succ_sub_inv_sq_isBigO_inv_cube_p2m2 (a : ℝ) :
    (fun n : ℕ =>
      a * ((n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) - ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  refine IsBigO.of_bound ‖a‖ ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn1pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hdiff :
      (n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) - ((n : ℝ)⁻¹) ^ 2 =
        -(1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1))) := by
    field_simp [hnpos.ne', hn1pos.ne']
    norm_num [Nat.cast_add, Nat.cast_one]
  have hden_pos : 0 < (n : ℝ) ^ 2 * ((n : ℝ) + 1) := by positivity
  have habs :
      |(n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) - ((n : ℝ)⁻¹) ^ 2| =
        1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1)) := by
    rw [hdiff, abs_neg, abs_of_nonneg]
    positivity
  have hden_le : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 2 * ((n : ℝ) + 1) := by
    nlinarith [sq_nonneg (n : ℝ), hnpos.le]
  have htail_le :
      1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1)) ≤ 1 / (n : ℝ) ^ 3 := by
    exact one_div_le_one_div_of_le (by positivity : 0 < (n : ℝ) ^ 3) hden_le
  have htarget_nonneg : 0 ≤ ((n : ℝ)⁻¹) ^ 3 := by positivity
  have htarget_norm : ‖((n : ℝ)⁻¹) ^ 3‖ = ((n : ℝ)⁻¹) ^ 3 := by
    rw [Real.norm_of_nonneg htarget_nonneg]
  calc
    ‖a * ((n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) - ((n : ℝ)⁻¹) ^ 2)‖
        = ‖a‖ *
          |(n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) - ((n : ℝ)⁻¹) ^ 2| := by
          rw [norm_mul]
          simp [Real.norm_eq_abs]
    _ = ‖a‖ * (1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1))) := by rw [habs]
    _ ≤ ‖a‖ * (1 / (n : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left htail_le (norm_nonneg a)
    _ = ‖a‖ * ‖((n : ℝ)⁻¹) ^ 3‖ := by
          rw [htarget_norm, one_div, inv_pow]

private lemma inv_sub_inv_succ_sub_inv_sq_add_inv_cube_isBigO_inv_four (a : ℝ) :
    (fun n : ℕ =>
      a * ((n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) -
        ((n : ℝ)⁻¹) ^ 2 + ((n : ℝ)⁻¹) ^ 3))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4) := by
  refine IsBigO.of_bound ‖a‖ ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn1pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hdiff :
      (n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) -
          ((n : ℝ)⁻¹) ^ 2 + ((n : ℝ)⁻¹) ^ 3 =
        1 / ((n : ℝ) ^ 3 * ((n : ℝ) + 1)) := by
    field_simp [hnpos.ne', hn1pos.ne']
    norm_num [Nat.cast_add, Nat.cast_one]
  have hden_pos : 0 < (n : ℝ) ^ 3 * ((n : ℝ) + 1) := by positivity
  have habs :
      |(n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) -
          ((n : ℝ)⁻¹) ^ 2 + ((n : ℝ)⁻¹) ^ 3| =
        1 / ((n : ℝ) ^ 3 * ((n : ℝ) + 1)) := by
    rw [hdiff, abs_of_nonneg]
    positivity
  have hden_le : (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 3 * ((n : ℝ) + 1) := by
    nlinarith [sq_nonneg (n : ℝ), sq_nonneg ((n : ℝ) ^ 2), hnpos.le]
  have htail_le :
      1 / ((n : ℝ) ^ 3 * ((n : ℝ) + 1)) ≤ 1 / (n : ℝ) ^ 4 := by
    exact one_div_le_one_div_of_le (by positivity : 0 < (n : ℝ) ^ 4) hden_le
  have htarget_nonneg : 0 ≤ ((n : ℝ)⁻¹) ^ 4 := by positivity
  have htarget_norm : ‖((n : ℝ)⁻¹) ^ 4‖ = ((n : ℝ)⁻¹) ^ 4 := by
    rw [Real.norm_of_nonneg htarget_nonneg]
  calc
    ‖a * ((n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) -
        ((n : ℝ)⁻¹) ^ 2 + ((n : ℝ)⁻¹) ^ 3)‖
        = ‖a‖ *
          |(n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) -
            ((n : ℝ)⁻¹) ^ 2 + ((n : ℝ)⁻¹) ^ 3| := by
          rw [norm_mul]
          simp [Real.norm_eq_abs]
    _ = ‖a‖ * (1 / ((n : ℝ) ^ 3 * ((n : ℝ) + 1))) := by rw [habs]
    _ ≤ ‖a‖ * (1 / (n : ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_left htail_le (norm_nonneg a)
    _ = ‖a‖ * ‖((n : ℝ)⁻¹) ^ 4‖ := by
          rw [htarget_norm, one_div, inv_pow]

private lemma inv_sq_sub_inv_succ_sq_sub_two_inv_cube_isBigO_inv_four (a : ℝ) :
    (fun n : ℕ =>
      a * (((n : ℝ)⁻¹) ^ 2 - ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 2) -
        2 * ((n : ℝ)⁻¹) ^ 3))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4) := by
  refine IsBigO.of_bound (5 * ‖a‖) ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn1pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hdiff :
      ((n : ℝ)⁻¹) ^ 2 - ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 2) -
          2 * ((n : ℝ)⁻¹) ^ 3 =
        -((3 * (n : ℝ) + 2) / ((n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2)) := by
    field_simp [hnpos.ne', hn1pos.ne']
    norm_num [Nat.cast_add, Nat.cast_one]
    ring_nf
  have hden_pos : 0 < (n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2 := by positivity
  have hnum_nonneg : 0 ≤ 3 * (n : ℝ) + 2 := by positivity
  have habs :
      |((n : ℝ)⁻¹) ^ 2 - ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 2) -
          2 * ((n : ℝ)⁻¹) ^ 3| =
        (3 * (n : ℝ) + 2) / ((n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2) := by
    rw [hdiff, abs_neg, abs_of_nonneg]
    positivity
  have htail_le :
      (3 * (n : ℝ) + 2) / ((n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2) ≤
        5 / (n : ℝ) ^ 4 := by
    rw [div_le_div_iff₀ hden_pos (by positivity : 0 < (n : ℝ) ^ 4)]
    have hbasic :
        (3 * (n : ℝ) + 2) * (n : ℝ) ≤ 5 * ((n : ℝ) + 1) ^ 2 := by
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
    calc
      (3 * (n : ℝ) + 2) * (n : ℝ) ^ 4
          = ((3 * (n : ℝ) + 2) * (n : ℝ)) * (n : ℝ) ^ 3 := by ring
      _ ≤ (5 * ((n : ℝ) + 1) ^ 2) * (n : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_right hbasic (by positivity)
      _ = 5 * ((n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2) := by ring
  have htarget_nonneg : 0 ≤ ((n : ℝ)⁻¹) ^ 4 := by positivity
  have htarget_norm : ‖((n : ℝ)⁻¹) ^ 4‖ = ((n : ℝ)⁻¹) ^ 4 := by
    rw [Real.norm_of_nonneg htarget_nonneg]
  calc
    ‖a * (((n : ℝ)⁻¹) ^ 2 - ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 2) -
        2 * ((n : ℝ)⁻¹) ^ 3)‖
        = ‖a‖ *
          |((n : ℝ)⁻¹) ^ 2 - ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 2) -
            2 * ((n : ℝ)⁻¹) ^ 3| := by
          rw [norm_mul]
          simp [Real.norm_eq_abs]
    _ = ‖a‖ * ((3 * (n : ℝ) + 2) /
          ((n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2)) := by rw [habs]
    _ ≤ ‖a‖ * (5 / (n : ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_left htail_le (norm_nonneg a)
    _ = 5 * ‖a‖ * ‖((n : ℝ)⁻¹) ^ 4‖ := by
          rw [htarget_norm]
          field_simp [hnpos.ne']

private lemma gammaSecondError_succDiff_isBigO_inv_cube_p2m2
    {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => gammaSecondError α (n + 1) - gammaSecondError α n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  set_option backward.isDefEq.respectTransparency false in
    have hY1 := gammaRatioNorm_sub_one_isBigO_inv_p2m2 hα
    have hStep2 := gammaStep_sub_one_isBigO_inv_sq_p2m2 α
    have hStep3 := gammaStep_sub_isBigO_inv_cube_p2m2 α
    have hprod0 := hY1.mul hStep2
    have hprod :
        (fun n : ℕ => (gammaRatioNorm α n - 1) * (gammaStep α n - 1))
          =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
      refine hprod0.congr_right ?_
      intro n
      ring_nf
    have htail := inv_sub_inv_succ_sub_inv_sq_isBigO_inv_cube_p2m2 (c1 α)
    have hsum := (hStep3.add hprod).add htail
    have heq :
        (fun n : ℕ => gammaSecondError α (n + 1) - gammaSecondError α n) =ᶠ[atTop]
          (fun n : ℕ =>
            (gammaStep α n - 1 + c1 α * ((n : ℝ)⁻¹) ^ 2) +
              (gammaRatioNorm α n - 1) * (gammaStep α n - 1) +
              c1 α * ((n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) - ((n : ℝ)⁻¹) ^ 2)) := by
      filter_upwards [gammaRatioNorm_succ_p2m2 hα] with n hrec
      unfold gammaSecondError
      rw [hrec]
      ring_nf
    exact heq.trans_isBigO hsum

private lemma gammaSecondError_tendsto_zero_p2m2
    {α : ℝ} (hα : 0 < α) :
    Tendsto (gammaSecondError α) atTop (𝓝 0) := by
  have hY := gammaRatioNorm_sub_one_isBigO_inv_p2m2 hα
  have hYlim : Tendsto (fun n : ℕ => gammaRatioNorm α n - 1) atTop (𝓝 0) :=
    hY.trans_tendsto (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hcorr :
      Tendsto (fun n : ℕ => c1 α * (n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (c1 α)
  simpa [gammaSecondError] using hYlim.sub hcorr

private theorem gammaRatioNorm_second_order_p2m2
    {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => gammaRatioNorm α n - (1 + c1 α * (n : ℝ)⁻¹))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  have hdiff := gammaSecondError_succDiff_isBigO_inv_cube_p2m2 hα
  have hlim := gammaSecondError_tendsto_zero_p2m2 hα
  have h := tendsto_zero_of_succDiff_isBigO_inv_cube_p2m2 hlim hdiff
  exact h.congr_left fun n => by
    unfold gammaSecondError
    ring_nf

private lemma gammaRatioNorm_second_order_sub_form
    {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => gammaRatioNorm α n - 1 - c1 α * (n : ℝ)⁻¹)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  exact (gammaRatioNorm_second_order_p2m2 hα).congr_left fun n => by ring_nf

private lemma const_mul_inv_isBigO_inv (a : ℝ) :
    (fun n : ℕ => a * (n : ℝ)⁻¹)
      =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  exact (isBigO_refl (fun n : ℕ => (n : ℝ)⁻¹) atTop).const_mul_left a

private lemma gammaThirdError_succDiff_isBigO_inv_four
    {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => gammaThirdError α (n + 1) - gammaThirdError α n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4) := by
  have hStep4 := gammaStep_sub_third_isBigO_inv_four α
  have hStep2 := gammaStep_sub_one_isBigO_inv_sq_p2m2 α
  have hStep3 := gammaStep_sub_isBigO_inv_cube_p2m2 α
  have hY2 := gammaRatioNorm_second_order_sub_form hα
  have hprodY0 := hY2.mul hStep2
  have hprodY :
      (fun n : ℕ =>
        (gammaRatioNorm α n - 1 - c1 α * (n : ℝ)⁻¹) *
          (gammaStep α n - 1))
        =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4) := by
    refine hprodY0.congr_right ?_
    intro n
    ring_nf
  have hcx := const_mul_inv_isBigO_inv (c1 α)
  have hprodC0 := hcx.mul hStep3
  have hprodC :
      (fun n : ℕ =>
        c1 α * (n : ℝ)⁻¹ *
          (gammaStep α n - 1 + c1 α * ((n : ℝ)⁻¹) ^ 2))
        =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4) := by
    refine hprodC0.congr_right ?_
    intro n
    ring_nf
  have htail1 := inv_sub_inv_succ_sub_inv_sq_add_inv_cube_isBigO_inv_four (c1 α)
  have htail2 := inv_sq_sub_inv_succ_sq_sub_two_inv_cube_isBigO_inv_four (c2 α)
  have hsum := (((hStep4.add hprodY).add hprodC).add htail1).add htail2
  have heq :
      (fun n : ℕ => gammaThirdError α (n + 1) - gammaThirdError α n) =ᶠ[atTop]
        (fun n : ℕ =>
          (gammaStep α n -
            (1 - c1 α * ((n : ℝ)⁻¹) ^ 2 +
              d3 α * ((n : ℝ)⁻¹) ^ 3)) +
            (gammaRatioNorm α n - 1 - c1 α * (n : ℝ)⁻¹) *
              (gammaStep α n - 1) +
            c1 α * (n : ℝ)⁻¹ *
              (gammaStep α n - 1 + c1 α * ((n : ℝ)⁻¹) ^ 2) +
            c1 α * ((n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) -
              ((n : ℝ)⁻¹) ^ 2 + ((n : ℝ)⁻¹) ^ 3) +
            c2 α * (((n : ℝ)⁻¹) ^ 2 -
              ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 2) -
              2 * ((n : ℝ)⁻¹) ^ 3)) := by
    filter_upwards [gammaRatioNorm_succ_p2m2 hα] with n hrec
    unfold gammaThirdError
    rw [hrec]
    dsimp [c1, c2, d3]
    ring_nf
  exact heq.trans_isBigO hsum

private lemma gammaThirdError_tendsto_zero
    {α : ℝ} (hα : 0 < α) :
    Tendsto (gammaThirdError α) atTop (𝓝 0) := by
  have hY := gammaRatioNorm_second_order_sub_form hα
  have htarget :
      Tendsto (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
  have hYlim :
      Tendsto (fun n : ℕ => gammaRatioNorm α n - 1 - c1 α * (n : ℝ)⁻¹)
        atTop (𝓝 0) :=
    hY.trans_tendsto htarget
  have hc2 :
      Tendsto (fun n : ℕ => c2 α * ((n : ℝ)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using htarget.const_mul (c2 α)
  change Tendsto
    (fun n : ℕ =>
      gammaRatioNorm α n - 1 - c1 α * (n : ℝ)⁻¹ -
        c2 α * ((n : ℝ)⁻¹) ^ 2) atTop (𝓝 0)
  simpa only [sub_zero] using hYlim.sub hc2

private theorem gammaRatioNorm_third_order
    {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ =>
      gammaRatioNorm α n -
        (1 + c1 α * (n : ℝ)⁻¹ + c2 α * ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  have hdiff := gammaThirdError_succDiff_isBigO_inv_four hα
  have hlim := gammaThirdError_tendsto_zero hα
  have h := tendsto_zero_of_succDiff_isBigO_inv_four hlim hdiff
  exact h.congr_left fun n => by
    unfold gammaThirdError
    ring_nf

theorem gamma_ratio_third_order {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ =>
      Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1) -
        (n : ℝ) ^ (α - 1) *
          (1 + (α * (α - 1) / 2) * (n : ℝ)⁻¹ +
            (α * (α - 1) * (α - 2) * (3 * α - 1) / 24) *
              ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 4)) := by
  have hnorm := gammaRatioNorm_third_order hα
  have hnorm_rpow :
      (fun n : ℕ =>
        gammaRatioNorm α n -
          (1 + c1 α * (n : ℝ)⁻¹ + c2 α * ((n : ℝ)⁻¹) ^ 2))
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(3 : ℝ))) := by
    exact hnorm.congr_right fun n => (rpow_neg_three_eq_inv_cube_nat n).symm
  have hp : (fun n : ℕ => (n : ℝ) ^ (α - 1))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 1)) := isBigO_refl _ _
  have hmul :
      (fun n : ℕ =>
        (n : ℝ) ^ (α - 1) *
          (gammaRatioNorm α n -
            (1 + c1 α * (n : ℝ)⁻¹ + c2 α * ((n : ℝ)⁻¹) ^ 2)))
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 4)) := by
    exact IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
      (a := α - 1) (b := -(3 : ℝ)) (c := α - 4) hp hnorm_rpow (by linarith)
  have heq :
      (fun n : ℕ =>
        Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1) -
          (n : ℝ) ^ (α - 1) *
            (1 + (α * (α - 1) / 2) * (n : ℝ)⁻¹ +
              (α * (α - 1) * (α - 2) * (3 * α - 1) / 24) *
                ((n : ℝ)⁻¹) ^ 2)) =ᶠ[atTop]
        (fun n : ℕ =>
          (n : ℝ) ^ (α - 1) *
            (gammaRatioNorm α n -
              (1 + c1 α * (n : ℝ)⁻¹ + c2 α * ((n : ℝ)⁻¹) ^ 2))) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
    have hpow_ne : (n : ℝ) ^ (α - 1) ≠ 0 := (Real.rpow_pos_of_pos hnpos _).ne'
    unfold gammaRatioNorm c1 c2
    field_simp [hpow_ne]
  exact heq.trans_isBigO hmul

theorem modelCoeff_thirdOrder {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ =>
      Ring.choose (α + n - 1) n -
        ((n : ℝ) ^ (α - 1) / Real.Gamma α) *
          (1 + (α * (α - 1) / 2) * (n : ℝ)⁻¹ +
            (α * (α - 1) * (α - 2) * (3 * α - 1) / 24) *
              ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 4)) := by
  have hΓ : Real.Gamma α ≠ 0 := (Real.Gamma_pos_of_pos hα).ne'
  have h := (gamma_ratio_third_order hα).const_mul_left (Real.Gamma α)⁻¹
  refine h.congr_left ?_
  intro n
  rw [modelCoeff_eq_gamma_ratio hα n]
  field_simp [hΓ]

end
end

section
open scoped BigOperators PowerSeries
open List Finset

noncomputable section

namespace FormalMultilinearSeries

lemma ofScalars_comp_coeff (a b : ℕ → ℂ) (n : ℕ) :
    ((FormalMultilinearSeries.ofScalars ℂ a).comp
      (FormalMultilinearSeries.ofScalars ℂ b)).coeff n =
      ∑ c : Composition n, a c.length * ∏ i : Fin c.length, b (c.blocksFun i) := by
  rw [FormalMultilinearSeries.coeff]
  simp [FormalMultilinearSeries.comp, FormalMultilinearSeries.applyComposition,
    FormalMultilinearSeries.ofScalars, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
    List.prod_ofFn, smul_eq_mul]

end FormalMultilinearSeries

private lemma prod_coeff_eq_zero_of_not_pos {g : ℂ⟦X⟧}
    (hg : PowerSeries.constantCoeff g = 0)
    {d n : ℕ} (l : { l : Fin d → ℕ // ∑ i, l i = n })
    (hl : ¬ ∀ i, 0 < l.1 i) :
    (∏ i : Fin d, PowerSeries.coeff (l.1 i) g) = 0 := by
  classical
  push Not at hl
  rcases hl with ⟨i, hi⟩
  have hzero : l.1 i = 0 := Nat.eq_zero_of_le_zero hi
  rw [Finset.prod_eq_zero_iff]
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rw [hzero]
  simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hg

private lemma coeff_pow_eq_zero_of_constantCoeff_eq_zero
    {g : ℂ⟦X⟧} (hg : PowerSeries.constantCoeff g = 0)
    {n d : ℕ} (hnd : n < d) :
    PowerSeries.coeff n (g ^ d) = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    exact PowerSeries.coeff_of_lt_order n
      (lt_of_lt_of_le (by exact_mod_cast hnd)
        (PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hg))

private lemma coeff_pow_eq_sum_composition_length {g : ℂ⟦X⟧}
    (hg : PowerSeries.constantCoeff g = 0) (d n : ℕ) :
    PowerSeries.coeff n (g ^ d) =
      ∑ c : { c : Composition n // c.length = d },
        ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g := by
  classical
  rw [PowerSeries.coeff_pow]
  let A := (Finset.range d).finsuppAntidiag n
  let B := { l : Fin d → ℕ // ∑ i, l i = n }
  letI : Fintype B := Fintype.ofEquiv A (finsuppAntidiagRangeEquivFin n d)
  let P : B → Prop := fun l => ∀ i, 0 < l.1 i
  let Pos := { l : Fin d → ℕ // (∀ i, 0 < l i) ∧ ∑ i, l i = n }
  letI : Fintype Pos := Fintype.ofEquiv { x : B // P x } (positiveSubtypeEquiv n d)
  have h_antidiag_to_B :
      (∑ l ∈ (Finset.range d).finsuppAntidiag n,
          ∏ i ∈ Finset.range d, PowerSeries.coeff (l i) g) =
        ∑ l : B, ∏ i : Fin d, PowerSeries.coeff (l.1 i) g := by
    calc
      (∑ l ∈ (Finset.range d).finsuppAntidiag n,
          ∏ i ∈ Finset.range d, PowerSeries.coeff (l i) g) =
          ∑ a : A, ∏ i ∈ Finset.range d, PowerSeries.coeff (a.1 i) g := by
        simpa [A] using (Finset.sum_attach A
          (fun a : ℕ →₀ ℕ => ∏ i ∈ Finset.range d, PowerSeries.coeff (a i) g)).symm
      _ = ∑ l : B, ∏ i : Fin d, PowerSeries.coeff (l.1 i) g := by
        exact Fintype.sum_equiv (finsuppAntidiagRangeEquivFin n d)
          (fun a : A => ∏ i ∈ Finset.range d, PowerSeries.coeff (a.1 i) g)
          (fun l : B => ∏ i : Fin d, PowerSeries.coeff (l.1 i) g)
          (by
            intro a
            calc
              (∏ i ∈ Finset.range d, PowerSeries.coeff (a.1 i) g) =
                  ∏ i : Fin d, PowerSeries.coeff (a.1 i.val) g := by
                exact (Fin.prod_univ_eq_prod_range
                  (fun i => PowerSeries.coeff (a.1 i) g) d).symm
              _ = ∏ i : Fin d,
                    PowerSeries.coeff (((finsuppAntidiagRangeEquivFin n d) a).1 i) g := by
                simp [finsuppAntidiagRangeEquivFin])
  rw [h_antidiag_to_B]
  have h_filter :
      (∑ l : B, ∏ i : Fin d, PowerSeries.coeff (l.1 i) g) =
        ∑ l : { x : B // P x },
          ∏ i : Fin d, PowerSeries.coeff (l.1.1 i) g := by
    have hsubset : (Finset.univ.filter P) ⊆ (Finset.univ : Finset B) := by
      intro x _hx
      simp
    have hsum_subset :
        ∑ x ∈ (Finset.univ.filter P), (∏ i : Fin d, PowerSeries.coeff (x.1 i) g) =
          ∑ x : B, ∏ i : Fin d, PowerSeries.coeff (x.1 i) g := by
      refine Finset.sum_subset hsubset ?_
      intro x _hx hxnot
      exact prod_coeff_eq_zero_of_not_pos hg x (by simpa [P] using hxnot)
    calc
      (∑ l : B, ∏ i : Fin d, PowerSeries.coeff (l.1 i) g) =
          ∑ x ∈ (Finset.univ.filter P), (∏ i : Fin d, PowerSeries.coeff (x.1 i) g) :=
        hsum_subset.symm
      _ = ∑ l : { x : B // P x },
          ∏ i : Fin d, PowerSeries.coeff (l.1.1 i) g := by
        refine Finset.sum_subtype (Finset.univ.filter P) ?_
          (fun x : B => ∏ i : Fin d, PowerSeries.coeff (x.1 i) g)
        intro x
        simp [P]
  rw [h_filter]
  calc
    (∑ l : { x : B // P x },
        ∏ i : Fin d, PowerSeries.coeff (l.1.1 i) g) =
      ∑ l : Pos,
        ∏ i : Fin d, PowerSeries.coeff (l.1 i) g := by
      exact Fintype.sum_equiv (positiveSubtypeEquiv n d)
        (fun l : { x : B // P x } =>
          ∏ i : Fin d, PowerSeries.coeff (l.1.1 i) g)
        (fun l : Pos =>
          ∏ i : Fin d, PowerSeries.coeff (l.1 i) g)
        (by intro l; rfl)
    _ = ∑ c : { c : Composition n // c.length = d },
        ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g := by
      exact Fintype.sum_equiv (positiveFinTupleCompositionEquiv n d)
        (fun l : Pos =>
          ∏ i : Fin d, PowerSeries.coeff (l.1 i) g)
        (fun c : { c : Composition n // c.length = d } =>
          ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g)
        (by
          intro l
          change (∏ i : Fin d, PowerSeries.coeff (l.1 i) g) =
            ∏ i : Fin (List.ofFn l.1).length,
              PowerSeries.coeff ((List.ofFn l.1).get i) g
          exact Fintype.prod_equiv (finCongr (by simp [List.length_ofFn]))
            (fun i : Fin d => PowerSeries.coeff (l.1 i) g)
            (fun i : Fin (List.ofFn l.1).length =>
              PowerSeries.coeff ((List.ofFn l.1).get i) g)
            (by intro i; simp))

private lemma subst_coeff_eq_sum_composition {f g : ℂ⟦X⟧}
    (hg : PowerSeries.constantCoeff g = 0) (n : ℕ) :
    PowerSeries.coeff n (f.subst g) =
      ∑ c : Composition n,
        PowerSeries.coeff c.length f *
          ∏ i : Fin c.length, PowerSeries.coeff (c.blocksFun i) g := by
  classical
  have hsubst := PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero' hg) f n
  rw [hsubst]
  simp only [smul_eq_mul]
  let term : ℕ → ℂ := fun d => PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d)
  have hsupport : Function.support term ⊆ (Finset.range (n + 1) : Set ℕ) := by
    intro d hd
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra hmem
    have hnd : n < d := by omega
    have hz : PowerSeries.coeff n (g ^ d) = 0 :=
      coeff_pow_eq_zero_of_constantCoeff_eq_zero hg hnd
    have hdne : term d ≠ 0 := hd
    simp [term, hz] at hdne
  calc
    (∑ᶠ d : ℕ, PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d)) =
        ∑ d ∈ Finset.range (n + 1), PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d) := by
      simpa [term] using finsum_eq_sum_of_support_subset term hsupport
    _ = ∑ d ∈ Finset.range (n + 1),
        ∑ c : { c : Composition n // c.length = d },
          PowerSeries.coeff d f *
            ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g := by
      refine Finset.sum_congr rfl ?_
      intro d _hd
      rw [coeff_pow_eq_sum_composition_length hg d n]
      simp [Finset.mul_sum]
    _ = ∑ c : Composition n,
        PowerSeries.coeff c.length f *
          ∏ i : Fin c.length, PowerSeries.coeff (c.blocksFun i) g := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun d => ∑ c : { c : Composition n // c.length = d },
          PowerSeries.coeff d f *
            ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g) (n + 1)]
      rw [← Fintype.sum_sigma (fun x : Sigma (fun d : Fin (n + 1) =>
          { c : Composition n // c.length = d.val }) =>
        PowerSeries.coeff x.1.val f *
          ∏ i : Fin x.2.1.length, PowerSeries.coeff (x.2.1.blocksFun i) g)]
      exact Fintype.sum_equiv (sigmaLengthCompositionEquiv n)
        (fun x : Sigma (fun d : Fin (n + 1) =>
          { c : Composition n // c.length = d.val }) =>
          PowerSeries.coeff x.1.val f *
            ∏ i : Fin x.2.1.length, PowerSeries.coeff (x.2.1.blocksFun i) g)
        (fun c : Composition n =>
          PowerSeries.coeff c.length f *
            ∏ i : Fin c.length, PowerSeries.coeff (c.blocksFun i) g)
        (by
          intro x
          rcases x with ⟨d, c, hc⟩
          dsimp [sigmaLengthCompositionEquiv]
          apply congrArg₂ HMul.hMul
          · exact congrArg (fun k => PowerSeries.coeff k f) hc.symm
          · rfl)

namespace PowerSeries

theorem toFMLS_subst_eq_comp {f g : PowerSeries ℂ}
    (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.toFMLS (f.subst g) =
      (PowerSeries.toFMLS f).comp (PowerSeries.toFMLS g) := by
  ext n
  simp [PowerSeries.coeff_toFMLS]
  change PowerSeries.coeff n (f.subst g) =
    ((FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n f)).comp
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n g))).coeff n
  rw [FormalMultilinearSeries.ofScalars_comp_coeff]
  exact subst_coeff_eq_sum_composition hg n

end PowerSeries
end
end

section
/-!
# Second-order two-term transfer

This file assembles the two-term transfer theorem from the committed model
coefficient estimates and the all-real little-o coefficient descent.
-/

set_option maxHeartbeats 1200000

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

private lemma coeff_sub_two_const_smul (C0 C1 : ℂ)
    (p q0 q1 : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    (p - C0 • q0 - C1 • q1).coeff n =
      p.coeff n - C0 * q0.coeff n - C1 * q1.coeff n := by
  rw [coeff_sub_const_smul, coeff_sub_const_smul]

private lemma rpow_sub_one_isLittleO (a : ℝ) :
    (fun n : ℕ => (n : ℝ) ^ (a - 1)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ a) := by
  refine IsLittleO.of_bound ?_
  intro c hc
  have hsmall : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ < c :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (Iio_mem_nhds hc)
  filter_upwards [eventually_ge_atTop 1, hsmall] with n hn hninvc
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  have hpowpos : 0 < (n : ℝ) ^ a := Real.rpow_pos_of_pos hnpos a
  have hleft_nonneg : 0 ≤ (n : ℝ) ^ (a - 1) := Real.rpow_nonneg (le_of_lt hnpos) _
  have hright_nonneg : 0 ≤ (n : ℝ) ^ a := le_of_lt hpowpos
  have hpow_eq : (n : ℝ) ^ (a - 1) = (n : ℝ) ^ a * (n : ℝ)⁻¹ := by
    calc
      (n : ℝ) ^ (a - 1) = (n : ℝ) ^ (a + (-(1 : ℝ))) := by ring_nf
      _ = (n : ℝ) ^ a * (n : ℝ) ^ (-(1 : ℝ)) := by rw [Real.rpow_add hnpos]
      _ = (n : ℝ) ^ a * (n : ℝ)⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hnpos), Real.rpow_one]
  calc
    ‖(n : ℝ) ^ (a - 1)‖ = (n : ℝ) ^ (a - 1) := Real.norm_of_nonneg hleft_nonneg
    _ = (n : ℝ) ^ a * (n : ℝ)⁻¹ := hpow_eq
    _ ≤ (n : ℝ) ^ a * c :=
      mul_le_mul_of_nonneg_left (le_of_lt hninvc) (le_of_lt hpowpos)
    _ = c * ‖(n : ℝ) ^ a‖ := by
      rw [Real.norm_of_nonneg hright_nonneg]
      ring

private lemma model0_expand_real {α : ℝ} (hα : 1 < α) {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) ^ (α - 1) / Real.Gamma α) *
        (1 + α * (α - 1) / (2 * (n : ℝ))) =
      (n : ℝ) ^ (α - 1) / Real.Gamma α +
        (α * (α - 1) / 2 / Real.Gamma α) * (n : ℝ) ^ (α - 2) := by
  have hΓ : Real.Gamma α ≠ 0 := (Real.Gamma_pos_of_pos (by linarith : 0 < α)).ne'
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
  have hpow : (n : ℝ) ^ (α - 2) = (n : ℝ) ^ (α - 1) * (n : ℝ)⁻¹ := by
    calc
      (n : ℝ) ^ (α - 2) = (n : ℝ) ^ ((α - 1) + (-(1 : ℝ))) := by ring_nf
      _ = (n : ℝ) ^ (α - 1) * (n : ℝ) ^ (-(1 : ℝ)) := by rw [Real.rpow_add hnpos]
      _ = (n : ℝ) ^ (α - 1) * (n : ℝ)⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hnpos), Real.rpow_one]
  rw [hpow]
  field_simp [hΓ, hnne]

private lemma model0_expand_eventually {α : ℝ} (hα : 1 < α) :
    (fun n : ℕ =>
      ((n : ℝ) ^ (α - 1) / Real.Gamma α) *
        (1 + α * (α - 1) / (2 * (n : ℝ))))
      =ᶠ[atTop]
    (fun n : ℕ =>
      (n : ℝ) ^ (α - 1) / Real.Gamma α +
        (α * (α - 1) / 2 / Real.Gamma α) * (n : ℝ) ^ (α - 2)) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact model0_expand_real hα hn

private lemma modelCoeff_secondOrder_littleO {α : ℝ} (hα : 1 < α) :
    (fun n : ℕ =>
      Ring.choose (α + n - 1) n -
        ((n : ℝ) ^ (α - 1) / Real.Gamma α +
          (α * (α - 1) / 2 / Real.Gamma α) * (n : ℝ) ^ (α - 2)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
  have hcompact :
      (fun n : ℕ =>
        Ring.choose (α + n - 1) n -
          ((n : ℝ) ^ (α - 1) / Real.Gamma α) *
            (1 + α * (α - 1) / (2 * (n : ℝ))))
        =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
    have hO := modelCoeff_secondOrder (α := α) (by linarith : 0 < α)
    have ho : (fun n : ℕ => (n : ℝ) ^ (α - 3)) =o[atTop]
        (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
      convert rpow_sub_one_isLittleO (α - 2) using 1
      ext n
      congr 1
      ring
    exact hO.trans_isLittleO ho
  have hEq :
      (fun n : ℕ =>
        Ring.choose (α + n - 1) n -
          ((n : ℝ) ^ (α - 1) / Real.Gamma α +
            (α * (α - 1) / 2 / Real.Gamma α) * (n : ℝ) ^ (α - 2)))
        =ᶠ[atTop]
      (fun n : ℕ =>
        Ring.choose (α + n - 1) n -
          ((n : ℝ) ^ (α - 1) / Real.Gamma α) *
            (1 + α * (α - 1) / (2 * (n : ℝ)))) := by
    filter_upwards [model0_expand_eventually hα] with n hn
    rw [hn]
  exact hEq.trans_isLittleO hcompact

private lemma modelCoeff_leading_sub_littleO {α : ℝ} (hα : 1 < α) :
    (fun n : ℕ =>
      Ring.choose ((α - 1) + n - 1) n -
        (n : ℝ) ^ (α - 2) / Real.Gamma (α - 1))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
  have hO := modelCoeff_explicit (α := α - 1) (by linarith : 0 < α - 1)
  have ho : (fun n : ℕ => (n : ℝ) ^ (α - 1 - 2)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
    convert rpow_sub_one_isLittleO (α - 2) using 1
    ext n
    congr 1
    ring
  convert hO.trans_isLittleO ho using 1
  · ext n
    congr 2
    ring_nf

private lemma ofReal_isLittleO {u v : ℕ → ℝ}
    (h : u =o[atTop] v) :
    (fun n : ℕ => ((u n : ℝ) : ℂ)) =o[atTop] v := by
  exact Asymptotics.IsLittleO.of_norm_left (by
    simpa [Complex.norm_real] using h.norm_left)

/--
Second-order two-term transfer for a real exponent `α > 1`.

The `C0` model contributes the displayed correction
`C0 * (α*(α-1)/2/Γ(α)) * n^(α-2)`, so the `n^(α-2)` coefficient is the sum of
that correction and the leading contribution from the `C1` model.
-/
theorem transfer_twoTerm_secondOrder
    {α : ℝ} {C0 C1 : ℂ} {R φ : ℝ} {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hα : 1 < α) (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ =>
        ‖f z - C0 * (1 - z) ^ (-(α : ℂ)) -
            C1 * (1 - z) ^ (-(((α - 1 : ℝ) : ℂ)))‖ *
          ‖(1 : ℂ) - z‖ ^ (α - 1))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ =>
      p.coeff n -
        (C0 *
            ((((n : ℝ) ^ (α - 1) / Real.Gamma α : ℝ) : ℂ) +
              (((α * (α - 1) / 2 / Real.Gamma α) *
                  (n : ℝ) ^ (α - 2) : ℝ) : ℂ)) +
          C1 * (((n : ℝ) ^ (α - 2) / Real.Gamma (α - 1) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
  let h0 : ℂ → ℂ := fun z => (1 - z) ^ (-(α : ℂ))
  let h1 : ℂ → ℂ := fun z => (1 - z) ^ (-(((α - 1 : ℝ) : ℂ)))
  let q0 : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ
      (fun n : ℕ => Ring.choose ((α : ℂ) + n - 1) n)
  let q1 : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ
      (fun n : ℕ => Ring.choose (((α - 1 : ℝ) : ℂ) + n - 1) n)
  let a0 : ℕ → ℂ := fun n =>
    (((n : ℝ) ^ (α - 1) / Real.Gamma α : ℝ) : ℂ) +
      (((α * (α - 1) / 2 / Real.Gamma α) * (n : ℝ) ^ (α - 2) : ℝ) : ℂ)
  let a1 : ℕ → ℂ := fun n =>
    (((n : ℝ) ^ (α - 2) / Real.Gamma (α - 1) : ℝ) : ℂ)
  have hφπ : φ < Real.pi := by linarith [hφ2, Real.pi_pos]
  have hp0 : HasFPowerSeriesAt h0 q0 0 := by
    have hraw := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (α : ℂ)).hasFPowerSeriesAt
    convert hraw using 1
    ext z
    dsimp [h0]
    rw [Complex.cpow_neg, inv_eq_one_div]
  have hp1 : HasFPowerSeriesAt h1 q1 0 := by
    have hraw :=
      (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (((α - 1 : ℝ) : ℂ))).hasFPowerSeriesAt
    convert hraw using 1
    ext z
    dsimp [h1]
    rw [Complex.cpow_neg, inv_eq_one_div]
  have hΔ0 : AnalyticOnNhd ℂ h0 (DeltaDomainArg R φ) := by
    simpa [h0] using
      (analyticOnNhd_one_sub_cpow_deltaDomain
        (α := (α : ℂ)) (R := R) (φ := φ) hφ0 hφπ)
  have hΔ1 : AnalyticOnNhd ℂ h1 (DeltaDomainArg R φ) := by
    simpa [h1] using
      (analyticOnNhd_one_sub_cpow_deltaDomain
        (α := (((α - 1 : ℝ) : ℂ))) (R := R) (φ := φ) hφ0 hφπ)
  have hpR : HasFPowerSeriesAt
      (fun z : ℂ => f z - C0 • h0 z - C1 • h1 z)
      (p - C0 • q0 - C1 • q1) 0 :=
    (hp.sub (hp0.const_smul (c := C0))).sub (hp1.const_smul (c := C1))
  have hΔR : AnalyticOnNhd ℂ
      (fun z : ℂ => f z - C0 • h0 z - C1 • h1 z)
      (DeltaDomainArg R φ) :=
    (hΔ.sub (hΔ0.const_smul (c := C0))).sub (hΔ1.const_smul (c := C1))
  have hres_norm : (fun n : ℕ => ‖(p - C0 • q0 - C1 • q1).coeff n‖)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
    convert coeff_norm_isLittleO_atTop_of_delta_littleO
      (R := R) (φ := φ) (β := α - 1)
      (f := fun z : ℂ => f z - C0 • h0 z - C1 • h1 z)
      (p := p - C0 • q0 - C1 • q1)
      hR hφ0 hφ2 hpR hΔR ?_ using 1
    · ext n
      congr 1
      ring
    · simpa [h0, h1, smul_eq_mul] using hsing
  have hres : (fun n : ℕ => (p - C0 • q0 - C1 • q1).coeff n)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) :=
    Asymptotics.IsLittleO.of_norm_left hres_norm
  have h0real := modelCoeff_secondOrder_littleO hα
  have h0c :
      (fun n : ℕ =>
        ((Ring.choose (α + n - 1) n -
          ((n : ℝ) ^ (α - 1) / Real.Gamma α +
            (α * (α - 1) / 2 / Real.Gamma α) * (n : ℝ) ^ (α - 2)) : ℝ) : ℂ))
        =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) :=
    ofReal_isLittleO h0real
  have h0term : (fun n : ℕ => C0 * q0.coeff n - C0 * a0 n)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
    have h := h0c.const_mul_left C0
    have hEq : (fun n : ℕ => C0 * q0.coeff n - C0 * a0 n) =ᶠ[atTop]
        (fun n : ℕ =>
          C0 * ((Ring.choose (α + n - 1) n -
            ((n : ℝ) ^ (α - 1) / Real.Gamma α +
              (α * (α - 1) / 2 / Real.Gamma α) * (n : ℝ) ^ (α - 2)) : ℝ) : ℂ)) := by
      refine Eventually.of_forall fun n => ?_
      dsimp [q0, a0]
      rw [FormalMultilinearSeries.coeff_ofScalars, choose_ofReal_model]
      rw [← Complex.ofReal_add, Complex.ofReal_sub]
      ring
    exact hEq.trans_isLittleO h
  have h1real := modelCoeff_leading_sub_littleO hα
  have h1c :
      (fun n : ℕ =>
        ((Ring.choose ((α - 1) + n - 1) n -
          (n : ℝ) ^ (α - 2) / Real.Gamma (α - 1) : ℝ) : ℂ))
        =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) :=
    ofReal_isLittleO h1real
  have h1term : (fun n : ℕ => C1 * q1.coeff n - C1 * a1 n)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
    have h := h1c.const_mul_left C1
    have hEq : (fun n : ℕ => C1 * q1.coeff n - C1 * a1 n) =ᶠ[atTop]
        (fun n : ℕ =>
          C1 * ((Ring.choose ((α - 1) + n - 1) n -
            (n : ℝ) ^ (α - 2) / Real.Gamma (α - 1) : ℝ) : ℂ)) := by
      refine Eventually.of_forall fun n => ?_
      dsimp [q1, a1]
      rw [FormalMultilinearSeries.coeff_ofScalars, choose_ofReal_model]
      rw [Complex.ofReal_sub]
      ring
    exact hEq.trans_isLittleO h
  have hsum : (fun n : ℕ =>
      (C0 * q0.coeff n - C0 * a0 n) +
        (C1 * q1.coeff n - C1 * a1 n) +
        (p - C0 • q0 - C1 • q1).coeff n)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) :=
    (h0term.add h1term).add hres
  have hEq : (fun n : ℕ =>
      p.coeff n -
        (C0 *
            ((((n : ℝ) ^ (α - 1) / Real.Gamma α : ℝ) : ℂ) +
              (((α * (α - 1) / 2 / Real.Gamma α) *
                  (n : ℝ) ^ (α - 2) : ℝ) : ℂ)) +
          C1 * (((n : ℝ) ^ (α - 2) / Real.Gamma (α - 1) : ℝ) : ℂ)))
      =ᶠ[atTop]
    (fun n : ℕ =>
      (C0 * q0.coeff n - C0 * a0 n) +
        (C1 * q1.coeff n - C1 * a1 n) +
        (p - C0 • q0 - C1 • q1).coeff n) := by
    refine Eventually.of_forall fun n => ?_
    dsimp [a0, a1]
    rw [coeff_sub_two_const_smul]
    ring
  exact hEq.trans_isLittleO hsum

end
end

section
/-!
# General second-order transfer

This file extends the second-order two-term transfer theorem to real exponents
away from the poles `1, 0, -1, ...`.  The proof follows the k-fold derivative
descent used by the all-real little-o transfer theorem.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

private lemma ofReal_isLittleO_p2m2 {u v : ℕ → ℝ}
    (h : u =o[atTop] v) :
    (fun n : ℕ => ((u n : ℝ) : ℂ)) =o[atTop] v := by
  exact Asymptotics.IsLittleO.of_norm_left (by
    simpa [Complex.norm_real] using h.norm_left)

private lemma one_sub_rpow_sub_linear_isLittleO (a : ℝ) :
    (fun x : ℝ => (1 - x) ^ a - 1 + a * x) =o[𝓝 0]
      (fun x : ℝ => x) := by
  have hlin : HasDerivAt (fun x : ℝ => 1 - x) (-1) 0 := by
    simpa using
      (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (0 : ℝ))
  have hpow : HasDerivAt (fun x : ℝ => (1 - x) ^ a) (-a) 0 := by
    have h := hlin.rpow_const (p := a)
      (Or.inl (by norm_num : (1 : ℝ) - 0 ≠ 0))
    simpa using h
  have ho := hpow.isLittleO
  simpa [mul_comm, mul_left_comm, mul_assoc] using ho

private lemma rpow_mul_inv_eventually (a : ℝ) :
    (fun n : ℕ => (n : ℝ) ^ (a - 1) * (n : ℝ)⁻¹) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (a - 2)) := by
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  calc
    (n : ℝ) ^ (a - 1) * (n : ℝ)⁻¹
        = (n : ℝ) ^ (a - 1) * (n : ℝ) ^ (-(1 : ℝ)) := by
            rw [Real.rpow_neg hnpos.le, Real.rpow_one]
    _ = (n : ℝ) ^ ((a - 1) + (-(1 : ℝ))) := by
            rw [← Real.rpow_add hnpos]
    _ = (n : ℝ) ^ (a - 2) := by ring_nf

private lemma shifted_rpow_div_first (a : ℝ) :
    (fun n : ℕ =>
      ((n - 1 : ℕ) : ℝ) ^ a / (n : ℝ) - (n : ℝ) ^ (a - 1) +
        a * (n : ℝ) ^ (a - 2))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (a - 2)) := by
  let H : ℝ → ℝ := fun x => (1 - x) ^ a - 1 + a * x
  have hH : H =o[𝓝 0] (fun x : ℝ => x) := by
    simpa [H] using one_sub_rpow_sub_linear_isLittleO a
  have hHinv : (fun n : ℕ => H ((n : ℝ)⁻¹)) =o[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
    simpa using hH.comp_tendsto (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hprod :=
    (isBigO_refl (fun n : ℕ => (n : ℝ) ^ (a - 1)) atTop).mul_isLittleO hHinv
  have hprod' : (fun n : ℕ => (n : ℝ) ^ (a - 1) * H ((n : ℝ)⁻¹))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (a - 2)) := by
    exact hprod.trans_eventuallyEq (rpow_mul_inv_eventually a)
  have heq : (fun n : ℕ =>
      ((n - 1 : ℕ) : ℝ) ^ a / (n : ℝ) - (n : ℝ) ^ (a - 1) +
        a * (n : ℝ) ^ (a - 2)) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (a - 1) * H ((n : ℝ)⁻¹)) := by
    refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    let x : ℝ := n
    have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn
    have hnpos : 0 < x := by dsimp [x]; exact_mod_cast hnpos_nat
    have hn1 : (1 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast hn
    have hcast_sub : ((n - 1 : ℕ) : ℝ) = x - 1 := by
      dsimp [x]
      norm_num [Nat.cast_sub hn]
    have hy_nonneg : 0 ≤ 1 - x⁻¹ := by
      have hinv_le : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
      linarith
    have hmulbase : x * (1 - x⁻¹) = x - 1 := by
      field_simp [hnpos.ne']
    have hpowsub : ((n - 1 : ℕ) : ℝ) ^ a =
        x ^ a * (1 - x⁻¹) ^ a := by
      rw [hcast_sub, ← hmulbase]
      exact Real.mul_rpow hnpos.le hy_nonneg
    have hdivpow : ((n - 1 : ℕ) : ℝ) ^ a / x =
        x ^ (a - 1) * (1 - x⁻¹) ^ a := by
      rw [hpowsub]
      have hxpow : x ^ a / x = x ^ (a - 1) := by
        calc
          x ^ a / x = x ^ a * x⁻¹ := by rw [div_eq_mul_inv]
          _ = x ^ a * x ^ (-(1 : ℝ)) := by
                rw [Real.rpow_neg hnpos.le, Real.rpow_one]
          _ = x ^ (a + (-(1 : ℝ))) := by rw [← Real.rpow_add hnpos]
          _ = x ^ (a - 1) := by ring_nf
      rw [show x ^ a * (1 - x⁻¹) ^ a / x =
          (x ^ a / x) * (1 - x⁻¹) ^ a by ring]
      rw [hxpow]
    have hpowinv : x ^ (a - 1) * x⁻¹ = x ^ (a - 2) := by
      calc
        x ^ (a - 1) * x⁻¹ =
            x ^ (a - 1) * x ^ (-(1 : ℝ)) := by
              rw [Real.rpow_neg hnpos.le, Real.rpow_one]
        _ = x ^ ((a - 1) + (-(1 : ℝ))) := by rw [← Real.rpow_add hnpos]
        _ = x ^ (a - 2) := by ring_nf
    dsimp [H]
    change ((n - 1 : ℕ) : ℝ) ^ a / x - x ^ (a - 1) + a * x ^ (a - 2) =
      x ^ (a - 1) * ((1 - x⁻¹) ^ a - 1 + a * x⁻¹)
    rw [hdivpow, ← hpowinv]
    ring
  exact heq.trans_isLittleO hprod'

private lemma one_sub_inv_rpow_sub_one_isLittleO (a : ℝ) :
    (fun n : ℕ => (1 - (n : ℝ)⁻¹) ^ (a - 1) - 1) =o[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
    tendsto_const_nhds
  have hbase : Tendsto (fun n : ℕ => 1 - (n : ℝ)⁻¹) atTop
      (𝓝 (1 : ℝ)) := by
    simpa using hconst.sub hinv
  have hpow_raw : Tendsto (fun n : ℕ => (1 - (n : ℝ)⁻¹) ^ (a - 1)) atTop
      (𝓝 ((1 : ℝ) ^ (a - 1))) :=
    hbase.rpow tendsto_const_nhds (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  have hpow : Tendsto (fun n : ℕ => (1 - (n : ℝ)⁻¹) ^ (a - 1)) atTop
      (𝓝 (1 : ℝ)) := by
    simpa using hpow_raw
  have hzero : Tendsto
      (fun n : ℕ => (1 - (n : ℝ)⁻¹) ^ (a - 1) - 1) atTop (𝓝 0) := by
    simpa using hpow.sub hconst
  exact (isLittleO_one_iff ℝ).mpr hzero

private lemma shifted_rpow_div_second (a : ℝ) :
    (fun n : ℕ =>
      ((n - 1 : ℕ) : ℝ) ^ (a - 1) / (n : ℝ) - (n : ℝ) ^ (a - 2))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (a - 2)) := by
  let K : ℕ → ℝ := fun n => (1 - (n : ℝ)⁻¹) ^ (a - 1) - 1
  have hK : K =o[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    simpa [K] using one_sub_inv_rpow_sub_one_isLittleO a
  have hprod :=
    (isBigO_refl (fun n : ℕ => (n : ℝ) ^ (a - 2)) atTop).mul_isLittleO hK
  have hprod' : (fun n : ℕ => (n : ℝ) ^ (a - 2) * K n)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (a - 2)) := by
    refine hprod.congr' (EventuallyEq.refl _ _) ?_
    refine eventually_atTop.mpr ⟨0, fun n _ => ?_⟩
    simp
  have heq : (fun n : ℕ =>
      ((n - 1 : ℕ) : ℝ) ^ (a - 1) / (n : ℝ) - (n : ℝ) ^ (a - 2))
      =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (a - 2) * K n) := by
    refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    let x : ℝ := n
    have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn
    have hnpos : 0 < x := by dsimp [x]; exact_mod_cast hnpos_nat
    have hn1 : (1 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast hn
    have hcast_sub : ((n - 1 : ℕ) : ℝ) = x - 1 := by
      dsimp [x]
      norm_num [Nat.cast_sub hn]
    have hy_nonneg : 0 ≤ 1 - x⁻¹ := by
      have hinv_le : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
      linarith
    have hmulbase : x * (1 - x⁻¹) = x - 1 := by
      field_simp [hnpos.ne']
    have hpowsub : ((n - 1 : ℕ) : ℝ) ^ (a - 1) =
        x ^ (a - 1) * (1 - x⁻¹) ^ (a - 1) := by
      rw [hcast_sub, ← hmulbase]
      exact Real.mul_rpow hnpos.le hy_nonneg
    have hdivpow : ((n - 1 : ℕ) : ℝ) ^ (a - 1) / x =
        x ^ (a - 2) * (1 - x⁻¹) ^ (a - 1) := by
      rw [hpowsub]
      have hxpow : x ^ (a - 1) / x = x ^ (a - 2) := by
        calc
          x ^ (a - 1) / x = x ^ (a - 1) * x⁻¹ := by rw [div_eq_mul_inv]
          _ = x ^ (a - 1) * x ^ (-(1 : ℝ)) := by
                rw [Real.rpow_neg hnpos.le, Real.rpow_one]
          _ = x ^ ((a - 1) + (-(1 : ℝ))) := by rw [← Real.rpow_add hnpos]
          _ = x ^ (a - 2) := by ring_nf
      rw [show x ^ (a - 1) * (1 - x⁻¹) ^ (a - 1) / x =
          (x ^ (a - 1) / x) * (1 - x⁻¹) ^ (a - 1) by ring]
      rw [hxpow]
    dsimp [K]
    change ((n - 1 : ℕ) : ℝ) ^ (a - 1) / x - x ^ (a - 2) =
      x ^ (a - 2) * ((1 - x⁻¹) ^ (a - 1) - 1)
    rw [hdivpow]
    ring
  exact heq.trans_isLittleO hprod'

private lemma complex_inv_natCast_isBigO :
    (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : ℂ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards with n
  have htarget : (n : ℝ) ^ (-(1 : ℝ)) = (n : ℝ)⁻¹ := by
    rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_one]
  rw [htarget]
  simp

private lemma rpow_neg_one_mul_eventually (a : ℝ) :
    (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ)) * (n : ℝ) ^ (a - 1)) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (a - 2)) := by
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  calc
    (n : ℝ) ^ (-(1 : ℝ)) * (n : ℝ) ^ (a - 1)
        = (n : ℝ) ^ ((-(1 : ℝ)) + (a - 1)) := by
            rw [← Real.rpow_add hnpos]
    _ = (n : ℝ) ^ (a - 2) := by ring_nf

private lemma coeff_of_scalarDerivSeries_pred
    (p : FormalMultilinearSeries ℂ ℂ ℂ) {n : ℕ} (hn : 1 ≤ n) :
    p.coeff n = (((n : ℝ)⁻¹ : ℝ) : ℂ) * (scalarDerivSeries p).coeff (n - 1) := by
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos_nat)
  have hcoeff : (scalarDerivSeries p).coeff (n - 1) = (n : ℂ) * p.coeff n := by
    rw [scalarDerivSeries_coeff]
    have hnat : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have hcast : ((n - 1 : ℕ) : ℂ) + 1 = (n : ℂ) := by
      norm_num [Nat.cast_sub hn]
    rw [hnat, hcast]
  rw [hcoeff]
  have hinv : (((n : ℝ)⁻¹ : ℝ) : ℂ) = (n : ℂ)⁻¹ := by
    norm_num [Complex.ofReal_inv]
  rw [hinv]
  field_simp [hnC]

lemma secondOrder_of_deriv_secondOrder
    {α : ℝ} {A B : ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hderiv :
      (fun m : ℕ =>
        (scalarDerivSeries p).coeff m -
          (A * (((m : ℝ) ^ α : ℝ) : ℂ) +
            B * (((m : ℝ) ^ (α - 1) : ℝ) : ℂ)))
        =o[atTop] (fun m : ℕ => (m : ℝ) ^ (α - 1))) :
    (fun n : ℕ =>
      p.coeff n -
        (A * (((n : ℝ) ^ (α - 1) : ℝ) : ℂ) +
          (B - (α : ℂ) * A) * (((n : ℝ) ^ (α - 2) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
  let err : ℕ → ℂ := fun m =>
    (scalarDerivSeries p).coeff m -
      (A * (((m : ℝ) ^ α : ℝ) : ℂ) +
        B * (((m : ℝ) ^ (α - 1) : ℝ) : ℂ))
  have herr_sub : (fun n : ℕ => err (n - 1)) =o[atTop]
      (fun n : ℕ => ((n - 1 : ℕ) : ℝ) ^ (α - 1)) := by
    simpa [err, Function.comp_apply] using
      hderiv.comp_tendsto (Filter.tendsto_sub_atTop_nat 1)
  have herr_n : (fun n : ℕ => err (n - 1)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ (α - 1)) :=
    herr_sub.trans_isBigO (nat_sub_const_rpow_isBigO 1 (α - 1))
  have hinv_err_raw :=
    complex_inv_natCast_isBigO.mul_isLittleO herr_n
  have hinv_err : (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : ℂ) * err (n - 1))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
    exact hinv_err_raw.trans_eventuallyEq (rpow_neg_one_mul_eventually α)
  have hAterm : (fun n : ℕ =>
        A * (((((n - 1 : ℕ) : ℝ) ^ α / (n : ℝ) -
            (n : ℝ) ^ (α - 1) + α * (n : ℝ) ^ (α - 2) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) :=
    (ofReal_isLittleO_p2m2 (shifted_rpow_div_first α)).const_mul_left A
  have hBterm : (fun n : ℕ =>
        B * (((((n - 1 : ℕ) : ℝ) ^ (α - 1) / (n : ℝ) -
            (n : ℝ) ^ (α - 2) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) :=
    (ofReal_isLittleO_p2m2 (shifted_rpow_div_second α)).const_mul_left B
  have hsum := (hinv_err.add hAterm).add hBterm
  have heq : (fun n : ℕ =>
      p.coeff n -
        (A * (((n : ℝ) ^ (α - 1) : ℝ) : ℂ) +
          (B - (α : ℂ) * A) * (((n : ℝ) ^ (α - 2) : ℝ) : ℂ))) =ᶠ[atTop]
    (fun n : ℕ =>
      (((n : ℝ)⁻¹ : ℝ) : ℂ) * err (n - 1) +
        A * (((((n - 1 : ℕ) : ℝ) ^ α / (n : ℝ) -
            (n : ℝ) ^ (α - 1) + α * (n : ℝ) ^ (α - 2) : ℝ) : ℂ)) +
        B * (((((n - 1 : ℕ) : ℝ) ^ (α - 1) / (n : ℝ) -
            (n : ℝ) ^ (α - 2) : ℝ) : ℂ))) := by
    refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    have hpcoeff := coeff_of_scalarDerivSeries_pred p hn
    have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn
    have hnR_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos_nat)
    have hdiv0 :
        (((n : ℝ)⁻¹ : ℝ) : ℂ) *
          ((((n - 1 : ℕ) : ℝ) ^ α : ℝ) : ℂ) =
            (((((n - 1 : ℕ) : ℝ) ^ α / (n : ℝ) : ℝ) : ℂ)) := by
      rw [← Complex.ofReal_mul]
      congr 1
      field_simp [hnR_ne]
    have hdiv1 :
        (((n : ℝ)⁻¹ : ℝ) : ℂ) *
          ((((n - 1 : ℕ) : ℝ) ^ (α - 1) : ℝ) : ℂ) =
            (((((n - 1 : ℕ) : ℝ) ^ (α - 1) / (n : ℝ) : ℝ) : ℂ)) := by
      rw [← Complex.ofReal_mul]
      congr 1
      field_simp [hnR_ne]
    change p.coeff n -
        (A * (((n : ℝ) ^ (α - 1) : ℝ) : ℂ) +
          (B - (α : ℂ) * A) * (((n : ℝ) ^ (α - 2) : ℝ) : ℂ)) =
      (((n : ℝ)⁻¹ : ℝ) : ℂ) * err (n - 1) +
        A * (((((n - 1 : ℕ) : ℝ) ^ α / (n : ℝ) -
            (n : ℝ) ^ (α - 1) + α * (n : ℝ) ^ (α - 2) : ℝ) : ℂ)) +
        B * (((((n - 1 : ℕ) : ℝ) ^ (α - 1) / (n : ℝ) -
            (n : ℝ) ^ (α - 2) : ℝ) : ℂ))
    rw [hpcoeff]
    dsimp [err]
    have hdiv0A :
        (((n : ℝ)⁻¹ : ℝ) : ℂ) *
          (A * ((((n - 1 : ℕ) : ℝ) ^ α : ℝ) : ℂ)) =
            A * (((((n - 1 : ℕ) : ℝ) ^ α / (n : ℝ) : ℝ) : ℂ)) := by
      calc
        (((n : ℝ)⁻¹ : ℝ) : ℂ) *
            (A * ((((n - 1 : ℕ) : ℝ) ^ α : ℝ) : ℂ))
            = A * ((((n : ℝ)⁻¹ : ℝ) : ℂ) *
                ((((n - 1 : ℕ) : ℝ) ^ α : ℝ) : ℂ)) := by ring
        _ = A * (((((n - 1 : ℕ) : ℝ) ^ α / (n : ℝ) : ℝ) : ℂ)) := by
            rw [hdiv0]
    have hdiv1B :
        (((n : ℝ)⁻¹ : ℝ) : ℂ) *
          (B * ((((n - 1 : ℕ) : ℝ) ^ (α - 1) : ℝ) : ℂ)) =
            B * (((((n - 1 : ℕ) : ℝ) ^ (α - 1) / (n : ℝ) : ℝ) : ℂ)) := by
      calc
        (((n : ℝ)⁻¹ : ℝ) : ℂ) *
            (B * ((((n - 1 : ℕ) : ℝ) ^ (α - 1) : ℝ) : ℂ))
            = B * ((((n : ℝ)⁻¹ : ℝ) : ℂ) *
                ((((n - 1 : ℕ) : ℝ) ^ (α - 1) : ℝ) : ℂ)) := by ring
        _ = B * (((((n - 1 : ℕ) : ℝ) ^ (α - 1) / (n : ℝ) : ℝ) : ℂ)) := by
            rw [hdiv1]
    rw [mul_sub, mul_add, hdiv0A, hdiv1B]
    norm_num [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul]
    ring
  exact heq.trans_isLittleO hsum

lemma secondOrderShiftCorr_succ (α : ℝ) (k : ℕ) :
    secondOrderShiftCorr α (k + 1) =
      secondOrderShiftCorr α k + (α + k) := by
  simp [secondOrderShiftCorr, Finset.sum_range_succ]

lemma secondOrderShiftCorr_eq (α : ℝ) (k : ℕ) :
    secondOrderShiftCorr α k =
      (k : ℝ) * α + (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  induction k with
  | zero =>
      simp [secondOrderShiftCorr]
  | succ k ih =>
      rw [secondOrderShiftCorr_succ, ih]
      norm_num [Nat.cast_add]
      ring

lemma scalarIteratedDerivSeries_succ
    (k : ℕ) (p : FormalMultilinearSeries ℂ ℂ ℂ) :
    scalarIteratedDerivSeries (k + 1) p =
      scalarDerivSeries (scalarIteratedDerivSeries k p) := rfl

theorem secondOrder_of_iteratedDeriv_secondOrder
    (k : ℕ) {α : ℝ} {A B : ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hderiv :
      (fun m : ℕ =>
        (scalarIteratedDerivSeries k p).coeff m -
          (A * (((m : ℝ) ^ (α + (k : ℝ) - 1) : ℝ) : ℂ) +
           B * (((m : ℝ) ^ (α + (k : ℝ) - 2) : ℝ) : ℂ)))
        =o[atTop] (fun m : ℕ => (m : ℝ) ^ (α + (k : ℝ) - 2))) :
    (fun n : ℕ =>
      p.coeff n -
        (A * (((n : ℝ) ^ (α - 1) : ℝ) : ℂ) +
         (B - ((secondOrderShiftCorr α k : ℝ) : ℂ) * A) *
            (((n : ℝ) ^ (α - 2) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
  induction k generalizing p α B with
  | zero =>
      simpa [scalarIteratedDerivSeries, secondOrderShiftCorr] using hderiv
  | succ k ih =>
      let q : FormalMultilinearSeries ℂ ℂ ℂ := scalarIteratedDerivSeries k p
      let a : ℝ := α + k
      have hderiv_q :
          (fun m : ℕ =>
            (scalarDerivSeries q).coeff m -
              (A * (((m : ℝ) ^ a : ℝ) : ℂ) +
               B * (((m : ℝ) ^ (a - 1) : ℝ) : ℂ)))
            =o[atTop] (fun m : ℕ => (m : ℝ) ^ (a - 1)) := by
        refine hderiv.congr' ?_ ?_
        · refine Eventually.of_forall fun m => ?_
          dsimp [q, a]
          rw [scalarIteratedDerivSeries_succ]
          congr 2
          · congr 1
            norm_num [Nat.cast_add]
            ring
          · congr 1
            norm_num [Nat.cast_add]
            ring
        · refine Eventually.of_forall fun m => ?_
          dsimp [a]
          congr 1
          norm_num [Nat.cast_add]
          ring
      have hq := secondOrder_of_deriv_secondOrder
        (α := a) (A := A) (B := B) (p := q) hderiv_q
      let Bq : ℂ := B - (a : ℂ) * A
      have hq' :
          (fun m : ℕ =>
            (scalarIteratedDerivSeries k p).coeff m -
              (A * (((m : ℝ) ^ (α + (k : ℝ) - 1) : ℝ) : ℂ) +
               Bq * (((m : ℝ) ^ (α + (k : ℝ) - 2) : ℝ) : ℂ)))
            =o[atTop] (fun m : ℕ => (m : ℝ) ^ (α + (k : ℝ) - 2)) := by
        simpa [q, a, Bq, add_assoc, add_comm, add_left_comm] using hq
      have hp := ih (α := α) (B := Bq) (p := p) hq'
      refine hp.congr_left ?_
      intro n
      dsimp [Bq, a]
      rw [secondOrderShiftCorr_succ]
      norm_num [Complex.ofReal_add]
      ring_nf
      exact Or.inl trivial

lemma rising_succ (a : ℝ) (k : ℕ) :
    rising a (k + 1) = rising a k * (a + k) := by
  simp [rising, Finset.prod_range_succ]

private lemma deriv_one_sub_cpow_neg {a : ℝ} {z : ℂ}
    (hz : (1 - z) ∈ Complex.slitPlane) :
    deriv (fun w : ℂ => (1 - w) ^ (-(a : ℂ))) z =
      (a : ℂ) * (1 - z) ^ (-(((a + 1 : ℝ) : ℂ))) := by
  have hdiff : DifferentiableAt ℂ (fun w : ℂ => 1 - w) z := by fun_prop
  have hder : deriv (fun w : ℂ => 1 - w) z = -1 := by
    rw [deriv_const_sub]
    simp [deriv_id'']
  rw [deriv_cpow_const hdiff hz, hder]
  have hexp : (-(a : ℂ) - 1) = (-(((a + 1 : ℝ) : ℂ))) := by
    norm_num [Complex.ofReal_add]
    ring
  rw [hexp]
  ring

private lemma eventually_one_sub_mem_slitPlane {z : ℂ}
    (hz : (1 - z) ∈ Complex.slitPlane) :
    ∀ᶠ w : ℂ in 𝓝 z, (1 - w) ∈ Complex.slitPlane := by
  have hcont : ContinuousAt (fun w : ℂ => 1 - w) z := by fun_prop
  exact hcont.eventually_mem (Complex.isOpen_slitPlane.mem_nhds hz)

lemma iteratedDeriv_one_sub_cpow_neg (k : ℕ) {a : ℝ} {z : ℂ}
    (hz : (1 - z) ∈ Complex.slitPlane) :
    iteratedDeriv k (fun w : ℂ => (1 - w) ^ (-(a : ℂ))) z =
      (((rising a k : ℝ) : ℂ) *
        (1 - z) ^ (-(((a + (k : ℝ) : ℝ) : ℂ)))) := by
  induction k generalizing z with
  | zero =>
      simp [iteratedDeriv_zero, rising]
  | succ k ih =>
      rw [iteratedDeriv_succ]
      let F : ℂ → ℂ := iteratedDeriv k (fun w : ℂ => (1 - w) ^ (-(a : ℂ)))
      let G : ℂ → ℂ := fun w : ℂ =>
        ((rising a k : ℝ) : ℂ) *
          (1 - w) ^ (-(((a + (k : ℝ) : ℝ) : ℂ)))
      have heq : F =ᶠ[𝓝 z] G := by
        filter_upwards [eventually_one_sub_mem_slitPlane hz] with w hw
        exact ih hw
      have hdiff_base : DifferentiableAt ℂ
          (fun w : ℂ => (1 - w) ^ (-(((a + (k : ℝ) : ℝ) : ℂ)))) z := by
        exact (show DifferentiableAt ℂ (fun w : ℂ => 1 - w) z by fun_prop).cpow_const hz
      calc
        deriv (iteratedDeriv k (fun w : ℂ => (1 - w) ^ (-(a : ℂ)))) z
            = deriv G z := Filter.EventuallyEq.deriv_eq heq
        _ = ((rising a k : ℝ) : ℂ) *
            (((a + (k : ℝ) : ℝ) : ℂ) *
              (1 - z) ^ (-(((a + (k : ℝ) + 1 : ℝ) : ℂ)))) := by
              dsimp [G]
              rw [deriv_const_mul _ hdiff_base]
              rw [deriv_one_sub_cpow_neg (a := a + (k : ℝ)) hz]
        _ = ((rising a (k + 1) : ℝ) : ℂ) *
            (1 - z) ^ (-(((a + ((k + 1 : ℕ) : ℝ) : ℝ) : ℂ))) := by
              rw [rising_succ]
              norm_num [Complex.ofReal_mul, Complex.ofReal_add, Nat.cast_add]
              ring

lemma Real.Gamma_add_nat_rising_of_forall_ne
    {a : ℝ} (k : ℕ)
    (h : ∀ j ∈ Finset.range k, a + (j : ℝ) ≠ 0) :
    Real.Gamma (a + (k : ℝ)) = rising a k * Real.Gamma a := by
  induction k with
  | zero =>
      simp [rising]
  | succ k ih =>
      have hlast : a + (k : ℝ) ≠ 0 := h k (by simp)
      have hprev : ∀ j ∈ Finset.range k, a + (j : ℝ) ≠ 0 := by
        intro j hj
        exact h j (by
          exact Finset.mem_range.mpr
            (Nat.lt_trans (Finset.mem_range.mp hj) (Nat.lt_succ_self k)))
      calc
        Real.Gamma (a + ((k + 1 : ℕ) : ℝ))
            = Real.Gamma ((a + (k : ℝ)) + 1) := by
                congr 1
                norm_num [Nat.cast_add]
                ring
        _ = (a + (k : ℝ)) * Real.Gamma (a + (k : ℝ)) :=
                Real.Gamma_add_one hlast
        _ = (a + (k : ℝ)) * (rising a k * Real.Gamma a) := by
                rw [ih hprev]
        _ = rising a (k + 1) * Real.Gamma a := by
                rw [rising_succ]
                ring

private lemma rising_ne_zero_of_forall_ne {a : ℝ} {k : ℕ}
    (h : ∀ j ∈ Finset.range k, a + (j : ℝ) ≠ 0) :
    rising a k ≠ 0 := by
  unfold rising
  exact Finset.prod_ne_zero_iff.mpr h

private lemma noPole_alpha_add {α : ℝ}
    (hαpole : ∀ m : ℕ, α ≠ 1 - (m : ℝ)) {k : ℕ} :
    ∀ j ∈ Finset.range k, α + (j : ℝ) ≠ 0 := by
  intro j _hj hzero
  have hα : α = 1 - ((j + 1 : ℕ) : ℝ) := by
    have : α = -(j : ℝ) := by linarith
    rw [this]
    norm_num [Nat.cast_add]
  exact hαpole (j + 1) hα

private lemma noPole_alpha_sub_one_add {α : ℝ}
    (hαpole : ∀ m : ℕ, α ≠ 1 - (m : ℝ)) {k : ℕ} :
    ∀ j ∈ Finset.range k, α - 1 + (j : ℝ) ≠ 0 := by
  intro j _hj hzero
  have hα : α = 1 - (j : ℝ) := by linarith
  exact hαpole j hα

private lemma Real.Gamma_ne_zero_of_alpha_pole {α : ℝ}
    (hαpole : ∀ m : ℕ, α ≠ 1 - (m : ℝ)) :
    Real.Gamma α ≠ 0 := by
  exact Real.Gamma_ne_zero (by
    intro m hm
    have hα : α = 1 - ((m + 1 : ℕ) : ℝ) := by
      rw [hm]
      norm_num [Nat.cast_add]
    exact hαpole (m + 1) hα)

private lemma Real.Gamma_ne_zero_of_alpha_sub_one_pole {α : ℝ}
    (hαpole : ∀ m : ℕ, α ≠ 1 - (m : ℝ)) :
    Real.Gamma (α - 1) ≠ 0 := by
  exact Real.Gamma_ne_zero (by
    intro m hm
    have hα : α = 1 - (m : ℝ) := by linarith
    exact hαpole m hα)

lemma rising_div_Gamma_add_eq_inv_Gamma
    {α : ℝ} (k : ℕ)
    (hαpole : ∀ m : ℕ, α ≠ 1 - (m : ℝ)) :
    rising α k / Real.Gamma (α + (k : ℝ)) = 1 / Real.Gamma α := by
  have hprod : rising α k ≠ 0 :=
    rising_ne_zero_of_forall_ne (noPole_alpha_add (α := α) hαpole)
  have hΓ : Real.Gamma α ≠ 0 := Real.Gamma_ne_zero_of_alpha_pole hαpole
  have hrec := Real.Gamma_add_nat_rising_of_forall_ne
    (a := α) k (noPole_alpha_add (α := α) hαpole)
  rw [hrec]
  field_simp [hprod, hΓ]

lemma rising_sub_one_div_Gamma_add_eq_inv_Gamma_sub_one
    {α : ℝ} (k : ℕ)
    (hαpole : ∀ m : ℕ, α ≠ 1 - (m : ℝ)) :
    rising (α - 1) k / Real.Gamma (α - 1 + (k : ℝ)) =
      1 / Real.Gamma (α - 1) := by
  have hprod : rising (α - 1) k ≠ 0 :=
    rising_ne_zero_of_forall_ne (noPole_alpha_sub_one_add (α := α) hαpole)
  have hΓ : Real.Gamma (α - 1) ≠ 0 :=
    Real.Gamma_ne_zero_of_alpha_sub_one_pole hαpole
  have hrec := Real.Gamma_add_nat_rising_of_forall_ne
    (a := α - 1) k (noPole_alpha_sub_one_add (α := α) hαpole)
  rw [hrec]
  field_simp [hprod, hΓ]

theorem transfer_twoTerm_secondOrder_general_of_k
    {α : ℝ} {C0 C1 : ℂ} {R φ : ℝ} {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (k : ℕ)
    (hβ : 1 < α + (k : ℝ))
    (hαpole : ∀ m : ℕ, α ≠ 1 - (m : ℝ))
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ =>
        ‖f z - C0 * (1 - z) ^ (-(α : ℂ)) -
            C1 * (1 - z) ^ (-(((α - 1 : ℝ) : ℂ)))‖ *
          ‖(1 : ℂ) - z‖ ^ (α - 1))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ =>
      p.coeff n -
        (C0 *
            ((((n : ℝ) ^ (α - 1) / Real.Gamma α : ℝ) : ℂ) +
              (((α * (α - 1) / 2 / Real.Gamma α) *
                  (n : ℝ) ^ (α - 2) : ℝ) : ℂ)) +
          C1 * (((n : ℝ) ^ (α - 2) / Real.Gamma (α - 1) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
  let β : ℝ := α + (k : ℝ)
  let D0 : ℂ := C0 * (((rising α k : ℝ) : ℂ))
  let D1 : ℂ := C1 * (((rising (α - 1) k : ℝ) : ℂ))
  let A : ℂ := C0 * (((1 / Real.Gamma α : ℝ) : ℂ))
  let B : ℂ :=
    C0 * ((((β * (β - 1) / 2 / Real.Gamma α : ℝ)) : ℂ)) +
      C1 * (((1 / Real.Gamma (α - 1) : ℝ) : ℂ))
  let h0 : ℂ → ℂ := fun z => (1 - z) ^ (-(α : ℂ))
  let h1 : ℂ → ℂ := fun z => (1 - z) ^ (-(((α - 1 : ℝ) : ℂ)))
  let g : ℂ → ℂ := fun z => f z - C0 • h0 z - C1 • h1 z
  let R' : ℝ := (1 + R) / 2
  let φ' : ℝ := (φ + Real.pi / 2) / 2
  have hφπ : φ < Real.pi := by linarith [hφ2, Real.pi_pos]
  have hR'1 : 1 < R' := by dsimp [R']; linarith
  have hRR' : R' < R := by dsimp [R']; linarith
  have hφ'0 : 0 < φ' := by dsimp [φ']; linarith [hφ0, Real.pi_pos]
  have hφlt : φ < φ' := by dsimp [φ']; linarith [hφ2]
  have hφ'2 : φ' < Real.pi / 2 := by dsimp [φ']; linarith [hφ2]
  have hφ'π : φ' < Real.pi := by linarith [hφ'2, Real.pi_pos]
  have hsubset : DeltaDomainArg R' φ' ⊆ DeltaDomainArg R φ := by
    intro z hz
    exact ⟨lt_trans hz.1 hRR', hz.2.1, lt_trans hφlt hz.2.2⟩
  have hΔ0 : AnalyticOnNhd ℂ h0 (DeltaDomainArg R φ) := by
    simpa [h0] using
      (analyticOnNhd_one_sub_cpow_deltaDomain
        (α := (α : ℂ)) (R := R) (φ := φ) hφ0 hφπ)
  have hΔ1 : AnalyticOnNhd ℂ h1 (DeltaDomainArg R φ) := by
    simpa [h1] using
      (analyticOnNhd_one_sub_cpow_deltaDomain
        (α := (((α - 1 : ℝ) : ℂ))) (R := R) (φ := φ) hφ0 hφπ)
  have hΔg : AnalyticOnNhd ℂ g (DeltaDomainArg R φ) := by
    simpa [g] using
      (hΔ.sub (hΔ0.const_smul (c := C0))).sub (hΔ1.const_smul (c := C1))
  have hsing_g : Tendsto (fun z : ℂ => ‖g z‖ * ‖(1 : ℂ) - z‖ ^ (α - 1))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0) := by
    simpa [g, h0, h1, smul_eq_mul] using hsing
  have hderiv_g_o : Tendsto (fun z : ℂ =>
      ‖iteratedDeriv k g z‖ * ‖(1 : ℂ) - z‖ ^ (β - 1))
      (𝓝[DeltaDomainArg R' φ'] (1 : ℂ)) (𝓝 0) := by
    have h := iteratedDeriv_littleO_of_delta_littleO
      (R := R) (R' := R') (φ := φ) (φ' := φ') (β := α - 1)
      (f := g) k hR'1 hRR' hφ0 hφlt hφ'2 hΔg hsing_g
    convert h using 1
    ext z
    congr 2
    dsimp [β]
    ring
  have hΔ' : AnalyticOnNhd ℂ f (DeltaDomainArg R' φ') := fun z hz => hΔ z (hsubset hz)
  have hp_iter : HasFPowerSeriesAt (iteratedDeriv k f)
      (scalarIteratedDerivSeries k p) (0 : ℂ) := hp.scalar_iteratedDeriv k
  have hΔ_iter : AnalyticOnNhd ℂ (iteratedDeriv k f) (DeltaDomainArg R' φ') := by
    simpa [iteratedDeriv_eq_iterate] using hΔ'.iterated_deriv k
  have hderiv_g_eq : ∀ z ∈ DeltaDomainArg R' φ',
      iteratedDeriv k g z =
        iteratedDeriv k f z -
          D0 * (1 - z) ^ (-(β : ℂ)) -
          D1 * (1 - z) ^ (-(((β - 1 : ℝ) : ℂ))) := by
    intro z hz
    have hz_big : z ∈ DeltaDomainArg R φ := hsubset hz
    have hzslit : (1 - z) ∈ Complex.slitPlane :=
      one_sub_mem_slitPlane_of_mem_delta hφ0 hz_big
    have hfcont : ContDiffAt ℂ (↑k) f z := (hΔ z hz_big).contDiffAt
    have h0cont : ContDiffAt ℂ (↑k) h0 z := (hΔ0 z hz_big).contDiffAt
    have h1cont : ContDiffAt ℂ (↑k) h1 z := (hΔ1 z hz_big).contDiffAt
    have hC0cont : ContDiffAt ℂ (↑k) (fun y : ℂ => C0 • h0 y) z :=
      h0cont.const_smul C0
    have hC1cont : ContDiffAt ℂ (↑k) (fun y : ℂ => C1 • h1 y) z :=
      h1cont.const_smul C1
    change iteratedDeriv k ((fun y : ℂ => f y - C0 • h0 y) -
          fun y : ℂ => C1 • h1 y) z =
        iteratedDeriv k f z -
          D0 * (1 - z) ^ (-(β : ℂ)) -
          D1 * (1 - z) ^ (-(((β - 1 : ℝ) : ℂ)))
    rw [iteratedDeriv_sub (hfcont.sub hC0cont) hC1cont]
    have hsub0 :
        iteratedDeriv k (fun x : ℂ => f x - C0 • h0 x) z =
          iteratedDeriv k f z - iteratedDeriv k (fun y : ℂ => C0 • h0 y) z := by
      simpa using (iteratedDeriv_sub hfcont hC0cont)
    rw [hsub0]
    have hC0der :
        iteratedDeriv k (fun y : ℂ => C0 • h0 y) z =
          C0 • iteratedDeriv k h0 z := by
      simpa using (iteratedDeriv_const_smul h0cont C0)
    have hC1der :
        iteratedDeriv k (fun y : ℂ => C1 • h1 y) z =
          C1 • iteratedDeriv k h1 z := by
      simpa using (iteratedDeriv_const_smul h1cont C1)
    rw [hC0der, hC1der]
    rw [iteratedDeriv_one_sub_cpow_neg (k := k) (a := α) hzslit]
    rw [iteratedDeriv_one_sub_cpow_neg (k := k) (a := α - 1) hzslit]
    dsimp [h0, h1, D0, D1, β]
    norm_num [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, smul_eq_mul]
    ring_nf
  have hsing_deriv : Tendsto
      (fun z : ℂ =>
        ‖iteratedDeriv k f z - D0 * (1 - z) ^ (-(β : ℂ)) -
            D1 * (1 - z) ^ (-(((β - 1 : ℝ) : ℂ)))‖ *
          ‖(1 : ℂ) - z‖ ^ (β - 1))
      (𝓝[DeltaDomainArg R' φ'] (1 : ℂ)) (𝓝 0) := by
    refine hderiv_g_o.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [hderiv_g_eq z hz]
  have htransfer := transfer_twoTerm_secondOrder
    (α := β) (C0 := D0) (C1 := D1)
    (R := R') (φ := φ') (f := iteratedDeriv k f)
    (p := scalarIteratedDerivSeries k p)
    (by simpa [β] using hβ) hR'1 hφ'0 hφ'2 hp_iter hΔ_iter hsing_deriv
  have hrise0 := rising_div_Gamma_add_eq_inv_Gamma (α := α) k hαpole
  have hrise1 := rising_sub_one_div_Gamma_add_eq_inv_Gamma_sub_one (α := α) k hαpole
  have hrise0' :
      ((rising α k / Real.Gamma (α + (k : ℝ)) : ℝ) : ℂ) =
        ((1 / Real.Gamma α : ℝ) : ℂ) := by
    rw [hrise0]
  have hrise1' :
      ((rising (α - 1) k / Real.Gamma (α + (k : ℝ) - 1) : ℝ) : ℂ) =
        ((1 / Real.Gamma (α - 1) : ℝ) : ℂ) := by
    convert congrArg (fun x : ℝ => ((x : ℝ) : ℂ)) hrise1 using 2
    ring
  have hrise0C :
      (((rising α k : ℝ) : ℂ) / ((Real.Gamma (α + (k : ℝ)) : ℝ) : ℂ)) =
        (((Real.Gamma α : ℝ) : ℂ))⁻¹ := by
    calc
      (((rising α k : ℝ) : ℂ) / ((Real.Gamma (α + (k : ℝ)) : ℝ) : ℂ))
          = ((rising α k / Real.Gamma (α + (k : ℝ)) : ℝ) : ℂ) := by
              rw [Complex.ofReal_div]
      _ = ((1 / Real.Gamma α : ℝ) : ℂ) := hrise0'
      _ = (((Real.Gamma α : ℝ) : ℂ))⁻¹ := by
              rw [Complex.ofReal_div]
              norm_num
  have hrise1C :
      (((rising (α - 1) k : ℝ) : ℂ) /
          ((Real.Gamma (α + (k : ℝ) - 1) : ℝ) : ℂ)) =
        (((Real.Gamma (α - 1) : ℝ) : ℂ))⁻¹ := by
    calc
      (((rising (α - 1) k : ℝ) : ℂ) /
          ((Real.Gamma (α + (k : ℝ) - 1) : ℝ) : ℂ))
          = ((rising (α - 1) k /
              Real.Gamma (α + (k : ℝ) - 1) : ℝ) : ℂ) := by
              rw [Complex.ofReal_div]
      _ = ((1 / Real.Gamma (α - 1) : ℝ) : ℂ) := hrise1'
      _ = (((Real.Gamma (α - 1) : ℝ) : ℂ))⁻¹ := by
              rw [Complex.ofReal_div]
              norm_num
  have hderiv_AB :
      (fun m : ℕ =>
        (scalarIteratedDerivSeries k p).coeff m -
          (A * (((m : ℝ) ^ (α + (k : ℝ) - 1) : ℝ) : ℂ) +
           B * (((m : ℝ) ^ (α + (k : ℝ) - 2) : ℝ) : ℂ)))
        =o[atTop] (fun m : ℕ => (m : ℝ) ^ (α + (k : ℝ) - 2)) := by
    refine htransfer.congr' ?_ ?_
    · refine Eventually.of_forall fun n => ?_
      dsimp [A, B, D0, D1, β]
      norm_num [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_div]
      ring_nf at hrise0C hrise1C ⊢
      rw [hrise0C, hrise1C]
    · refine Eventually.of_forall fun n => ?_
      dsimp [β]
  have hdesc := secondOrder_of_iteratedDeriv_secondOrder
    (k := k) (α := α) (A := A) (B := B) (p := p) hderiv_AB
  refine hdesc.congr_left ?_
  intro n
  dsimp [A, B, β]
  rw [secondOrderShiftCorr_eq]
  norm_num [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_div]
  ring_nf

theorem transfer_twoTerm_secondOrder_general
    {α : ℝ} {C0 C1 : ℂ} {R φ : ℝ} {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hαpole : ∀ m : ℕ, α ≠ 1 - (m : ℝ))
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ =>
        ‖f z - C0 * (1 - z) ^ (-(α : ℂ)) -
            C1 * (1 - z) ^ (-(((α - 1 : ℝ) : ℂ)))‖ *
          ‖(1 : ℂ) - z‖ ^ (α - 1))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ =>
      p.coeff n -
        (C0 *
            ((((n : ℝ) ^ (α - 1) / Real.Gamma α : ℝ) : ℂ) +
              (((α * (α - 1) / 2 / Real.Gamma α) *
                  (n : ℝ) ^ (α - 2) : ℝ) : ℂ)) +
          C1 * (((n : ℝ) ^ (α - 2) / Real.Gamma (α - 1) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (1 - α)
  exact transfer_twoTerm_secondOrder_general_of_k
    (α := α) (C0 := C0) (C1 := C1) (R := R) (φ := φ)
    (f := f) (p := p) k (by linarith) hαpole hR hφ0 hφ2 hp hΔ hsing

end
end

section
open Complex Filter Asymptotics
open scoped ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic
namespace Alignments

open AnalyticCombinatorics.Ch1

lemma coeff_cycleEGFℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n cycleEGFℂ = ((n : ℂ)⁻¹) := by
  simp [cycleEGFℂ]

lemma coeff_cycleEGFℚ (n : ℕ) :
    PowerSeries.coeff (R := ℚ) n cycleEGFℚ = ((n : ℚ)⁻¹) := by
  simp [cycleEGFℚ]

lemma cycleEGFℚ_constantCoeff :
    PowerSeries.constantCoeff cycleEGFℚ = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_cycleEGFℚ]
  simp

lemma cycleAnalyticFun_zero : cycleAnalyticFun 0 = 0 := by
  simp [cycleAnalyticFun]

theorem cycleAnalyticFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt cycleAnalyticFun (PowerSeries.toFMLS cycleEGFℂ) (0 : ℂ) := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
  have hz_norm : ‖z‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  simpa [cycleAnalyticFun, coeff_cycleEGFℂ, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    Complex.hasSum_taylorSeries_neg_log hz_norm

lemma one_sub_mem_slitPlane_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    1 - z ∈ Complex.slitPlane := by
  rw [sub_eq_add_neg]
  exact Complex.mem_slitPlane_of_norm_lt_one (by simpa using hz)

lemma one_sub_ne_zero_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    1 - z ≠ 0 :=
  Complex.slitPlane_ne_zero (one_sub_mem_slitPlane_of_norm_lt_one hz)

end Alignments
end Meromorphic
end Ch5
end AnalyticCombinatorics
end
end

section
/-!
# Two-regular labelled graphs

This file records the singularity-analysis asymptotic for the EGF

`exp (-z/2 - z^2/4) / sqrt (1 - z)`.

The sequence is defined through this EGF: `twoRegularGraphCount n / n!` is the
real coefficient of the Taylor expansion at zero.
-/

open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries

noncomputable section

/-- The entire prefactor in the EGF for 2-regular labelled graphs. -/
def twoRegularPrefactor (z : ℂ) : ℂ :=
  Complex.exp (-(z / 2) - z ^ 2 / 4)

/-- The EGF as a complex analytic function. -/
def twoRegularEGFFun (z : ℂ) : ℂ :=
  twoRegularPrefactor z * (1 - z) ^ (-(1 / 2 : ℂ))

/-- The singular coefficient produced by evaluating the entire prefactor at `1`. -/
def twoRegularSingularCoeff : ℂ :=
  Complex.exp (-(3 / 4 : ℂ))

lemma analyticOnNhd_twoRegularPrefactor {s : Set ℂ} :
    AnalyticOnNhd ℂ twoRegularPrefactor s := by
  have hid : AnalyticOnNhd ℂ (fun z : ℂ => z) s := analyticOnNhd_id
  have hpoly :
      AnalyticOnNhd ℂ (fun z : ℂ => -(z / 2) - z ^ 2 / 4) s :=
    (hid.div_const.neg).sub ((hid.pow 2).div_const)
  simpa [twoRegularPrefactor] using hpoly.cexp

lemma analyticOnNhd_twoRegularEGFFun {R φ : ℝ} (hφ0 : 0 < φ) (hφπ : φ < Real.pi) :
    AnalyticOnNhd ℂ twoRegularEGFFun (DeltaDomainArg R φ) := by
  unfold twoRegularEGFFun
  exact analyticOnNhd_twoRegularPrefactor.mul
    (analyticOnNhd_one_sub_cpow_deltaDomain (α := (1 / 2 : ℂ))
      (R := R) (φ := φ) hφ0 hφπ)

lemma analyticAt_twoRegularEGFFun_zero :
    AnalyticAt ℂ twoRegularEGFFun (0 : ℂ) := by
  have hR : (0 : ℂ) ∈ DeltaDomainArg (3 / 2 : ℝ) (Real.pi / 4) :=
    zero_mem_deltaDomainArg (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
      (by norm_num) (by nlinarith [Real.pi_pos])
  exact analyticOnNhd_twoRegularEGFFun (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
    (by positivity) (by nlinarith [Real.pi_pos]) 0 hR

/-- The Taylor series at zero of the two-regular EGF. -/
def twoRegularEGFSeriesℂ : FormalMultilinearSeries ℂ ℂ ℂ :=
  Classical.choose analyticAt_twoRegularEGFFun_zero

lemma twoRegularEGFFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt twoRegularEGFFun twoRegularEGFSeriesℂ (0 : ℂ) :=
  Classical.choose_spec analyticAt_twoRegularEGFFun_zero

/-- The EGF coefficient `[z^n] G(z)`, as a real number. -/
def twoRegularEGFCoeff (n : ℕ) : ℝ :=
  ((twoRegularEGFSeriesℂ.coeff n).re)

/-- The labelled count defined by `g_n / n! = [z^n] G(z)`. -/
def twoRegularGraphCount (n : ℕ) : ℝ :=
  (n.factorial : ℝ) * twoRegularEGFCoeff n

lemma twoRegularGraphCount_div_factorial (n : ℕ) :
    twoRegularGraphCount n / (n.factorial : ℝ) = twoRegularEGFCoeff n := by
  unfold twoRegularGraphCount
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]

end
end

section
/-!
# Genuine labelled class of two-regular graphs

A two-regular labelled graph is a labelled `SET` of undirected cycles of
length at least three.  The cycle carried by one block is modelled as a full
cycle permutation on the block labels, modulo reversing the orientation.
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

namespace TwoRegularClass

open AnalyticCombinatorics.Ch1
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments

instance (n : ℕ) : DecidableEq (FullCyclePerm n) := by
  classical
  infer_instance

lemma fullCyclePerm_card {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card (FullCyclePerm n) = (n - 1).factorial := by
  classical
  have hcycles := Equiv.Perm.card_of_cycleType_singleton
    (α := Fin n) (n := n) hn (by simp)
  have hsub :
      Fintype.card (FullCyclePerm n) =
        ({g | g.cycleType = ({n} : Multiset ℕ)} :
          Finset (Equiv.Perm (Fin n))).card := by
    unfold FullCyclePerm
    exact Fintype.subtype_card
      ({g | g.cycleType = ({n} : Multiset ℕ)} : Finset (Equiv.Perm (Fin n)))
      (by intro g; simp)
  rw [hsub, hcycles]
  simp

lemma fullCyclePerm_orderOf {n : ℕ} (c : FullCyclePerm n) :
    orderOf c.1 = n := by
  rw [← Equiv.Perm.lcm_cycleType c.1, c.2]
  simp

lemma fullCycleReverse_ne_of_three_le {n : ℕ} (hn : 3 ≤ n) (c : FullCyclePerm n) :
    fullCycleReverse c ≠ c := by
  intro h
  have hinv : c.1⁻¹ = c.1 := congrArg Subtype.val h
  have hsq : c.1 ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [← hinv]
    rw [mul_inv_cancel]
  have hdiv : n ∣ 2 := by
    rw [← fullCyclePerm_orderOf c]
    exact orderOf_dvd_of_pow_eq_one hsq
  exact not_le_of_gt (by omega : 2 < n) (Nat.le_of_dvd (by norm_num) hdiv)

lemma fixedBy_false_card (n : ℕ) :
    Fintype.card (AddAction.fixedBy (FullCyclePerm n) false) =
      Fintype.card (FullCyclePerm n) := by
  classical
  change Fintype.card {c : FullCyclePerm n // false +ᵥ c = c} =
    Fintype.card (FullCyclePerm n)
  exact Fintype.card_congr
    { toFun := fun c => c.1
      invFun := fun c => ⟨c, rfl⟩
      left_inv := fun c => by cases c; rfl
      right_inv := fun c => rfl }

lemma fixedBy_true_card_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    Fintype.card (AddAction.fixedBy (FullCyclePerm n) true) = 0 := by
  classical
  change Fintype.card {c : FullCyclePerm n // true +ᵥ c = c} = 0
  haveI : IsEmpty {c : FullCyclePerm n // true +ᵥ c = c} :=
    ⟨fun x => fullCycleReverse_ne_of_three_le hn x.1 (by simpa using x.2)⟩
  exact Fintype.card_eq_zero

lemma undirectedCycle_card_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    Fintype.card (UndirectedCycle n) = (n - 1).factorial / 2 := by
  classical
  have hburn := AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup
    Bool (FullCyclePerm n)
  rw [Fintype.sum_bool, fixedBy_false_card, fixedBy_true_card_of_three_le hn,
    fullCyclePerm_card (by omega : 2 ≤ n), Fintype.card_bool, zero_add] at hburn
  exact Nat.eq_div_of_mul_eq_right (by norm_num : 2 ≠ 0)
    (by simpa [UndirectedCycle, mul_comm] using hburn.symm)

@[simp] lemma undirectedCycleClass_counts (n : ℕ) :
    undirectedCycleClass.counts n =
      if 3 ≤ n then (n - 1).factorial / 2 else 0 := by
  classical
  by_cases h : 3 ≤ n
  · simp [undirectedCycleClass, CombClass.counts, h, undirectedCycle_card_of_three_le h]
  · simp [undirectedCycleClass, CombClass.counts, h]

@[simp] lemma undirectedCycleClass_counts_zero :
    undirectedCycleClass.counts 0 = 0 := by
  simp

lemma undirectedCycleClass_coeff_egf_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    PowerSeries.coeff (R := ℚ) n undirectedCycleClass.egf =
      (1 : ℚ) / (2 * n) := by
  rw [CombClass.coeff_egf, undirectedCycleClass_counts, if_pos hn]
  have hn0 : n ≠ 0 := by omega
  have hfac : n.factorial = n * (n - 1).factorial := by
    cases n with
    | zero => contradiction
    | succ m =>
        simp [Nat.factorial_succ, Nat.mul_comm]
  have hcard := undirectedCycle_card_of_three_le hn
  have hburn := AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup
    Bool (FullCyclePerm n)
  rw [Fintype.sum_bool, fixedBy_false_card, fixedBy_true_card_of_three_le hn,
    fullCyclePerm_card (by omega : 2 ≤ n), Fintype.card_bool, zero_add] at hburn
  change (n - 1).factorial = Fintype.card (UndirectedCycle n) * 2 at hburn
  have hmul_nat : Fintype.card (UndirectedCycle n) * 2 = (n - 1).factorial := by
    exact hburn.symm
  have hhalf_mul_nat : ((n - 1).factorial / 2) * 2 = (n - 1).factorial := by
    rw [← hcard]
    exact hmul_nat
  have hmul_rat : (((n - 1).factorial / 2 : ℕ) : ℚ) * 2 =
      ((n - 1).factorial : ℚ) := by
    exact_mod_cast hhalf_mul_nat
  have hhalf_rat :
      (((n - 1).factorial / 2 : ℕ) : ℚ) =
        ((n - 1).factorial : ℚ) / 2 := by
    nlinarith
  rw [hfac]
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  have hfnq : (((n - 1).factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - 1)
  have h2q : (2 : ℚ) ≠ 0 := by norm_num
  rw [hhalf_rat]
  field_simp [hnq, hfnq, h2q]
  norm_num [Nat.cast_mul]
  ring

lemma undirectedCycleClass_coeff_egf_of_lt_three {n : ℕ} (hn : n < 3) :
    PowerSeries.coeff (R := ℚ) n undirectedCycleClass.egf = 0 := by
  rw [CombClass.coeff_egf, undirectedCycleClass_counts, if_neg (by omega)]
  simp

section
end

set_option backward.isDefEq.respectTransparency false in
/-- The core EGF is half the directed cycle EGF, with sizes one and two removed. -/
theorem undirectedCycleClass_egf :
    undirectedCycleClass.egf =
      (2⁻¹ : ℚ) • cycleEGFℚ -
        (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) -
          (4⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2 := by
  ext n
  by_cases hn : 3 ≤ n
  · rw [undirectedCycleClass_coeff_egf_of_three_le hn]
    rw [map_sub, map_sub, map_smul, map_smul, map_smul, coeff_cycleEGFℚ]
    have hn1 : n ≠ 1 := by omega
    have hn2 : n ≠ 2 := by omega
    simp [PowerSeries.coeff_X, PowerSeries.coeff_X_pow, hn1, hn2]
    field_simp [show (n : ℚ) ≠ 0 by exact_mod_cast (by omega : n ≠ 0)]
  · have hnlt : n < 3 := by omega
    rw [undirectedCycleClass_coeff_egf_of_lt_three hnlt]
    interval_cases n
    · simp [cycleEGFℚ_constantCoeff]
    · simp [coeff_cycleEGFℚ, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
    · norm_num [coeff_cycleEGFℚ, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]

/-- The EGF of the genuine two-regular class is the labelled `SET` exponential. -/
theorem twoRegularClass_egf :
    twoRegularClass.egf = (PowerSeries.exp ℚ).subst undirectedCycleClass.egf := by
  rw [twoRegularClass, CombClass.egf_set undirectedCycleClass undirectedCycleClass_counts_zero]

/-! ### Complex analytic bridge to the singularity-analysis file -/

/-- The complex core EGF for one undirected cycle block. -/
def twoRegularCoreEGFℂ : PowerSeries ℂ :=
  PowerSeries.mapℂ undirectedCycleClass.egf

/-- The complex EGF of the genuine two-regular class. -/
def twoRegularClassEGFℂ : PowerSeries ℂ :=
  PowerSeries.mapℂ twoRegularClass.egf

/-- The closed complex core series. -/
def twoRegularCoreSeriesℂ : PowerSeries ℂ :=
  (2⁻¹ : ℂ) • cycleEGFℂ -
    (2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) -
      (4⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2

section
end

set_option backward.isDefEq.respectTransparency false in
lemma twoRegularCoreEGFℂ_eq :
    twoRegularCoreEGFℂ = twoRegularCoreSeriesℂ := by
  unfold twoRegularCoreEGFℂ twoRegularCoreSeriesℂ
  rw [undirectedCycleClass_egf]
  ext n
  simp [PowerSeries.coeff_mapℂ, coeff_cycleEGFℚ, coeff_cycleEGFℂ]
  by_cases h1 : n = 1
  · subst n
    simp [PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
  · by_cases h2 : n = 2
    · subst n
      simp [PowerSeries.coeff_X]
    · simp [PowerSeries.coeff_X, PowerSeries.coeff_X_pow, h1, h2]

lemma twoRegularCoreEGFℂ_constantCoeff :
    PowerSeries.constantCoeff twoRegularCoreEGFℂ = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [twoRegularCoreEGFℂ, PowerSeries.coeff_mapℂ, CombClass.coeff_egf]

lemma twoRegularClassEGFℂ_eq_complex_subst :
    twoRegularClassEGFℂ =
      (PowerSeries.exp ℂ).subst twoRegularCoreEGFℂ := by
  rw [twoRegularClassEGFℂ, twoRegularCoreEGFℂ, twoRegularClass_egf]
  have hsubst : PowerSeries.HasSubst undirectedCycleClass.egf := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, CombClass.coeff_egf,
      undirectedCycleClass_counts_zero]
    simp
  change PowerSeries.map (algebraMap ℚ ℂ)
      ((PowerSeries.exp ℚ).subst undirectedCycleClass.egf) = _
  simpa [PowerSeries.mapℂ] using
    (PowerSeries.map_subst (a := undirectedCycleClass.egf)
      (h := algebraMap ℚ ℂ) hsubst (PowerSeries.exp ℚ))

lemma toFMLS_twoRegularCoreSeriesℂ :
    PowerSeries.toFMLS twoRegularCoreSeriesℂ =
      (2⁻¹ : ℂ) • PowerSeries.toFMLS cycleEGFℂ -
        (2⁻¹ : ℂ) • PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ) -
          (4⁻¹ : ℂ) • PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 2) := by
  ext n
  simp [twoRegularCoreSeriesℂ, PowerSeries.toFMLS]

lemma hasFPowerSeriesAt_id_toFMLS_X :
    HasFPowerSeriesAt (fun z : ℂ => z)
      (PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ)) (0 : ℂ) := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards with z
  let term : ℕ → ℂ :=
    fun n => z ^ n • (PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ)).coeff n
  have hsingle : HasSum term (term 1) := by
    apply hasSum_single
    intro n hn
    simp [term, PowerSeries.coeff_X, hn]
  convert hsingle using 1
  simp [term, PowerSeries.toFMLS]

lemma hasFPowerSeriesAt_sq_toFMLS_X_sq :
    HasFPowerSeriesAt (fun z : ℂ => z ^ 2)
      (PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 2)) (0 : ℂ) := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards with z
  let term : ℕ → ℂ :=
    fun n => z ^ n •
      (PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 2)).coeff n
  have hsingle : HasSum term (term 2) := by
    apply hasSum_single
    intro n hn
    simp [term, PowerSeries.coeff_X_pow, hn]
  convert hsingle using 1
  simp [term, PowerSeries.toFMLS]

/-- Analytic representative of the one-block EGF near zero. -/
def twoRegularCoreFun : ℂ → ℂ :=
  (2⁻¹ : ℂ) • cycleAnalyticFun -
    (2⁻¹ : ℂ) • (fun z : ℂ => z) -
      (4⁻¹ : ℂ) • (fun z : ℂ => z ^ 2)

lemma twoRegularCoreFun_zero : twoRegularCoreFun 0 = 0 := by
  simp [twoRegularCoreFun, cycleAnalyticFun_zero]

lemma twoRegularCoreFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt twoRegularCoreFun
      (PowerSeries.toFMLS twoRegularCoreEGFℂ) (0 : ℂ) := by
  have hcycle := cycleAnalyticFun_hasFPowerSeriesAt_zero.const_smul (c := (2⁻¹ : ℂ))
  have hid := hasFPowerSeriesAt_id_toFMLS_X.const_smul (c := (2⁻¹ : ℂ))
  have hsq := hasFPowerSeriesAt_sq_toFMLS_X_sq.const_smul (c := (4⁻¹ : ℂ))
  have h := (hcycle.sub hid).sub hsq
  rw [twoRegularCoreEGFℂ_eq, toFMLS_twoRegularCoreSeriesℂ]
  simpa [twoRegularCoreFun] using h

lemma exp_toFMLS_exp_eq_expSeries :
    PowerSeries.toFMLS (PowerSeries.exp ℂ) = NormedSpace.expSeries ℂ ℂ := by
  rw [NormedSpace.expSeries_eq_ofScalars]
  ext n
  simp [PowerSeries.toFMLS]

lemma exp_hasFPowerSeriesAt_zero_toFMLS :
    HasFPowerSeriesAt Complex.exp (PowerSeries.toFMLS (PowerSeries.exp ℂ)) (0 : ℂ) := by
  have hsum : HasFPowerSeriesAt (NormedSpace.expSeries ℂ ℂ).sum
      (NormedSpace.expSeries ℂ ℂ) (0 : ℂ) := by
    exact ((NormedSpace.expSeries ℂ ℂ).hasFPowerSeriesOnBall
      (by
        rw [NormedSpace.expSeries_radius_eq_top]
        exact WithTop.top_pos)).hasFPowerSeriesAt
  have hfun : (NormedSpace.expSeries ℂ ℂ).sum = Complex.exp := by
    funext z
    calc
      (NormedSpace.expSeries ℂ ℂ).sum z = NormedSpace.exp z := by
        exact congrFun (NormedSpace.exp_eq_expSeries_sum ℂ).symm z
      _ = Complex.exp z := by
        exact (congrFun Complex.exp_eq_exp_ℂ z).symm
  rw [exp_toFMLS_exp_eq_expSeries]
  rwa [hfun] at hsum

lemma twoRegularClassEGFℂ_hasFPowerSeriesAt_exp_core :
    HasFPowerSeriesAt (fun z : ℂ => Complex.exp (twoRegularCoreFun z))
      (PowerSeries.toFMLS twoRegularClassEGFℂ) (0 : ℂ) := by
  have houter : HasFPowerSeriesAt Complex.exp
      (PowerSeries.toFMLS (PowerSeries.exp ℂ)) (twoRegularCoreFun 0) := by
    simpa [twoRegularCoreFun_zero] using exp_hasFPowerSeriesAt_zero_toFMLS
  have hcomp := HasFPowerSeriesAt.comp (g := Complex.exp)
    (f := twoRegularCoreFun) houter twoRegularCoreFun_hasFPowerSeriesAt_zero
  rw [twoRegularClassEGFℂ_eq_complex_subst]
  rw [PowerSeries.toFMLS_subst_eq_comp twoRegularCoreEGFℂ_constantCoeff]
  simpa [Function.comp_def] using hcomp

lemma exp_twoRegularCoreFun_eq_twoRegularEGFFun_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    Complex.exp (twoRegularCoreFun z) = twoRegularEGFFun z := by
  have hz0 : (1 : ℂ) - z ≠ 0 := one_sub_ne_zero_of_norm_lt_one hz
  have hcore :
      twoRegularCoreFun z =
        (-(z / 2) - z ^ 2 / 4) + Complex.log (1 - z) * (-(1 / 2 : ℂ)) := by
    simp [twoRegularCoreFun, cycleAnalyticFun]
    ring
  unfold twoRegularEGFFun twoRegularPrefactor
  rw [hcore, Complex.exp_add]
  congr 1
  rw [Complex.cpow_def, if_neg hz0]

theorem twoRegularClassEGFℂ_toFMLS_eq_twoRegularEGFSeriesℂ :
    PowerSeries.toFMLS twoRegularClassEGFℂ = twoRegularEGFSeriesℂ := by
  have heq :
      (fun z : ℂ => Complex.exp (twoRegularCoreFun z)) =ᶠ[𝓝 (0 : ℂ)] twoRegularEGFFun := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
    have hz_norm : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    exact exp_twoRegularCoreFun_eq_twoRegularEGFFun_of_norm_lt_one hz_norm
  exact HasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually
    twoRegularClassEGFℂ_hasFPowerSeriesAt_exp_core
    twoRegularEGFFun_hasFPowerSeriesAt_zero heq

theorem twoRegularClass_counts_eq_twoRegularGraphCount (n : ℕ) :
    (twoRegularClass.counts n : ℝ) = twoRegularGraphCount n := by
  have hseries := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n)
    twoRegularClassEGFℂ_toFMLS_eq_twoRegularEGFSeriesℂ
  have hcoeffℂ :
      (((twoRegularClass.counts n : ℚ) / (n.factorial : ℚ) : ℚ) : ℂ) =
        twoRegularEGFSeriesℂ.coeff n := by
    simpa [twoRegularClassEGFℂ, PowerSeries.coeff_mapℂ, CombClass.coeff_egf]
      using hseries
  have hcoeffℝ :
      (twoRegularClass.counts n : ℝ) / (n.factorial : ℝ) = twoRegularEGFCoeff n := by
    have hre := congrArg Complex.re hcoeffℂ
    simpa [twoRegularEGFCoeff] using hre
  rw [twoRegularGraphCount]
  rw [← hcoeffℝ]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]

end TwoRegularClass
end
end

section
/-!
# Second-order asymptotics for 2-regular labelled graphs

This file applies the `0 < α < 1` second-order transfer theorem to

`exp (-z/2 - z^2/4) * (1 - z)^(-1/2)`.
-/

open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries

noncomputable section

lemma twoRegular_Gamma_neg_half :
    Real.Gamma (-(1 / 2 : ℝ)) = -2 * Real.sqrt Real.pi := by
  have h := Real.Gamma_add_one (s := (-(1 / 2 : ℝ)))
    (by norm_num : (-(1 / 2 : ℝ)) ≠ 0)
  norm_num at h
  rw [Real.Gamma_one_half_eq] at h
  linarith

end
end

/-!
# Third-order asymptotics for 2-regular labelled graphs

This file proves the three-term singularity-analysis expansion for

`exp (-z/2 - z^2/4) * (1 - z)^(-1/2)`.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries

noncomputable section

private def twoRegularInvSqrtSeriesℂ : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun n : ℕ => Ring.choose ((1 / 2 : ℂ) + n - 1) n)

private def twoRegularInvSqrtThirdModel (n : ℕ) : ℝ :=
  ((n : ℝ) ^ (-(1 / 2 : ℝ)) / Real.Gamma (1 / 2 : ℝ)) +
    (((-(1 / 8 : ℝ)) / Real.Gamma (1 / 2 : ℝ)) *
      (n : ℝ) ^ (-(3 / 2 : ℝ))) +
      (((1 / 128 : ℝ) / Real.Gamma (1 / 2 : ℝ)) *
        (n : ℝ) ^ (-(5 / 2 : ℝ)))

private def twoRegularRemainderThirdModel (n : ℕ) : ℂ :=
  twoRegularSingularCoeff *
      (((n : ℝ) ^ (-(3 / 2 : ℝ)) /
        Real.Gamma (-(1 / 2 : ℝ)) : ℝ) : ℂ) +
    twoRegularSingularCoeff *
      (((((3 / 8 : ℝ) / Real.Gamma (-(1 / 2 : ℝ))) *
        (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)) +
    (twoRegularSingularCoeff / 4) *
      (((n : ℝ) ^ (-(5 / 2 : ℝ)) /
        Real.Gamma ((-(1 / 2 : ℝ)) - 1) : ℝ) : ℂ)

private lemma rpow_sub_one_isLittleO_p2m2 (a : ℝ) :
    (fun n : ℕ => (n : ℝ) ^ (a - 1)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ a) := by
  refine IsLittleO.of_bound ?_
  intro c hc
  have hsmall : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ < c :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (Iio_mem_nhds hc)
  filter_upwards [eventually_ge_atTop 1, hsmall] with n hn hninvc
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  have hpowpos : 0 < (n : ℝ) ^ a := Real.rpow_pos_of_pos hnpos a
  have hleft_nonneg : 0 ≤ (n : ℝ) ^ (a - 1) := Real.rpow_nonneg (le_of_lt hnpos) _
  have hright_nonneg : 0 ≤ (n : ℝ) ^ a := le_of_lt hpowpos
  have hpow_eq : (n : ℝ) ^ (a - 1) = (n : ℝ) ^ a * (n : ℝ)⁻¹ := by
    calc
      (n : ℝ) ^ (a - 1) = (n : ℝ) ^ (a + (-(1 : ℝ))) := by ring_nf
      _ = (n : ℝ) ^ a * (n : ℝ) ^ (-(1 : ℝ)) := by rw [Real.rpow_add hnpos]
      _ = (n : ℝ) ^ a * (n : ℝ)⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hnpos), Real.rpow_one]
  calc
    ‖(n : ℝ) ^ (a - 1)‖ = (n : ℝ) ^ (a - 1) := Real.norm_of_nonneg hleft_nonneg
    _ = (n : ℝ) ^ a * (n : ℝ)⁻¹ := hpow_eq
    _ ≤ (n : ℝ) ^ a * c :=
      mul_le_mul_of_nonneg_left (le_of_lt hninvc) (le_of_lt hpowpos)
    _ = c * ‖(n : ℝ) ^ a‖ := by
      rw [Real.norm_of_nonneg hright_nonneg]
      ring

private lemma ofReal_isLittleO_p2m3 {u v : ℕ → ℝ}
    (h : u =o[atTop] v) :
    (fun n : ℕ => ((u n : ℝ) : ℂ)) =o[atTop] v := by
  exact Asymptotics.IsLittleO.of_norm_left (by
    simpa [Complex.norm_real] using h.norm_left)

private lemma complex_re_isLittleO_ofReal {f : ℕ → ℂ} {g r : ℕ → ℝ}
    (h : (fun n : ℕ => f n - ((g n : ℝ) : ℂ)) =o[atTop] r) :
    (fun n : ℕ => (f n).re - g n) =o[atTop] r := by
  rw [Asymptotics.isLittleO_iff] at h ⊢
  intro c hc
  have hc_bound := h hc
  filter_upwards [hc_bound] with n hn
  calc
    ‖(f n).re - g n‖ = ‖(f n - (g n : ℂ)).re‖ := by
      simp [Complex.sub_re]
    _ ≤ ‖f n - (g n : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ c * ‖r n‖ := hn

private lemma coeff_sub_const_smul_p2m2 (C : ℂ)
  (p q : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    (p - C • q).coeff n = p.coeff n - C * q.coeff n := by
  change (p n) 1 - ((C • q) n) 1 = (p n) 1 - C * (q n) 1
  simp only [FormalMultilinearSeries.smul_apply, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul]

private lemma twoRegular_not_pole_neg_half :
    ∀ m : ℕ, (-(1 / 2 : ℝ)) ≠ 1 - (m : ℝ) := by
  intro m hm
  have h2m : (2 * (m : ℝ) : ℝ) = 3 := by nlinarith
  have hnat : 2 * m = 3 := by exact_mod_cast h2m
  omega

lemma twoRegular_Gamma_neg_three_halves :
    Real.Gamma (-(3 / 2 : ℝ)) = 4 * Real.sqrt Real.pi / 3 := by
  have h := Real.Gamma_add_one (s := (-(3 / 2 : ℝ)))
    (by norm_num : (-(3 / 2 : ℝ)) ≠ 0)
  norm_num at h
  rw [twoRegular_Gamma_neg_half] at h
  nlinarith

lemma twoRegularInvSqrt_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt (fun z : ℂ => (1 - z) ^ (-(1 / 2 : ℂ)))
      twoRegularInvSqrtSeriesℂ (0 : ℂ) := by
  have hraw :=
    (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero
      ((1 / 2 : ℂ))).hasFPowerSeriesAt
  unfold twoRegularInvSqrtSeriesℂ
  convert hraw using 1
  ext z
  rw [Complex.cpow_neg, inv_eq_one_div]

lemma analyticOnNhd_twoRegularInvSqrt {R φ : ℝ} (hφ0 : 0 < φ) (hφπ : φ < Real.pi) :
    AnalyticOnNhd ℂ (fun z : ℂ => (1 - z) ^ (-(1 / 2 : ℂ)))
      (DeltaDomainArg R φ) := by
  simpa using
    (analyticOnNhd_one_sub_cpow_deltaDomain
      (α := (1 / 2 : ℂ)) (R := R) (φ := φ) hφ0 hφπ)

lemma twoRegularPrefactor_exp_local (z : ℂ) :
    twoRegularPrefactor z =
      twoRegularSingularCoeff *
        Complex.exp ((1 - z) - (1 - z) ^ 2 / 4) := by
  unfold twoRegularPrefactor twoRegularSingularCoeff
  rw [← Complex.exp_add]
  congr 1
  ring

private lemma complex_exp_sub_quadratic_isLittleO :
    (fun x : ℂ => Complex.exp x - (1 + x + x ^ 2 / 2))
      =o[𝓝 (0 : ℂ)] (fun x : ℂ => ‖x‖ ^ 2) := by
  have h := Complex.exp_sub_sum_range_succ_isLittleO_pow 2
  have hnorm := h.norm_left.norm_right
  refine Asymptotics.IsLittleO.of_norm_left ?_
  refine hnorm.congr' ?_ ?_
  · filter_upwards with x
    congr 1
    simp [Finset.sum_range_succ]
  · filter_upwards with x
    rw [norm_pow]

private lemma twoRegularPrefactor_threeTerm_isLittleO :
    (fun z : ℂ =>
      twoRegularPrefactor z - twoRegularSingularCoeff -
        twoRegularSingularCoeff * (1 - z) -
          (twoRegularSingularCoeff / 4) * (1 - z) ^ 2)
      =o[𝓝 (1 : ℂ)] (fun z : ℂ => ‖(1 : ℂ) - z‖ ^ 2) := by
  let u : ℂ → ℂ := fun z => 1 - z
  let x : ℂ → ℂ := fun z => u z - u z ^ 2 / 4
  have hx0 : Tendsto x (𝓝 (1 : ℂ)) (𝓝 (0 : ℂ)) := by
    have hu0 : Tendsto u (𝓝 (1 : ℂ)) (𝓝 (0 : ℂ)) := by
      simpa [u] using (tendsto_const_nhds.sub tendsto_id : Tendsto
        (fun z : ℂ => (1 : ℂ) - z) (𝓝 (1 : ℂ)) (𝓝 ((1 : ℂ) - 1)))
    simpa [x] using hu0.sub ((hu0.pow 2).div_const 4)
  have hexp :=
    complex_exp_sub_quadratic_isLittleO.comp_tendsto hx0
  have hxO : (fun z : ℂ => ‖x z‖ ^ 2) =O[𝓝 (1 : ℂ)]
      (fun z : ℂ => ‖u z‖ ^ 2) := by
    have hfactor : Tendsto (fun z : ℂ => 1 - u z / 4) (𝓝 (1 : ℂ)) (𝓝 (1 : ℂ)) := by
      have hu0 : Tendsto u (𝓝 (1 : ℂ)) (𝓝 (0 : ℂ)) := by
        simpa [u] using (tendsto_const_nhds.sub tendsto_id : Tendsto
          (fun z : ℂ => (1 : ℂ) - z) (𝓝 (1 : ℂ)) (𝓝 ((1 : ℂ) - 1)))
      simpa using (tendsto_const_nhds.sub (hu0.div_const 4))
    have hbound : (fun z : ℂ => 1 - u z / 4) =O[𝓝 (1 : ℂ)]
        (fun _ : ℂ => (1 : ℝ)) :=
      hfactor.isBigO_one ℝ
    have hbound_norm := hbound.norm_left
    refine IsBigO.of_bound 4 ?_
    have hsmall : ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), ‖1 - u z / 4‖ ≤ 2 := by
      have hlt : ‖(1 : ℂ)‖ < (2 : ℝ) := by norm_num
      exact (hfactor.norm.eventually (Iio_mem_nhds hlt)).mono fun z hz => le_of_lt hz
    filter_upwards [hsmall] with z hz
    have hnonneg : 0 ≤ ‖u z‖ ^ 2 := by positivity
    have hx_eq : x z = u z * (1 - u z / 4) := by
      dsimp [x, u]
      ring
    calc
      ‖‖x z‖ ^ 2‖ = ‖x z‖ ^ 2 := by
        rw [Real.norm_of_nonneg (by positivity : 0 ≤ ‖x z‖ ^ 2)]
      _ = (‖u z‖ * ‖1 - u z / 4‖) ^ 2 := by
        rw [hx_eq, norm_mul]
      _ ≤ (‖u z‖ * 2) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hz (norm_nonneg _)) 2
      _ = 4 * ‖‖u z‖ ^ 2‖ := by
        rw [Real.norm_of_nonneg hnonneg]
        ring
  have hmain : (fun z : ℂ =>
        Complex.exp (x z) - (1 + x z + x z ^ 2 / 2))
      =o[𝓝 (1 : ℂ)] (fun z : ℂ => ‖u z‖ ^ 2) :=
    hexp.trans_isBigO hxO
  have htail : (fun z : ℂ => -u z ^ 3 / 4 + u z ^ 4 / 32)
      =o[𝓝 (1 : ℂ)] (fun z : ℂ => ‖u z‖ ^ 2) := by
    have hu0 : Tendsto u (𝓝 (1 : ℂ)) (𝓝 (0 : ℂ)) := by
      simpa [u] using (tendsto_const_nhds.sub tendsto_id : Tendsto
        (fun z : ℂ => (1 : ℂ) - z) (𝓝 (1 : ℂ)) (𝓝 ((1 : ℂ) - 1)))
    have hcubic : (fun w : ℂ => -w ^ 3 / 4 + w ^ 4 / 32)
        =o[𝓝 (0 : ℂ)] (fun w : ℂ => ‖w‖ ^ 2) := by
      have hsmall : (fun w : ℂ => w) =o[𝓝 (0 : ℂ)] (fun _ : ℂ => (1 : ℝ)) :=
        Asymptotics.IsLittleO.of_norm_left
          ((isLittleO_one_iff ℝ).2 (tendsto_norm_zero : Tendsto
            (fun w : ℂ => ‖w‖) (𝓝 0) (𝓝 0)))
      have hbase : (fun w : ℂ => w ^ 2) =O[𝓝 (0 : ℂ)] (fun w : ℂ => ‖w‖ ^ 2) := by
        refine IsBigO.of_bound 1 ?_
        filter_upwards with w
        rw [norm_pow, Real.norm_of_nonneg (by positivity : 0 ≤ ‖w‖ ^ 2)]
        simp
      have hw3 : (fun w : ℂ => w ^ 3) =o[𝓝 (0 : ℂ)] (fun w : ℂ => ‖w‖ ^ 2) := by
        have h := hbase.mul_isLittleO hsmall
        refine h.congr' ?_ ?_
        · filter_upwards with w
          ring
        · filter_upwards with w
          ring
      have hw4 : (fun w : ℂ => w ^ 4) =o[𝓝 (0 : ℂ)] (fun w : ℂ => ‖w‖ ^ 2) := by
        have hsmall2 : (fun w : ℂ => w ^ 2) =o[𝓝 (0 : ℂ)] (fun _ : ℂ => (1 : ℝ)) := by
          have hnormsq : (fun w : ℂ => ‖w‖ ^ 2) =o[𝓝 (0 : ℂ)]
              (fun _ : ℂ => (1 : ℝ)) := by
            refine (isLittleO_one_iff ℝ).2 ?_
            simpa using ((tendsto_norm_zero : Tendsto (fun w : ℂ => ‖w‖)
              (𝓝 0) (𝓝 0)).pow 2)
          exact hbase.trans_isLittleO hnormsq
        have h := hbase.mul_isLittleO hsmall2
        refine h.congr' ?_ ?_
        · filter_upwards with w
          ring
        · filter_upwards with w
          ring
      exact (hw3.const_mul_left (-(1 / 4 : ℂ))).add
        (hw4.const_mul_left (1 / 32 : ℂ)) |>.congr_left (fun w => by ring)
    simpa [u] using hcubic.comp_tendsto hu0
  have hsum := hmain.add htail
  have hscaled := hsum.const_mul_left twoRegularSingularCoeff
  refine hscaled.congr_left ?_
  intro z
  rw [twoRegularPrefactor_exp_local]
  dsimp [x, u]
  ring

section
end

set_option backward.isDefEq.respectTransparency false in
lemma tendsto_twoRegularPrefactor_threeTerm :
    Tendsto
      (fun z : ℂ =>
        ‖twoRegularPrefactor z - twoRegularSingularCoeff -
            twoRegularSingularCoeff * (1 - z) -
              (twoRegularSingularCoeff / 4) * (1 - z) ^ 2‖ *
          ‖(1 : ℂ) - z‖ ^ (-(2 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  have hnorm := twoRegularPrefactor_threeTerm_isLittleO.norm_left
  have hquot_nhds : Tendsto
      (fun z : ℂ =>
        ‖twoRegularPrefactor z - twoRegularSingularCoeff -
            twoRegularSingularCoeff * (1 - z) -
              (twoRegularSingularCoeff / 4) * (1 - z) ^ 2‖ /
          ‖(1 : ℂ) - z‖ ^ 2)
      (𝓝 (1 : ℂ)) (𝓝 0) := by
    refine (isLittleO_iff_tendsto' ?_).mp hnorm
    filter_upwards with z hz
    have hz1 : z = 1 := by
      rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at hz
      exact hz.symm
    subst z
    norm_num [twoRegularPrefactor, twoRegularSingularCoeff]
  have hwithin : Tendsto
      (fun z : ℂ =>
        ‖twoRegularPrefactor z - twoRegularSingularCoeff -
            twoRegularSingularCoeff * (1 - z) -
              (twoRegularSingularCoeff / 4) * (1 - z) ^ 2‖ /
          ‖(1 : ℂ) - z‖ ^ 2)
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) :=
    hquot_nhds.mono_left nhdsWithin_le_nhds
  refine hwithin.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz_ne : z ≠ 1 := hz.2.1
  have hnorm_ne : ‖(1 : ℂ) - z‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    simpa [sub_eq_zero] using (Ne.symm hz_ne)
  rw [Real.rpow_neg (norm_nonneg ((1 : ℂ) - z))]
  rw [div_eq_mul_inv]
  rw [Real.rpow_two]

lemma twoRegular_remainder_singularity_norm_eq {z : ℂ} (hz : z ≠ 1) :
    ‖(twoRegularEGFFun z -
          twoRegularSingularCoeff * (1 - z) ^ (-(1 / 2 : ℂ))) -
        twoRegularSingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
          (twoRegularSingularCoeff / 4) * (1 - z) ^ (3 / 2 : ℂ)‖ *
        ‖(1 : ℂ) - z‖ ^ (-(3 / 2 : ℝ)) =
      ‖twoRegularPrefactor z - twoRegularSingularCoeff -
          twoRegularSingularCoeff * (1 - z) -
            (twoRegularSingularCoeff / 4) * (1 - z) ^ 2‖ *
        ‖(1 : ℂ) - z‖ ^ (-(2 : ℝ)) := by
  let u : ℂ := 1 - z
  have hu_ne : u ≠ 0 := by
    dsimp [u]
    simpa [sub_eq_zero] using (Ne.symm hz)
  have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  have hpow_half : u * u ^ (-(1 / 2 : ℂ)) = u ^ (1 / 2 : ℂ) := by
    calc
      u * u ^ (-(1 / 2 : ℂ)) =
          u ^ (1 : ℂ) * u ^ (-(1 / 2 : ℂ)) := by rw [Complex.cpow_one]
      _ = u ^ ((1 : ℂ) + (-(1 / 2 : ℂ))) := by
          rw [← Complex.cpow_add _ _ hu_ne]
      _ = u ^ (1 / 2 : ℂ) := by norm_num
  have hpow_three_half : u ^ 2 * u ^ (-(1 / 2 : ℂ)) = u ^ (3 / 2 : ℂ) := by
    have hnat : u ^ 2 = u ^ (2 : ℂ) := (Complex.cpow_natCast u 2).symm
    calc
      u ^ 2 * u ^ (-(1 / 2 : ℂ)) =
          u ^ (2 : ℂ) * u ^ (-(1 / 2 : ℂ)) := by rw [hnat]
      _ = u ^ ((2 : ℂ) + (-(1 / 2 : ℂ))) := by
          rw [← Complex.cpow_add _ _ hu_ne]
      _ = u ^ (3 / 2 : ℂ) := by norm_num
  have hpow_norm : ‖u ^ (-(1 / 2 : ℂ))‖ = ‖u‖ ^ (-(1 / 2 : ℝ)) := by
    convert Complex.norm_cpow_real u (-(1 / 2 : ℝ)) using 1
    norm_num
  unfold twoRegularEGFFun
  change ‖(twoRegularPrefactor z * u ^ (-(1 / 2 : ℂ)) -
          twoRegularSingularCoeff * u ^ (-(1 / 2 : ℂ))) -
        twoRegularSingularCoeff * u ^ (1 / 2 : ℂ) -
          (twoRegularSingularCoeff / 4) * u ^ (3 / 2 : ℂ)‖ *
        ‖u‖ ^ (-(3 / 2 : ℝ)) =
      ‖twoRegularPrefactor z - twoRegularSingularCoeff -
          twoRegularSingularCoeff * u -
            (twoRegularSingularCoeff / 4) * u ^ 2‖ *
        ‖u‖ ^ (-(2 : ℝ))
  rw [← hpow_half, ← hpow_three_half]
  rw [show (twoRegularPrefactor z * u ^ (-(1 / 2 : ℂ)) -
          twoRegularSingularCoeff * u ^ (-(1 / 2 : ℂ))) -
        twoRegularSingularCoeff * (u * u ^ (-(1 / 2 : ℂ))) -
          (twoRegularSingularCoeff / 4) * (u ^ 2 * u ^ (-(1 / 2 : ℂ))) =
      (twoRegularPrefactor z - twoRegularSingularCoeff -
          twoRegularSingularCoeff * u -
            (twoRegularSingularCoeff / 4) * u ^ 2) *
        u ^ (-(1 / 2 : ℂ)) by ring]
  rw [norm_mul, hpow_norm]
  have hmul : ‖u‖ ^ (-(1 / 2 : ℝ)) * ‖u‖ ^ (-(3 / 2 : ℝ)) =
      ‖u‖ ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add hu_norm_pos]
    norm_num
  rw [mul_assoc, hmul]

lemma tendsto_twoRegular_remainder_singularity :
    Tendsto
      (fun z : ℂ =>
        ‖(twoRegularEGFFun z -
              twoRegularSingularCoeff * (1 - z) ^ (-(1 / 2 : ℂ))) -
            twoRegularSingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
              (twoRegularSingularCoeff / 4) * (1 - z) ^ (3 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(3 / 2 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  refine tendsto_twoRegularPrefactor_threeTerm.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (twoRegular_remainder_singularity_norm_eq hz.2.1).symm

lemma twoRegular_remainder_transfer_complex_thirdOrder :
    (fun n : ℕ =>
      (twoRegularEGFSeriesℂ - twoRegularSingularCoeff • twoRegularInvSqrtSeriesℂ).coeff n -
        twoRegularRemainderThirdModel n)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  let f : ℂ → ℂ := fun z =>
    twoRegularEGFFun z -
      twoRegularSingularCoeff * (1 - z) ^ (-(1 / 2 : ℂ))
  have hp : HasFPowerSeriesAt f
      (twoRegularEGFSeriesℂ - twoRegularSingularCoeff • twoRegularInvSqrtSeriesℂ)
      (0 : ℂ) := by
    have hsub := twoRegularEGFFun_hasFPowerSeriesAt_zero.sub
      (twoRegularInvSqrt_hasFPowerSeriesAt_zero.const_smul (c := twoRegularSingularCoeff))
    simpa [f, smul_eq_mul] using hsub
  have hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
    have hφπ : Real.pi / 4 < Real.pi := by nlinarith [Real.pi_pos]
    simpa [f] using
      (analyticOnNhd_twoRegularEGFFun (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
        (by positivity) hφπ).sub
        ((analyticOnNhd_twoRegularInvSqrt (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
          (by positivity) hφπ).const_smul (c := twoRegularSingularCoeff))
  have htransfer := transfer_twoTerm_secondOrder_general
    (α := (-(1 / 2 : ℝ))) (C0 := twoRegularSingularCoeff)
    (C1 := twoRegularSingularCoeff / 4)
    (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
    (f := f)
    (p := twoRegularEGFSeriesℂ - twoRegularSingularCoeff • twoRegularInvSqrtSeriesℂ)
    twoRegular_not_pole_neg_half (by norm_num) (by positivity)
    (by nlinarith [Real.pi_pos]) hp hΔ ?_
  · refine htransfer.congr' ?_ ?_
    · refine Eventually.of_forall fun n => ?_
      unfold twoRegularRemainderThirdModel
      norm_num
      ring
    · refine Eventually.of_forall fun n => ?_
      norm_num
  · convert tendsto_twoRegular_remainder_singularity using 1
    ext z
    norm_num [f]

lemma twoRegular_invSqrt_model_thirdOrder :
    (fun n : ℕ =>
      twoRegularSingularCoeff * twoRegularInvSqrtSeriesℂ.coeff n -
        twoRegularSingularCoeff * ((twoRegularInvSqrtThirdModel n : ℝ) : ℂ))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  have hmodelO := modelCoeff_thirdOrder (α := (1 / 2 : ℝ)) (by norm_num)
  have htail : (fun n : ℕ => (n : ℝ) ^ ((1 / 2 : ℝ) - 4))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
    convert rpow_sub_one_isLittleO_p2m2 (-(5 / 2 : ℝ)) using 1
    ext n
    congr 1
    norm_num
  have hmodel := hmodelO.trans_isLittleO htail
  have hcomplex := (ofReal_isLittleO_p2m3 hmodel).const_mul_left twoRegularSingularCoeff
  refine hcomplex.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  have hpow0 : (n : ℝ) ^ ((1 / 2 : ℝ) - 1) =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    congr 1
    norm_num
  have hpow1 : (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ)⁻¹ =
      (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have hinv : (n : ℝ)⁻¹ = (n : ℝ) ^ (-(1 : ℝ)) := by
      rw [Real.rpow_neg hnpos.le, Real.rpow_one]
    calc
      (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ)⁻¹ =
          (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 : ℝ)) := by rw [hinv]
      _ = (n : ℝ) ^ (-(1 / 2 : ℝ) + -(1 : ℝ)) := by rw [← Real.rpow_add hnpos]
      _ = (n : ℝ) ^ (-(3 / 2 : ℝ)) := by ring_nf
  have hpow2 : (n : ℝ) ^ (-(1 / 2 : ℝ)) * ((n : ℝ)⁻¹) ^ 2 =
      (n : ℝ) ^ (-(5 / 2 : ℝ)) := by
    have hinv2 : ((n : ℝ)⁻¹) ^ 2 = (n : ℝ) ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg hnpos.le]
      norm_num
    calc
      (n : ℝ) ^ (-(1 / 2 : ℝ)) * ((n : ℝ)⁻¹) ^ 2 =
          (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(2 : ℝ)) := by rw [hinv2]
      _ = (n : ℝ) ^ (-(1 / 2 : ℝ) + -(2 : ℝ)) := by rw [← Real.rpow_add hnpos]
      _ = (n : ℝ) ^ (-(5 / 2 : ℝ)) := by ring_nf
  have hpow1' : (n : ℝ) ^ (-1 / 2 : ℝ) * (n : ℝ)⁻¹ =
      (n : ℝ) ^ (-3 / 2 : ℝ) := by
    convert hpow1 using 2 <;> norm_num
  have hpow2' : (n : ℝ) ^ (-1 / 2 : ℝ) * ((n : ℝ)⁻¹) ^ 2 =
      (n : ℝ) ^ (-5 / 2 : ℝ) := by
    convert hpow2 using 2 <;> norm_num
  have hraw :
      ((n : ℝ) ^ ((1 / 2 : ℝ) - 1) / Real.Gamma (1 / 2 : ℝ)) *
          (1 + ((1 / 2 : ℝ) * ((1 / 2 : ℝ) - 1) / 2) * (n : ℝ)⁻¹ +
            ((1 / 2 : ℝ) * ((1 / 2 : ℝ) - 1) * ((1 / 2 : ℝ) - 2) *
                (3 * (1 / 2 : ℝ) - 1) / 24) * ((n : ℝ)⁻¹) ^ 2) =
        twoRegularInvSqrtThirdModel n := by
    unfold twoRegularInvSqrtThirdModel
    rw [hpow0]
    norm_num
    ring_nf
    rw [
      show (n : ℝ) ^ (-1 / 2 : ℝ) * (Real.Gamma (1 / 2 : ℝ))⁻¹ * (n : ℝ)⁻¹ =
          (Real.Gamma (1 / 2 : ℝ))⁻¹ * (n : ℝ) ^ (-3 / 2 : ℝ) by
        rw [← hpow1']
        ring,
      show (n : ℝ) ^ (-1 / 2 : ℝ) * (Real.Gamma (1 / 2 : ℝ))⁻¹ *
            ((n : ℝ)⁻¹) ^ 2 =
          (Real.Gamma (1 / 2 : ℝ))⁻¹ * (n : ℝ) ^ (-5 / 2 : ℝ) by
        rw [← hpow2']
        ring]
  unfold twoRegularInvSqrtSeriesℂ
  rw [FormalMultilinearSeries.coeff_ofScalars]
  have hchoose :
      Ring.choose ((1 / 2 : ℂ) + (n : ℕ) - 1) n =
        ((Ring.choose ((1 / 2 : ℝ) + (n : ℕ) - 1) n : ℝ) : ℂ) := by
    simpa using choose_ofReal_model (1 / 2 : ℝ) n
  rw [hchoose]
  rw [hraw]
  rw [Complex.ofReal_sub]
  ring

lemma twoRegular_thirdOrder_model_complex_eq (n : ℕ) :
    twoRegularSingularCoeff * ((twoRegularInvSqrtThirdModel n : ℝ) : ℂ) +
        twoRegularRemainderThirdModel n =
      ((twoRegularAsymptoticConstant * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
          twoRegularSecondConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            twoRegularThirdConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) := by
  unfold twoRegularInvSqrtThirdModel twoRegularRemainderThirdModel
    twoRegularThirdConstant twoRegularSecondConstant twoRegularAsymptoticConstant
    twoRegularSingularCoeff
  rw [Real.Gamma_one_half_eq, twoRegular_Gamma_neg_half,
    show (-(1 / 2 : ℝ)) - 1 = -(3 / 2 : ℝ) by norm_num,
    twoRegular_Gamma_neg_three_halves]
  norm_num [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_sub]
  ring

lemma twoRegular_transfer_complex_thirdOrder :
    (fun n : ℕ =>
      twoRegularEGFSeriesℂ.coeff n -
        ((twoRegularAsymptoticConstant * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
          twoRegularSecondConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            twoRegularThirdConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  have hsum := twoRegular_invSqrt_model_thirdOrder.add
    twoRegular_remainder_transfer_complex_thirdOrder
  refine hsum.congr_left ?_
  intro n
  rw [coeff_sub_const_smul_p2m2]
  rw [← twoRegular_thirdOrder_model_complex_eq n]
  ring

theorem twoRegularEGFCoeff_thirdOrder :
    (fun n : ℕ =>
      twoRegularEGFCoeff n -
        (twoRegularAsymptoticConstant * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
          twoRegularSecondConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            twoRegularThirdConstant * (n : ℝ) ^ (-(5 / 2 : ℝ))))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  exact complex_re_isLittleO_ofReal twoRegular_transfer_complex_thirdOrder

theorem twoRegularGraphCount_div_factorial_thirdOrder :
    (fun n : ℕ =>
      twoRegularGraphCount n / (n.factorial : ℝ) -
        (twoRegularAsymptoticConstant * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
          twoRegularSecondConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            twoRegularThirdConstant * (n : ℝ) ^ (-(5 / 2 : ℝ))))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  refine twoRegularEGFCoeff_thirdOrder.congr_left ?_
  intro n
  rw [twoRegularGraphCount_div_factorial]

end

open TwoRegularClass
set_option maxHeartbeats 1200000
open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries
theorem solution :
    (fun n : ℕ =>
      (twoRegularClass.counts n : ℝ) / (n.factorial : ℝ) -
        (twoRegularAsymptoticConstant * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
          twoRegularSecondConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            twoRegularThirdConstant * (n : ℝ) ^ (-(5 / 2 : ℝ))))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  refine twoRegularGraphCount_div_factorial_thirdOrder.congr_left ?_
  intro n
  rw [twoRegularClass_counts_eq_twoRegularGraphCount n]
