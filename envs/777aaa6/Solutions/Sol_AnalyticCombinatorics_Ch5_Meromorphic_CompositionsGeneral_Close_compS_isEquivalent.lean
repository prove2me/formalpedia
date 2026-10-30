-- Prove2me | solution 1 for AnalyticCombinatorics.Ch5.Meromorphic.CompositionsGeneral.Close.compS_isEquivalent
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-25T15:35:46.47814+00:00
-- url     : https://prove2.me/submissions/7cf66f12-3e5c-4895-b353-cefcb7fbee83

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SubstComp
import Definitions.Def_AnalyticCombinatorics_Ch5_Meromorphic_SupercriticalSeqGenuine
import Definitions.Def_AnalyticCombinatorics_Ch5_Meromorphic_CompositionsGeneral
import Definitions.Def_AnalyticCombinatorics_Ch5_Meromorphic_CompositionsGeneralClose
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Card

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

private lemma inv_lt_inv_of_pos_lt {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    y⁻¹ < x⁻¹ := by
  simpa [one_div] using one_div_lt_one_div_of_lt hx hxy

private lemma inv_radius_pow_isLittleO_simplePole
    {ρ c : ℂ} {R : ℝ}
    (hρ : 0 < ‖ρ‖) (hρR : ‖ρ‖ < R) (hc : c ≠ 0) :
    (fun n : ℕ => R⁻¹ ^ n : ℕ → ℝ) =o[atTop]
      (fun n : ℕ => c * ρ⁻¹ ^ (n + 1)) := by
  have hR : 0 < R := hρ.trans hρR
  have hinv_lt : R⁻¹ < ‖ρ‖⁻¹ :=
    inv_lt_inv_of_pos_lt hρ hρR
  have hpowLittle :
      (fun n : ℕ => R⁻¹ ^ n : ℕ → ℝ) =o[atTop]
        (fun n : ℕ => ‖ρ‖⁻¹ ^ n : ℕ → ℝ) :=
    isLittleO_pow_pow_of_lt_left (inv_nonneg.mpr hR.le) hinv_lt
  have hcnorm : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hρnorm : ‖ρ‖ ≠ 0 := ne_of_gt hρ
  have hpowOmain :
      (fun n : ℕ => ‖ρ‖⁻¹ ^ n : ℕ → ℝ) =O[atTop]
        (fun n : ℕ => c * ρ⁻¹ ^ (n + 1)) := by
    refine isBigO_of_le' (l := atTop) (c := (‖c‖ * ‖ρ‖⁻¹)⁻¹) ?_
    intro n
    have hbase_nonneg : 0 ≤ ‖ρ‖⁻¹ := inv_nonneg.mpr (norm_nonneg ρ)
    have hpow_nonneg : 0 ≤ ‖ρ‖⁻¹ ^ n := pow_nonneg hbase_nonneg n
    rw [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg]
    apply le_of_eq
    calc
      ‖ρ‖⁻¹ ^ n =
          (‖c‖ * ‖ρ‖⁻¹)⁻¹ * (‖c‖ * (‖ρ‖⁻¹ ^ (n + 1))) := by
        rw [pow_succ]
        field_simp [hcnorm, hρnorm]
      _ = (‖c‖ * ‖ρ‖⁻¹)⁻¹ * ‖c * ρ⁻¹ ^ (n + 1)‖ := by
        rw [norm_mul, norm_pow, norm_inv]
  exact hpowLittle.trans_isBigO hpowOmain

/-- The single-pole principal part with pole at `ρ` has coefficients
`c * (ρ⁻¹)^(n+1)`, matching the normalization of
`PowerSeries.coeff_simplePoleSum`. -/
theorem single_simplePole_principal_isEquivalent
    {ρ c : ℂ} :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n
      (PowerSeries.C (c * ρ⁻¹) *
        PowerSeries.rescale ρ⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ)))) ~[atTop]
      (fun n : ℕ => c * ρ⁻¹ ^ (n + 1)) := by
  apply Filter.EventuallyEq.isEquivalent
  exact Eventually.of_forall fun n => by
    calc
      PowerSeries.coeff (R := ℂ) n
          (PowerSeries.C (c * ρ⁻¹) *
            PowerSeries.rescale ρ⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ))) =
          (c * ρ⁻¹) * ρ⁻¹ ^ n := by
        rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale_invUnitsSub_one]
      _ = c * ρ⁻¹ ^ (n + 1) := by
        rw [pow_succ]
        ring

/-- Dominant simple pole transfer: a single simple pole at `ρ` plus a remainder analytic past `R`
has coefficients asymptotic to the pole contribution. -/
theorem dominant_simplePole_isEquivalent
    (f g : PowerSeries ℂ) {ρ c : ℂ} {R : ℝ}
    (hρ : 0 < ‖ρ‖) (hρR : ‖ρ‖ < R) (hc : c ≠ 0)
    (hgR : ENNReal.ofReal R < (PowerSeries.toFMLS g).radius)
    (hfg :
      f =
        PowerSeries.C (c * ρ⁻¹) *
          PowerSeries.rescale ρ⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ)) + g) :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n f) ~[atTop]
      (fun n : ℕ => c * ρ⁻¹ ^ (n + 1)) := by
  let S : PowerSeries ℂ :=
    PowerSeries.C (c * ρ⁻¹) *
      PowerSeries.rescale ρ⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ))
  have hR : 0 < R := hρ.trans hρR
  have hremO :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n f -
        PowerSeries.coeff (R := ℂ) n S) =O[atTop] (fun n : ℕ => R⁻¹ ^ n) :=
    coeff_sub_principalPart_isBigO_of_remainder_radius f S g hR hgR hfg
  have hgeom :
      (fun n : ℕ => R⁻¹ ^ n : ℕ → ℝ) =o[atTop]
        (fun n : ℕ => c * ρ⁻¹ ^ (n + 1)) :=
    inv_radius_pow_isLittleO_simplePole hρ hρR hc
  have hremLittle :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n f -
        PowerSeries.coeff (R := ℂ) n S) =o[atTop]
        (fun n : ℕ => c * ρ⁻¹ ^ (n + 1)) :=
    hremO.trans_isLittleO hgeom
  have hS :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n S) ~[atTop]
        (fun n : ℕ => c * ρ⁻¹ ^ (n + 1)) := by
    simpa [S] using single_simplePole_principal_isEquivalent
      (ρ := ρ) (c := c)
  have hsum :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n S +
        (PowerSeries.coeff (R := ℂ) n f - PowerSeries.coeff (R := ℂ) n S)) ~[atTop]
        (fun n : ℕ => c * ρ⁻¹ ^ (n + 1)) :=
    hS.add_isLittleO hremLittle
  exact hsum.congr_left (Eventually.of_forall fun n => by ring)

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

lemma shiftedC_hasFPowerSeriesAt_zero
    {Cfun : ℂ → ℂ} {ρ : ℂ} (hC : AnalyticAt ℂ Cfun ρ) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (shiftedC Cfun ρ) p 0 := by
  rcases hC with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  have hp' : HasFPowerSeriesAt (fun z : ℂ => Cfun (z + ρ)) p (0 : ℂ) := by
    simpa using hp.comp_sub (-ρ)
  exact hp'.congr (Eventually.of_forall fun z => by
    simp [shiftedC, add_comm])

lemma cdiv_hasFPowerSeriesAt_zero
    {Cfun : ℂ → ℂ} {ρ : ℂ} (hC : AnalyticAt ℂ Cfun ρ) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (cdiv Cfun ρ) p 0 := by
  rcases shiftedC_hasFPowerSeriesAt_zero (Cfun := Cfun) (ρ := ρ) hC with ⟨p, hp⟩
  exact ⟨p.fslope, by simpa [cdiv] using hp.has_fpower_series_dslope_fslope⟩

lemma cdiv_analyticAt_zero
    {Cfun : ℂ → ℂ} {ρ : ℂ} (hC : AnalyticAt ℂ Cfun ρ) :
    AnalyticAt ℂ (cdiv Cfun ρ) 0 := by
  rcases cdiv_hasFPowerSeriesAt_zero (Cfun := Cfun) (ρ := ρ) hC with ⟨p, hp⟩
  exact ⟨p, hp⟩

lemma shiftedC_hasDerivAt_zero
    {Cfun : ℂ → ℂ} {ρ Cderiv : ℂ}
    (hderiv : HasDerivAt Cfun Cderiv ρ) :
    HasDerivAt (shiftedC Cfun ρ) Cderiv 0 := by
  have h' : HasDerivAt Cfun Cderiv (ρ + 0) := by
    simpa using hderiv
  have hshift := h'.comp_const_add ρ (0 : ℂ)
  simpa [shiftedC] using hshift

lemma cdiv_zero
    {Cfun : ℂ → ℂ} {ρ Cderiv : ℂ}
    (hderiv : HasDerivAt Cfun Cderiv ρ) :
    cdiv Cfun ρ 0 = Cderiv := by
  rw [cdiv, dslope_same]
  exact (shiftedC_hasDerivAt_zero (Cfun := Cfun) (ρ := ρ) hderiv).deriv

lemma cdiv_shift_eq
    {Cfun : ℂ → ℂ} {ρ Cρ w : ℂ} (hCρ : Cfun ρ = Cρ) :
    Cfun (ρ + w) = Cρ + w * cdiv Cfun ρ w := by
  have h := sub_smul_dslope (shiftedC Cfun ρ) (0 : ℂ) w
  change (w - 0) • cdiv Cfun ρ w = shiftedC Cfun ρ w - shiftedC Cfun ρ 0 at h
  have h' : w * cdiv Cfun ρ w = Cfun (ρ + w) - Cρ := by
    simpa [shiftedC, hCρ, smul_eq_mul] using h
  calc
    Cfun (ρ + w) = Cρ + (Cfun (ρ + w) - Cρ) := by ring
    _ = Cρ + w * cdiv Cfun ρ w := by rw [← h']

lemma cdiv_analyticAt_of_ne
    {Cfun : ℂ → ℂ} {ρ w : ℂ} (hw : w ≠ 0)
    (hCw : AnalyticAt ℂ Cfun (ρ + w)) :
    AnalyticAt ℂ (cdiv Cfun ρ) w := by
  have hmodel : AnalyticAt ℂ
      (fun u : ℂ => u⁻¹ * (Cfun (ρ + u) - Cfun ρ)) w := by
    have hshift : AnalyticAt ℂ (fun u : ℂ => ρ + u) w :=
      analyticAt_const.add analyticAt_id
    have hCshift : AnalyticAt ℂ (fun u : ℂ => Cfun (ρ + u)) w :=
      AnalyticAt.comp' (𝕜 := ℂ) (g := Cfun) (f := fun u : ℂ => ρ + u)
        (x := w) hCw hshift
    exact (analyticAt_id.inv hw).mul
      (hCshift.sub (analyticAt_const (𝕜 := ℂ) (v := Cfun ρ) (x := w)))
  refine hmodel.congr ?_
  exact (dslope_eventuallyEq_slope_of_ne (shiftedC Cfun ρ) hw).mono fun u hu => by
    simpa [cdiv, shiftedC, slope_def_module, smul_eq_mul] using hu.symm

lemma cdiv_analyticAt_of_shift
    {Cfun : ℂ → ℂ} {ρ w : ℂ}
    (hCρ : AnalyticAt ℂ Cfun ρ)
    (hCw : AnalyticAt ℂ Cfun (ρ + w)) :
    AnalyticAt ℂ (cdiv Cfun ρ) w := by
  by_cases hw : w = 0
  · simpa [hw] using cdiv_analyticAt_zero (Cfun := Cfun) (ρ := ρ) hCρ
  · exact cdiv_analyticAt_of_ne (Cfun := Cfun) (ρ := ρ) hw hCw

lemma cdivSlope_hasFPowerSeriesAt_zero
    {Cfun : ℂ → ℂ} {ρ : ℂ} (hC : AnalyticAt ℂ Cfun ρ) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (cdivSlope Cfun ρ) p 0 := by
  rcases cdiv_hasFPowerSeriesAt_zero (Cfun := Cfun) (ρ := ρ) hC with ⟨p, hp⟩
  exact ⟨p.fslope, by simpa [cdivSlope] using hp.has_fpower_series_dslope_fslope⟩

lemma cdivSlope_analyticAt_zero
    {Cfun : ℂ → ℂ} {ρ : ℂ} (hC : AnalyticAt ℂ Cfun ρ) :
    AnalyticAt ℂ (cdivSlope Cfun ρ) 0 := by
  rcases cdivSlope_hasFPowerSeriesAt_zero (Cfun := Cfun) (ρ := ρ) hC with ⟨p, hp⟩
  exact ⟨p, hp⟩

lemma cdiv_eq_deriv_add
    {Cfun : ℂ → ℂ} {ρ Cderiv w : ℂ}
    (hderiv : HasDerivAt Cfun Cderiv ρ) :
    cdiv Cfun ρ w = Cderiv + w * cdivSlope Cfun ρ w := by
  have h := sub_smul_dslope (cdiv Cfun ρ) (0 : ℂ) w
  change (w - 0) • cdivSlope Cfun ρ w =
    cdiv Cfun ρ w - cdiv Cfun ρ 0 at h
  rw [cdiv_zero (Cfun := Cfun) (ρ := ρ) hderiv] at h
  have h' : w * cdivSlope Cfun ρ w = cdiv Cfun ρ w - Cderiv := by
    simpa [smul_eq_mul] using h
  calc
    cdiv Cfun ρ w = Cderiv + (cdiv Cfun ρ w - Cderiv) := by ring
    _ = Cderiv + w * cdivSlope Cfun ρ w := by rw [← h']

lemma cdivSlope_analyticAt_of_ne
    {Cfun : ℂ → ℂ} {ρ Cderiv w : ℂ}
    (hCρ : AnalyticAt ℂ Cfun ρ)
    (hCw : AnalyticAt ℂ Cfun (ρ + w))
    (hderiv : HasDerivAt Cfun Cderiv ρ) (hw : w ≠ 0) :
    AnalyticAt ℂ (cdivSlope Cfun ρ) w := by
  have hmodel : AnalyticAt ℂ
      (fun u : ℂ => u⁻¹ * (cdiv Cfun ρ u - Cderiv)) w := by
    exact (analyticAt_id.inv hw).mul
      ((cdiv_analyticAt_of_shift (Cfun := Cfun) (ρ := ρ) hCρ hCw).sub
        (analyticAt_const (𝕜 := ℂ) (v := Cderiv) (x := w)))
  refine hmodel.congr ?_
  exact (dslope_eventuallyEq_slope_of_ne (cdiv Cfun ρ) hw).mono fun u hu => by
    simpa [cdivSlope, slope_def_module,
      cdiv_zero (Cfun := Cfun) (ρ := ρ) hderiv, smul_eq_mul] using hu.symm

lemma cdivSlope_analyticAt_of_shift
    {Cfun : ℂ → ℂ} {ρ Cderiv w : ℂ}
    (hCρ : AnalyticAt ℂ Cfun ρ)
    (hCw : AnalyticAt ℂ Cfun (ρ + w))
    (hderiv : HasDerivAt Cfun Cderiv ρ) :
    AnalyticAt ℂ (cdivSlope Cfun ρ) w := by
  by_cases hw : w = 0
  · simpa [hw] using cdivSlope_analyticAt_zero (Cfun := Cfun) (ρ := ρ) hCρ
  · exact cdivSlope_analyticAt_of_ne
      (Cfun := Cfun) (ρ := ρ) (Cderiv := Cderiv) hCρ hCw hderiv hw

lemma cdiv_ne_zero_of_ne
    {Cfun : ℂ → ℂ} {ρ z : ℂ}
    (hCρ : Cfun ρ = 1) (hden : 1 - Cfun z ≠ 0) :
    cdiv Cfun ρ (z - ρ) ≠ 0 := by
  intro hzero
  have hshift := cdiv_shift_eq (Cfun := Cfun) (ρ := ρ) (Cρ := 1)
    (w := z - ρ) hCρ
  have hzsplit : ρ + (z - ρ) = z := by ring
  rw [hzsplit, hzero, mul_zero, add_zero] at hshift
  apply hden
  rw [hshift]
  ring

lemma cdiv_ne_zero_at
    {Cfun : ℂ → ℂ} {ρ Cderiv z : ℂ}
    (hCρ : Cfun ρ = 1)
    (hderiv : HasDerivAt Cfun Cderiv ρ) (hCderiv_ne : Cderiv ≠ 0)
    (hden : z ≠ ρ → 1 - Cfun z ≠ 0) :
    cdiv Cfun ρ (z - ρ) ≠ 0 := by
  by_cases hz : z = ρ
  · simpa [hz] using cdiv_zero (Cfun := Cfun) (ρ := ρ) hderiv ▸ hCderiv_ne
  · exact cdiv_ne_zero_of_ne (Cfun := Cfun) (ρ := ρ) hCρ (hden hz)

lemma analyticAt_remainderFun
    {Cfun : ℂ → ℂ} {ρ Cderiv z : ℂ}
    (hCρ_value : Cfun ρ = 1)
    (hCρ : AnalyticAt ℂ Cfun ρ)
    (hCz : AnalyticAt ℂ Cfun z)
    (hderiv : HasDerivAt Cfun Cderiv ρ) (hCderiv_ne : Cderiv ≠ 0)
    (hden : z ≠ ρ → 1 - Cfun z ≠ 0) :
    AnalyticAt ℂ (remainderFun Cfun ρ Cderiv) z := by
  have hshift : AnalyticAt ℂ (fun y : ℂ => y - ρ) z :=
    analyticAt_id.sub (analyticAt_const (𝕜 := ℂ) (v := ρ) (x := z))
  have hCw : AnalyticAt ℂ Cfun (ρ + (z - ρ)) := by
    convert hCz using 1
    ring
  have hnum0 : AnalyticAt ℂ (cdivSlope Cfun ρ) (z - ρ) :=
    cdivSlope_analyticAt_of_shift
      (Cfun := Cfun) (ρ := ρ) (Cderiv := Cderiv) hCρ hCw hderiv
  have hden0 : AnalyticAt ℂ (cdiv Cfun ρ) (z - ρ) :=
    cdiv_analyticAt_of_shift (Cfun := Cfun) (ρ := ρ) hCρ hCw
  have hnum : AnalyticAt ℂ (fun y : ℂ => cdivSlope Cfun ρ (y - ρ)) z :=
    AnalyticAt.comp' (𝕜 := ℂ) (g := cdivSlope Cfun ρ)
      (f := fun y : ℂ => y - ρ) (x := z) hnum0 hshift
  have hden_cdiv : AnalyticAt ℂ (fun y : ℂ => cdiv Cfun ρ (y - ρ)) z :=
    AnalyticAt.comp' (𝕜 := ℂ) (g := cdiv Cfun ρ)
      (f := fun y : ℂ => y - ρ) (x := z) hden0 hshift
  have hconst : AnalyticAt ℂ (fun _ : ℂ => Cderiv) z :=
    analyticAt_const (𝕜 := ℂ) (v := Cderiv) (x := z)
  have hden_an : AnalyticAt ℂ
      (fun y : ℂ => Cderiv * cdiv Cfun ρ (y - ρ)) z :=
    hconst.mul hden_cdiv
  have hden_ne : Cderiv * cdiv Cfun ρ (z - ρ) ≠ 0 :=
    mul_ne_zero hCderiv_ne
      (cdiv_ne_zero_at (Cfun := Cfun) (ρ := ρ) (Cderiv := Cderiv)
        hCρ_value hderiv hCderiv_ne hden)
  change AnalyticAt ℂ
    (fun y : ℂ =>
      cdivSlope Cfun ρ (y - ρ) / (Cderiv * cdiv Cfun ρ (y - ρ))) z
  exact hnum.div hden_an hden_ne

theorem remainderFun_differentiableOn_closedBall
    {Cfun : ℂ → ℂ} {ρ Cderiv : ℂ} {S : ℝ}
    (hCρ_value : Cfun ρ = 1)
    (hCρ : AnalyticAt ℂ Cfun ρ)
    (hCan : ∀ z ∈ Metric.closedBall (0 : ℂ) S, AnalyticAt ℂ Cfun z)
    (hderiv : HasDerivAt Cfun Cderiv ρ) (hCderiv_ne : Cderiv ≠ 0)
    (hden : ∀ z ∈ Metric.closedBall (0 : ℂ) S, z ≠ ρ → 1 - Cfun z ≠ 0) :
    DifferentiableOn ℂ (remainderFun Cfun ρ Cderiv) (Metric.closedBall (0 : ℂ) S) := by
  intro z hz
  exact (analyticAt_remainderFun
    (Cfun := Cfun) (ρ := ρ) (Cderiv := Cderiv) (z := z)
    hCρ_value hCρ (hCan z hz) hderiv hCderiv_ne
    (fun hzρ => hden z hz hzρ)).differentiableAt.differentiableWithinAt

lemma remainderFun_eq_inv_sub_principal
    {Cfun : ℂ → ℂ} {ρ Cderiv z : ℂ}
    (hCρ : Cfun ρ = 1)
    (hderiv : HasDerivAt Cfun Cderiv ρ) (hCderiv_ne : Cderiv ≠ 0)
    (hz : z ≠ ρ) (hden : 1 - Cfun z ≠ 0) :
    remainderFun Cfun ρ Cderiv z =
      (1 - Cfun z)⁻¹ - Cderiv⁻¹ * (ρ - z)⁻¹ := by
  let w : ℂ := z - ρ
  let Sdiv : ℂ := cdiv Cfun ρ w
  let Tdiv : ℂ := cdivSlope Cfun ρ w
  let A : ℂ := Cderiv
  have hw : w ≠ 0 := by
    dsimp [w]
    exact sub_ne_zero.mpr hz
  have hS : Sdiv ≠ 0 := by
    dsimp [Sdiv, w]
    exact cdiv_ne_zero_of_ne (Cfun := Cfun) (ρ := ρ) hCρ hden
  have hA : A ≠ 0 := by simpa [A] using hCderiv_ne
  have hzsplit : ρ + w = z := by
    dsimp [w]
    ring
  have hCz : Cfun z = 1 + w * Sdiv := by
    rw [← hzsplit]
    simpa [Sdiv] using cdiv_shift_eq (Cfun := Cfun) (ρ := ρ) (Cρ := 1)
      (w := w) hCρ
  have hSrel : Sdiv = A + w * Tdiv := by
    simpa [Sdiv, Tdiv, A, w] using
      cdiv_eq_deriv_add (Cfun := Cfun) (ρ := ρ) (Cderiv := Cderiv) (w := z - ρ)
        hderiv
  have hrz : ρ - z = -w := by
    dsimp [w]
    ring
  rw [remainderFun]
  change Tdiv / (A * Sdiv) =
    (1 - Cfun z)⁻¹ - A⁻¹ * (ρ - z)⁻¹
  rw [hCz, hrz]
  field_simp [hw, hS, hA]
  rw [hSrel]
  ring

theorem inv_sub_principal_eventuallyEq_remainderFun_at_zero
    {Cfun : ℂ → ℂ} {ρ Cderiv : ℂ} {S : ℝ}
    (hρ : 0 < ‖ρ‖) (hρS : ‖ρ‖ < S)
    (hCρ : Cfun ρ = 1)
    (hderiv : HasDerivAt Cfun Cderiv ρ) (hCderiv_ne : Cderiv ≠ 0)
    (hden : ∀ z ∈ Metric.closedBall (0 : ℂ) S, z ≠ ρ → 1 - Cfun z ≠ 0) :
    (fun z : ℂ => (1 - Cfun z)⁻¹ - Cderiv⁻¹ * (ρ - z)⁻¹)
      =ᶠ[𝓝 (0 : ℂ)] remainderFun Cfun ρ Cderiv := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hρ] with z hzball
  have hz_norm : ‖z‖ < ‖ρ‖ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hzball
  have hz_closed : z ∈ Metric.closedBall (0 : ℂ) S := by
    have hzS : ‖z‖ ≤ S := (hz_norm.trans hρS).le
    simpa [Metric.mem_closedBall, dist_eq_norm] using hzS
  have hz_ne : z ≠ ρ := by
    intro h
    have hnorm : ‖z‖ = ‖ρ‖ := by rw [h]
    linarith
  exact (remainderFun_eq_inv_sub_principal
    (Cfun := Cfun) (ρ := ρ) (Cderiv := Cderiv) (z := z)
    hCρ hderiv hCderiv_ne hz_ne (hden z hz_closed hz_ne)).symm

lemma toFMLS_sub (f g : PowerSeries ℂ) :
    PowerSeries.toFMLS (f - g) = PowerSeries.toFMLS f - PowerSeries.toFMLS g := by
  ext n
  simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars]

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

theorem remainderFun_hasFPowerSeriesAt_zero
    (F : PowerSeries ℂ) {Cfun : ℂ → ℂ} {ρ Cderiv : ℂ} {S : ℝ}
    (hρ : 0 < ‖ρ‖) (hρS : ‖ρ‖ < S)
    (hCρ : Cfun ρ = 1)
    (hderiv : HasDerivAt Cfun Cderiv ρ) (hCderiv_ne : Cderiv ≠ 0)
    (hden : ∀ z ∈ Metric.closedBall (0 : ℂ) S, z ≠ ρ → 1 - Cfun z ≠ 0)
    (hF : HasFPowerSeriesAt (fun z : ℂ => (1 - Cfun z)⁻¹) (PowerSeries.toFMLS F) 0) :
    HasFPowerSeriesAt (remainderFun Cfun ρ Cderiv)
      (PowerSeries.toFMLS (F - principalSeries ρ Cderiv⁻¹)) 0 := by
  have hprincipal :
      HasFPowerSeriesAt (principalFun ρ Cderiv⁻¹)
        (PowerSeries.toFMLS (principalSeries ρ Cderiv⁻¹)) 0 :=
    principalFun_hasFPowerSeriesAt_zero (ρ := ρ) (c := Cderiv⁻¹) hρ
  have hsub := hF.sub hprincipal
  have hsub' : HasFPowerSeriesAt
      (fun z : ℂ => (1 - Cfun z)⁻¹ - Cderiv⁻¹ * (ρ - z)⁻¹)
      (PowerSeries.toFMLS (F - principalSeries ρ Cderiv⁻¹)) 0 := by
    simpa [toFMLS_sub, principalFun] using hsub
  exact hsub'.congr
    (inv_sub_principal_eventuallyEq_remainderFun_at_zero
      (Cfun := Cfun) (ρ := ρ) (Cderiv := Cderiv) (S := S)
      hρ hρS hCρ hderiv hCderiv_ne hden)

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

/-- Genuine supercritical-sequence decomposition: the principal-part-plus-remainder form follows
from the analytic supercritical data and the fact that `F` represents `1/(1-C)` at the origin.

The auxiliary radius `S` is the formalized "analytic on a neighborhood of the closed disk of
radius `R`" margin: differentiability on the larger closed disk gives
`ENNReal.ofReal R < radius`. -/
theorem supercriticalSeq_decomposition_from_supercritical_data
    (F : PowerSeries ℂ) {Cfun : ℂ → ℂ} {ρ Cderiv : ℂ} {R S : ℝ}
    (hρ : 0 < ‖ρ‖) (hρR : ‖ρ‖ < R) (hRS : R < S)
    (hCρ : Cfun ρ = 1)
    (hCan : ∀ z ∈ Metric.closedBall (0 : ℂ) S, AnalyticAt ℂ Cfun z)
    (hderiv : HasDerivAt Cfun Cderiv ρ) (hCderiv_ne : Cderiv ≠ 0)
    (hden : ∀ z ∈ Metric.closedBall (0 : ℂ) S, z ≠ ρ → 1 - Cfun z ≠ 0)
    (hF : HasFPowerSeriesAt (fun z : ℂ => (1 - Cfun z)⁻¹) (PowerSeries.toFMLS F) 0) :
    ∃ g : PowerSeries ℂ,
      HasFPowerSeriesAt (remainderFun Cfun ρ Cderiv) (PowerSeries.toFMLS g) 0 ∧
      ENNReal.ofReal R < (PowerSeries.toFMLS g).radius ∧
      F =
        PowerSeries.C (Cderiv⁻¹ * ρ⁻¹) *
          PowerSeries.rescale ρ⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ)) + g := by
  let g : PowerSeries ℂ := F - principalSeries ρ Cderiv⁻¹
  have hρS : ‖ρ‖ < S := hρR.trans hRS
  have hρ_closed : ρ ∈ Metric.closedBall (0 : ℂ) S := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hρS.le
  have hCρ_an : AnalyticAt ℂ Cfun ρ := hCan ρ hρ_closed
  have hg_has :
      HasFPowerSeriesAt (remainderFun Cfun ρ Cderiv) (PowerSeries.toFMLS g) 0 := by
    simpa [g] using
      remainderFun_hasFPowerSeriesAt_zero
        (F := F) (Cfun := Cfun) (ρ := ρ) (Cderiv := Cderiv) (S := S)
        hρ hρS hCρ hderiv hCderiv_ne hden hF
  have hg_diff :
      DifferentiableOn ℂ (remainderFun Cfun ρ Cderiv) (Metric.closedBall (0 : ℂ) S) :=
    remainderFun_differentiableOn_closedBall
      (Cfun := Cfun) (ρ := ρ) (Cderiv := Cderiv) (S := S)
      hCρ hCρ_an hCan hderiv hCderiv_ne hden
  have hS : 0 < S := hρ.trans hρS
  have hgR : ENNReal.ofReal R < (PowerSeries.toFMLS g).radius :=
    powerSeries_radius_gt_of_hasFPowerSeriesAt_differentiableOn_larger
      (G := g) (gfun := remainderFun Cfun ρ Cderiv) (R := R) (S := S)
      hS hRS hg_has hg_diff
  have hfg_principal : F = principalSeries ρ Cderiv⁻¹ + g := by
    set_option backward.isDefEq.respectTransparency false in
      simp [g]
  refine ⟨g, hg_has, hgR, ?_⟩
  simpa [principalSeries] using hfg_principal

end SupercriticalSeqGenuine
end Meromorphic
end Ch5
end AnalyticCombinatorics
end

/-!
# General finite-part-set compositions

This file develops the finite-alphabet composition model
`1 / (1 - ∑ s ∈ S, z^s)` for a finite nonempty set of positive parts.
-/

open Complex Filter Asymptotics
open scoped BigOperators ComplexOrder ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic
namespace CompositionsGeneral

namespace CompList

variable {S : Finset ℕ} {n : ℕ}

end CompList

@[simp] lemma coeff_compSeriesℂ (S : Finset ℕ) (h0 : 0 ∉ S) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (compSeriesℂ S h0) = (compS S h0 n : ℂ) := by
  simp [compSeriesℂ]

lemma partPoly_complex_ofReal (S : Finset ℕ) (x : ℝ) :
    partPoly ℂ S (x : ℂ) = (partPoly ℝ S x : ℂ) := by
  simp [partPoly]

lemma partPoly_monoOn_nonneg (S : Finset ℕ) :
    MonotoneOn (partPoly ℝ S) (Set.Ici 0) := by
  intro x hx y hy hxy
  dsimp [partPoly]
  exact Finset.sum_le_sum fun s _ => pow_le_pow_left₀ hx hxy s

lemma partPoly_strictMonoOn_nonneg {S : Finset ℕ} (hS : S.Nonempty) (h0 : 0 ∉ S) :
    StrictMonoOn (partPoly ℝ S) (Set.Ici 0) := by
  intro x hx y hy hxy
  classical
  rcases hS with ⟨s, hs⟩
  have hspos : s ≠ 0 := fun hs0 => h0 (by simpa [hs0] using hs)
  have hle_all : ∀ t ∈ S, x ^ t ≤ y ^ t :=
    fun t _ => pow_le_pow_left₀ hx hxy.le t
  have hlt_s : x ^ s < y ^ s :=
    pow_lt_pow_left₀ hxy hx hspos
  dsimp [partPoly]
  exact Finset.sum_lt_sum hle_all ⟨s, hs, hlt_s⟩

theorem compS_zero (S : Finset ℕ) (h0 : 0 ∉ S) :
    compS S h0 0 = 1 := by
  rw [compS]
  letI : Fintype (CompList S 0) := CompList.instFintype S 0 h0
  calc
    Fintype.card (CompList S 0) = Fintype.card Unit :=
      Fintype.card_congr (compListZeroEquivPUnit S h0)
    _ = 1 := by simp

theorem compS_succ_eq_sum_subtype (S : Finset ℕ) (h0 : 0 ∉ S) (n : ℕ) :
    compS S h0 (n + 1) =
      ∑ s : {s : ℕ // s ∈ S ∧ s ≤ n + 1}, compS S h0 (n + 1 - s.1) := by
  rw [compS]
  letI : Fintype (CompList S (n + 1)) := CompList.instFintype S (n + 1) h0
  letI : Fintype {s : ℕ // s ∈ S ∧ s ≤ n + 1} := instFintypePartLe S (n + 1)
  letI : ∀ s : {s : ℕ // s ∈ S ∧ s ≤ n + 1},
      Fintype (CompList S (n + 1 - s.1)) :=
    fun s => CompList.instFintype S (n + 1 - s.1) h0
  letI : Fintype (firstPartCodomain S n) := by
    unfold firstPartCodomain
    infer_instance
  have hcard :
      Fintype.card (CompList S (n + 1)) = Fintype.card (firstPartCodomain S n) :=
    Fintype.card_congr (compListSuccEquivSigma S n)
  rw [hcard]
  unfold firstPartCodomain
  change Fintype.card (Sigma (fun s : {s : ℕ // s ∈ S ∧ s ≤ n + 1} =>
      CompList S (n + 1 - s.1))) =
    ∑ s : {s : ℕ // s ∈ S ∧ s ≤ n + 1}, compS S h0 (n + 1 - s.1)
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro s _hs
  rw [compS]

lemma rhoS_pos {S : Finset ℕ} (hcard : 2 ≤ S.card) (h0 : 0 ∉ S) :
    0 < rhoS S hcard h0 :=
  (Classical.choose_spec (exists_partPoly_eq_one (S := S) hcard h0)).1

lemma partPoly_rhoS {S : Finset ℕ} (hcard : 2 ≤ S.card) (h0 : 0 ∉ S) :
    partPoly ℝ S (rhoS S hcard h0) = 1 :=
  (Classical.choose_spec (exists_partPoly_eq_one (S := S) hcard h0)).2.2

theorem partPoly_eq_one_unique_on_nonneg {S : Finset ℕ}
    (hcard : 2 ≤ S.card) (h0 : 0 ∉ S) {x : ℝ} (hx : 0 ≤ x)
    (hxone : partPoly ℝ S x = 1) :
    x = rhoS S hcard h0 := by
  classical
  have hS : S.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (by norm_num : 0 < 2) hcard)
  have hstrict := partPoly_strictMonoOn_nonneg (S := S) hS h0
  have hρnonneg : 0 ≤ rhoS S hcard h0 := (rhoS_pos hcard h0).le
  by_cases hlt : x < rhoS S hcard h0
  · have := hstrict hx hρnonneg hlt
    rw [hxone, partPoly_rhoS hcard h0] at this
    exact (lt_irrefl (1 : ℝ) this).elim
  · have hρle : rhoS S hcard h0 ≤ x := le_of_not_gt hlt
    by_cases hgt : rhoS S hcard h0 < x
    · have := hstrict hρnonneg hx hgt
      rw [hxone, partPoly_rhoS hcard h0] at this
      exact (lt_irrefl (1 : ℝ) this).elim
    · exact le_antisymm (le_of_not_gt hgt) hρle

lemma norm_partPoly_le_partPoly_norm (S : Finset ℕ) (z : ℂ) :
    ‖partPoly ℂ S z‖ ≤ partPoly ℝ S ‖z‖ := by
  classical
  calc
    ‖partPoly ℂ S z‖ = ‖∑ s ∈ S, z ^ s‖ := rfl
    _ ≤ ∑ s ∈ S, ‖z ^ s‖ := norm_sum_le S (fun s => z ^ s)
    _ = partPoly ℝ S ‖z‖ := by
      simp [partPoly, norm_pow]

theorem root_norm_eq_rhoS {S : Finset ℕ} (hcard : 2 ≤ S.card) (h0 : 0 ∉ S)
    {z : ℂ} (hroot : 1 - partPoly ℂ S z = 0)
    (hzle : ‖z‖ ≤ rhoS S hcard h0) :
    ‖z‖ = rhoS S hcard h0 := by
  classical
  have hP : partPoly ℂ S z = 1 := (sub_eq_zero.mp hroot).symm
  have hnormP : ‖partPoly ℂ S z‖ = 1 := by
    rw [hP, norm_one]
  have hleρ : partPoly ℝ S ‖z‖ ≤ partPoly ℝ S (rhoS S hcard h0) := by
    exact partPoly_monoOn_nonneg S (norm_nonneg z) (rhoS_pos hcard h0).le hzle
  have hle1 : partPoly ℝ S ‖z‖ ≤ 1 := by
    simpa [partPoly_rhoS hcard h0] using hleρ
  have hge1 : 1 ≤ partPoly ℝ S ‖z‖ := by
    rw [← hnormP]
    exact norm_partPoly_le_partPoly_norm S z
  have heq : partPoly ℝ S ‖z‖ = 1 := le_antisymm hle1 hge1
  exact partPoly_eq_one_unique_on_nonneg hcard h0 (norm_nonneg z) heq

lemma complex_eq_of_nonneg (w : ℂ) (hw : 0 ≤ w) :
    w = (‖w‖ : ℝ) := by
  apply Complex.ext
  · exact Complex.re_eq_norm.mpr hw
  · exact (Complex.nonneg_iff.mp hw).2.symm.trans (by simp)

theorem root_powers_nonneg {S : Finset ℕ} (hcard : 2 ≤ S.card) (h0 : 0 ∉ S)
    {z : ℂ} (hroot : 1 - partPoly ℂ S z = 0)
    (hzle : ‖z‖ ≤ rhoS S hcard h0) :
    ∀ s ∈ S, 0 ≤ z ^ s := by
  classical
  have hP : partPoly ℂ S z = 1 := (sub_eq_zero.mp hroot).symm
  have hnormz : ‖z‖ = rhoS S hcard h0 :=
    root_norm_eq_rhoS hcard h0 hroot hzle
  have hsum_norm : ∑ s ∈ S, ‖z ^ s‖ = 1 := by
    calc
      ∑ s ∈ S, ‖z ^ s‖ = partPoly ℝ S ‖z‖ := by
        simp [partPoly, norm_pow]
      _ = 1 := by
        rw [hnormz, partPoly_rhoS hcard h0]
  have hsum_re : ∑ s ∈ S, (z ^ s).re = 1 := by
    have hre := congrArg Complex.re hP
    simpa [partPoly] using hre
  have hsum_zero : ∑ s ∈ S, (‖z ^ s‖ - (z ^ s).re) = 0 := by
    rw [Finset.sum_sub_distrib, hsum_norm, hsum_re]
    ring
  have hnonneg : ∀ s ∈ S, 0 ≤ ‖z ^ s‖ - (z ^ s).re := by
    intro s hs
    exact sub_nonneg.mpr (Complex.re_le_norm (z ^ s))
  intro s hs
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum_zero s hs
  have hre_eq : (z ^ s).re = ‖z ^ s‖ := by linarith
  exact Complex.re_eq_norm.mp hre_eq

lemma pow_finset_gcd_eq_one (u : ℂ) (S : Finset ℕ) :
    u ^ (S.gcd id) = 1 ↔ ∀ s ∈ S, u ^ s = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp
  | insert a S ha ih =>
      rw [Finset.gcd_insert]
      change u ^ Nat.gcd (id a) (S.gcd id) = 1 ↔ ∀ s ∈ insert a S, u ^ s = 1
      rw [pow_gcd_eq_one, ih]
      constructor
      · intro h s hs
        rcases Finset.mem_insert.mp hs with rfl | hsS
        · exact h.1
        · exact h.2 s hsS
      · intro h
        constructor
        · exact h a (Finset.mem_insert_self a S)
        · intro s hs
          exact h s (Finset.mem_insert_of_mem hs)

theorem root_eq_rhoS_of_gcd {S : Finset ℕ} (hcard : 2 ≤ S.card) (h0 : 0 ∉ S)
    (hgcd : S.gcd id = 1) {z : ℂ}
    (hroot : 1 - partPoly ℂ S z = 0)
    (hzle : ‖z‖ ≤ rhoS S hcard h0) :
    z = (rhoS S hcard h0 : ℂ) := by
  classical
  let ρ : ℝ := rhoS S hcard h0
  have hρpos : 0 < ρ := rhoS_pos hcard h0
  have hρneℂ : ((ρ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hρpos
  have hnormz : ‖z‖ = ρ := by
    simpa [ρ] using root_norm_eq_rhoS hcard h0 hroot hzle
  have hpows_nonneg : ∀ s ∈ S, 0 ≤ z ^ s :=
    root_powers_nonneg hcard h0 hroot hzle
  have hpows_eq : ∀ s ∈ S, z ^ s = ((ρ ^ s : ℝ) : ℂ) := by
    intro s hs
    have hnonneg := hpows_nonneg s hs
    calc
      z ^ s = (‖z ^ s‖ : ℝ) := complex_eq_of_nonneg (z ^ s) hnonneg
      _ = ((ρ ^ s : ℝ) : ℂ) := by
        rw [norm_pow, hnormz]
  let u : ℂ := z / (ρ : ℂ)
  have hu_pows : ∀ s ∈ S, u ^ s = 1 := by
    intro s hs
    have hspos : s ≠ 0 := fun hs0 => h0 (by simpa [hs0] using hs)
    have hρpow_ne : ((ρ : ℂ) ^ s) ≠ 0 := pow_ne_zero s hρneℂ
    calc
      u ^ s = z ^ s / (ρ : ℂ) ^ s := by
        simp [u, div_pow]
      _ = 1 := by
        rw [hpows_eq s hs]
        norm_cast
        field_simp [hρpow_ne]
  have hu_gcd : u ^ (S.gcd id) = 1 :=
    (pow_finset_gcd_eq_one u S).2 hu_pows
  have hu : u = 1 := by
    rw [hgcd] at hu_gcd
    simpa using hu_gcd
  calc
    z = u * (ρ : ℂ) := by
      simp [u, hρneℂ]
    _ = (ρ : ℂ) := by
      rw [hu]
      ring

theorem compS_isEquivalent_of_dominant_decomposition
    (S : Finset ℕ) (hcard : 2 ≤ S.card) (h0 : 0 ∉ S)
    (g : PowerSeries ℂ) {R : ℝ}
    (hρR : ‖rhoSℂ S hcard h0‖ < R)
    (hderiv_ne : partPolyDerivAt S (rhoSℂ S hcard h0) ≠ 0)
    (hgR : ENNReal.ofReal R < (PowerSeries.toFMLS g).radius)
    (hdecomp :
      compSeriesℂ S h0 =
        PowerSeries.C (residueConstant S hcard h0 * (rhoSℂ S hcard h0)⁻¹) *
          PowerSeries.rescale (rhoSℂ S hcard h0)⁻¹
            (PowerSeries.invUnitsSub (1 : ℂˣ)) + g) :
    (fun n : ℕ => (compS S h0 n : ℂ)) ~[atTop]
      (fun n : ℕ =>
        compAsymptoticConstant S hcard h0 * (rhoSℂ S hcard h0)⁻¹ ^ n) := by
  classical
  have hρpos : 0 < ‖rhoSℂ S hcard h0‖ := by
    rw [rhoSℂ]
    rw [Complex.norm_of_nonneg (rhoS_pos hcard h0).le]
    exact rhoS_pos hcard h0
  have hc_ne : residueConstant S hcard h0 ≠ 0 := by
    exact inv_ne_zero hderiv_ne
  have hmain :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n (compSeriesℂ S h0)) ~[atTop]
        (fun n : ℕ =>
          residueConstant S hcard h0 * (rhoSℂ S hcard h0)⁻¹ ^ (n + 1)) :=
    dominant_simplePole_isEquivalent
      (compSeriesℂ S h0) g
      (ρ := rhoSℂ S hcard h0) (c := residueConstant S hcard h0) (R := R)
      hρpos hρR hc_ne hgR hdecomp
  have hcoeff :
      (fun n : ℕ => (compS S h0 n : ℂ)) =ᶠ[atTop]
        (fun n : ℕ => PowerSeries.coeff (R := ℂ) n (compSeriesℂ S h0)) :=
    Eventually.of_forall fun n => by simp [compSeriesℂ, compS]
  exact (hcoeff.trans_isEquivalent hmain).trans_eventuallyEq
    (Eventually.of_forall fun n => by
      rw [compAsymptoticConstant]
      change residueConstant S hcard h0 * (rhoSℂ S hcard h0)⁻¹ ^ (n + 1) =
        residueConstant S hcard h0 * (rhoSℂ S hcard h0)⁻¹ *
          (rhoSℂ S hcard h0)⁻¹ ^ n
      rw [pow_succ]
      ring)

end CompositionsGeneral
end Meromorphic
end Ch5
end AnalyticCombinatorics
end

/-!
# Closing the general finite-part composition family

This file supplies the formal OGF bridge, the derivative nonvanishing input, and the
dominant-pole decomposition needed by `CompositionsGeneral`.
-/

open Complex Filter Asymptotics
open scoped BigOperators ComplexOrder ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic
namespace CompositionsGeneral
namespace Close

lemma partSeriesℂ_eq (S : Finset ℕ) :
    partSeriesℂ S = ∑ s ∈ S, (PowerSeries.X : PowerSeries ℂ) ^ s := rfl

lemma compS_succ_eq_sum_filter (S : Finset ℕ) (h0 : 0 ∉ S) (n : ℕ) :
    compS S h0 (n + 1) =
      ∑ s ∈ S.filter (fun s => s ≤ n + 1), compS S h0 (n + 1 - s) := by
  classical
  rw [compS_succ_eq_sum_subtype S h0 n]
  let e :
      {s : ℕ // s ∈ S ∧ s ≤ n + 1} ≃
        {s : ℕ // s ∈ S.filter (fun s => s ≤ n + 1)} := by
    refine
      { toFun := ?_
        invFun := ?_
        left_inv := ?_
        right_inv := ?_ }
    · intro s
      exact (⟨s.1, Finset.mem_filter.mpr ⟨s.2.1, s.2.2⟩⟩ :
        {s : ℕ // s ∈ S.filter (fun s => s ≤ n + 1)})
    · intro s
      exact (⟨s.1, Finset.mem_filter.mp s.2⟩ :
        {s : ℕ // s ∈ S ∧ s ≤ n + 1})
    · intro s
      ext
      rfl
    · intro s
      ext
      rfl
  calc
    (∑ s : {s : ℕ // s ∈ S ∧ s ≤ n + 1}, compS S h0 (n + 1 - s.1)) =
        ∑ s : {s : ℕ // s ∈ S.filter (fun s => s ≤ n + 1)},
          compS S h0 (n + 1 - s.1) := by
      exact Fintype.sum_equiv e
        (fun s : {s : ℕ // s ∈ S ∧ s ≤ n + 1} => compS S h0 (n + 1 - s.1))
        (fun s : {s : ℕ // s ∈ S.filter (fun s => s ≤ n + 1)} =>
          compS S h0 (n + 1 - s.1))
        (by intro s; rfl)
    _ = ∑ s ∈ S.filter (fun s => s ≤ n + 1), compS S h0 (n + 1 - s) := by
      simpa using
        (Finset.sum_attach (S.filter (fun s => s ≤ n + 1))
          (fun s : ℕ => compS S h0 (n + 1 - s)))

lemma coeff_compSeriesℂ_mul_partSeriesℂ
    (S : Finset ℕ) (h0 : 0 ∉ S) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (compSeriesℂ S h0 * partSeriesℂ S) =
      ∑ s ∈ S.filter (fun s => s ≤ n), (compS S h0 (n - s) : ℂ) := by
  set_option backward.isDefEq.respectTransparency false in
    classical
    rw [partSeriesℂ, Finset.mul_sum]
    simp only [map_sum]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro s hs
    by_cases hsn : s ≤ n
    · simp [hsn, PowerSeries.coeff_mul_X_pow', coeff_compSeriesℂ]
    · simp [hsn, PowerSeries.coeff_mul_X_pow']

lemma constantCoeff_compSeriesℂ (S : Finset ℕ) (h0 : 0 ∉ S) :
    PowerSeries.constantCoeff (compSeriesℂ S h0) = 1 := by
  rw [compSeriesℂ, PowerSeries.constantCoeff_mk]
  exact_mod_cast compS_zero S h0

lemma coeff_zero_partSeriesℂ (S : Finset ℕ) (h0 : 0 ∉ S) :
    PowerSeries.coeff (R := ℂ) 0 (partSeriesℂ S) = 0 := by
  classical
  simp [partSeriesℂ, PowerSeries.coeff_X_pow, h0]

lemma constantCoeff_partSeriesℂ (S : Finset ℕ) (h0 : 0 ∉ S) :
    PowerSeries.constantCoeff (partSeriesℂ S) = 0 := by
  simpa [PowerSeries.constantCoeff] using coeff_zero_partSeriesℂ S h0

/-- Formal OGF identity for genuine `S`-composition counts. -/
theorem compSeriesℂ_mul_denominator (S : Finset ℕ) (h0 : 0 ∉ S) :
    compSeriesℂ S h0 *
      (1 - ∑ s ∈ S, (PowerSeries.X : PowerSeries ℂ) ^ s) = 1 := by
  set_option backward.isDefEq.respectTransparency false in
    classical
    rw [← partSeriesℂ_eq S]
    have hsplit :
        compSeriesℂ S h0 * (1 - partSeriesℂ S) =
          compSeriesℂ S h0 - compSeriesℂ S h0 * partSeriesℂ S := by
      ring
    rw [hsplit]
    ext n
    cases n with
    | zero =>
        simpa [constantCoeff_compSeriesℂ S h0] using constantCoeff_partSeriesℂ S h0
    | succ n =>
        simp only [map_sub, coeff_compSeriesℂ, coeff_compSeriesℂ_mul_partSeriesℂ,
          PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte]
        have hrecℕ := compS_succ_eq_sum_filter S h0 n
        have hrecℂ :
            (compS S h0 (n + 1) : ℂ) =
              ∑ s ∈ S.filter (fun s => s ≤ n + 1), (compS S h0 (n + 1 - s) : ℂ) := by
          exact_mod_cast hrecℕ
        exact sub_eq_zero.mpr hrecℂ

lemma denominator_constantCoeff_ne_zero (S : Finset ℕ) (h0 : 0 ∉ S) :
    PowerSeries.constantCoeff
      (1 - ∑ s ∈ S, (PowerSeries.X : PowerSeries ℂ) ^ s : PowerSeries ℂ) ≠ 0 := by
  rw [← partSeriesℂ_eq S]
  simp [constantCoeff_partSeriesℂ S h0]

/-- The genuine count series is the rational OGF. -/
theorem compSeriesℂ_eq_compOGFℂ (S : Finset ℕ) (h0 : 0 ∉ S) :
    compSeriesℂ S h0 = compOGFℂ S := by
  rw [compOGFℂ]
  exact (PowerSeries.eq_inv_iff_mul_eq_one (denominator_constantCoeff_ne_zero S h0)).2
    (compSeriesℂ_mul_denominator S h0)

lemma compOGFℂ_eq_geometric_subst (S : Finset ℕ) (h0 : 0 ∉ S) :
    compOGFℂ S = (PowerSeries.invUnitsSub (1 : ℂˣ)).subst (partSeriesℂ S) := by
  set_option backward.isDefEq.respectTransparency false in
    let H : PowerSeries ℂ := partSeriesℂ S
    have hH0 : PowerSeries.constantCoeff H = 0 := by
      simpa [H] using constantCoeff_partSeriesℂ S h0
    have hHas : PowerSeries.HasSubst H := PowerSeries.HasSubst.of_constantCoeff_zero hH0
    have hsubst : (PowerSeries.invUnitsSub (1 : ℂˣ)).subst H * (1 - H) = 1 := by
      have hsubHX :
          (PowerSeries.C ((1 : ℂˣ) : ℂ) - PowerSeries.X).subst H = 1 - H := by
        rw [← PowerSeries.coe_substAlgHom hHas, map_sub,
          PowerSeries.substAlgHom_X hHas]
        simp
      rw [← hsubHX, ← PowerSeries.subst_mul hHas, PowerSeries.invUnitsSub_mul_sub]
      change (PowerSeries.C (1 : ℂ)).subst H = 1
      rw [← PowerSeries.coe_substAlgHom hHas]
      simp
    rw [compOGFℂ]
    rw [← partSeriesℂ_eq S]
    change (1 - H)⁻¹ = (PowerSeries.invUnitsSub (1 : ℂˣ)).subst H
    have h0 : PowerSeries.constantCoeff (1 - H : PowerSeries ℂ) ≠ 0 := by
      simp [H, constantCoeff_partSeriesℂ S h0]
    exact ((PowerSeries.eq_inv_iff_mul_eq_one h0).2 hsubst).symm

lemma toFMLS_invUnitsSub_one :
    PowerSeries.toFMLS (PowerSeries.invUnitsSub (1 : ℂˣ)) =
      formalMultilinearSeries_geometric ℂ ℂ := by
  ext n
  simp [PowerSeries.toFMLS, formalMultilinearSeries_geometric_eq_ofScalars,
    FormalMultilinearSeries.ofScalars]

lemma toFMLS_add (f g : PowerSeries ℂ) :
    PowerSeries.toFMLS (f + g) = PowerSeries.toFMLS f + PowerSeries.toFMLS g := by
  change FormalMultilinearSeries.ofScalars ℂ
      (fun n => PowerSeries.coeff (R := ℂ) n (f + g)) =
    FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff (R := ℂ) n f) +
      FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff (R := ℂ) n g)
  rw [← FormalMultilinearSeries.ofScalars_add]
  congr

lemma toFMLS_finset_sum {ι : Type*} (s : Finset ι) (F : ι → PowerSeries ℂ) :
    PowerSeries.toFMLS (∑ i ∈ s, F i) =
      ∑ i ∈ s, PowerSeries.toFMLS (F i) := by
  set_option backward.isDefEq.respectTransparency false in
    classical
    induction s using Finset.induction_on with
    | empty =>
        change FormalMultilinearSeries.ofScalars ℂ (fun n => (0 : ℂ)) = 0
        exact FormalMultilinearSeries.ofScalars_series_eq_zero_of_scalar_zero ℂ ℂ
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, toFMLS_add, ih]

lemma hasFPowerSeriesAt_pow_toFMLS_X_pow (s : ℕ) :
    HasFPowerSeriesAt (fun z : ℂ => z ^ s)
      (PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ s)) (0 : ℂ) := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards with z
  let term : ℕ → ℂ :=
    fun n => z ^ n •
      (PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ s)).coeff n
  have hsingle : HasSum term (term s) := by
    apply hasSum_single
    intro n hn
    simp [term, PowerSeries.coeff_X_pow, hn]
  convert hsingle using 1
  simp [term, PowerSeries.toFMLS]

lemma partPoly_hasFPowerSeriesAt_zero (S : Finset ℕ) :
    HasFPowerSeriesAt (partPoly ℂ S)
      (PowerSeries.toFMLS (partSeriesℂ S)) (0 : ℂ) := by
  classical
  have hsum :
      HasFPowerSeriesAt (fun z : ℂ => ∑ s ∈ S, z ^ s)
        (∑ s ∈ S, PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ s)) (0 : ℂ) := by
    induction S using Finset.induction_on with
    | empty =>
        simpa using
          (hasFPowerSeriesAt_const (𝕜 := ℂ) (E := ℂ) (F := ℂ)
            (c := (0 : ℂ)) (e := (0 : ℂ)))
    | insert a S ha ih =>
        simpa [Finset.sum_insert ha] using
          (hasFPowerSeriesAt_pow_toFMLS_X_pow a).add ih
  have hFMLS :
      (∑ s ∈ S, PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ s)) =
        PowerSeries.toFMLS (partSeriesℂ S) := by
    rw [partSeriesℂ]
    exact (toFMLS_finset_sum S
      (fun s : ℕ => (PowerSeries.X : PowerSeries ℂ) ^ s)).symm
  simpa [partPoly, hFMLS]
    using hsum

theorem compSeriesℂ_hasFPowerSeriesAt_zero (S : Finset ℕ) (h0 : 0 ∉ S) :
    HasFPowerSeriesAt (fun z : ℂ => (1 - partPoly ℂ S z)⁻¹)
      (PowerSeries.toFMLS (compSeriesℂ S h0)) (0 : ℂ) := by
  have houter : HasFPowerSeriesAt (fun z : ℂ => (1 - z)⁻¹)
      (formalMultilinearSeries_geometric ℂ ℂ) (0 : ℂ) :=
    (hasFPowerSeriesOnBall_inv_one_sub ℂ ℂ).hasFPowerSeriesAt
  have houter' : HasFPowerSeriesAt (fun z : ℂ => (1 - z)⁻¹)
      (formalMultilinearSeries_geometric ℂ ℂ) (partPoly ℂ S 0) := by
    simpa [partPoly_zero_of_notMem_zero (R := ℂ) S h0] using houter
  have hcomp := houter'.comp (partPoly_hasFPowerSeriesAt_zero S)
  rw [compSeriesℂ_eq_compOGFℂ S h0, compOGFℂ_eq_geometric_subst S h0]
  rw [PowerSeries.toFMLS_subst_eq_comp (constantCoeff_partSeriesℂ S h0)]
  rw [toFMLS_invUnitsSub_one]
  exact hcomp

lemma partPoly_hasDerivAt (S : Finset ℕ) (ρ : ℂ) :
    HasDerivAt (partPoly ℂ S) (partPolyDerivAt S ρ) ρ := by
  classical
  change HasDerivAt (fun z : ℂ => ∑ s ∈ S, z ^ s)
    (∑ s ∈ S, (s : ℂ) * ρ ^ (s - 1)) ρ
  have h := HasDerivAt.sum (u := S)
    (fun s _hs => hasDerivAt_pow s ρ)
  convert h using 1
  funext z
  simp

lemma partPoly_analyticAt (S : Finset ℕ) (z : ℂ) :
    AnalyticAt ℂ (partPoly ℂ S) z := by
  classical
  unfold partPoly
  fun_prop

lemma partPoly_rhoSℂ (S : Finset ℕ) (hcard : 2 ≤ S.card) (h0 : 0 ∉ S) :
    partPoly ℂ S (rhoSℂ S hcard h0) = 1 := by
  rw [rhoSℂ, partPoly_complex_ofReal, partPoly_rhoS hcard h0]
  norm_num

theorem partPolyDerivAt_rhoSℂ_ne_zero
    (S : Finset ℕ) (hcard : 2 ≤ S.card) (h0 : 0 ∉ S) :
    partPolyDerivAt S (rhoSℂ S hcard h0) ≠ 0 := by
  classical
  let ρ : ℝ := rhoS S hcard h0
  have hρpos : 0 < ρ := rhoS_pos hcard h0
  have hSnonempty : S.Nonempty :=
    Finset.card_pos.mp (lt_of_lt_of_le (by norm_num : 0 < 2) hcard)
  have hterm_pos :
      ∀ s ∈ S, 0 < (s : ℝ) * ρ ^ (s - 1) := by
    intro s hs
    have hsposNat : 0 < s := Nat.pos_of_ne_zero fun hs0 => h0 (by simpa [hs0] using hs)
    have hspos : 0 < (s : ℝ) := by exact_mod_cast hsposNat
    exact mul_pos hspos (pow_pos hρpos (s - 1))
  have hsum_pos : 0 < ∑ s ∈ S, (s : ℝ) * ρ ^ (s - 1) :=
    Finset.sum_pos hterm_pos hSnonempty
  have hsum_ne : (∑ s ∈ S, (s : ℝ) * ρ ^ (s - 1)) ≠ 0 :=
    ne_of_gt hsum_pos
  have hcast :
      partPolyDerivAt S (rhoSℂ S hcard h0) =
        ((∑ s ∈ S, (s : ℝ) * ρ ^ (s - 1)) : ℂ) := by
    simp [partPolyDerivAt, rhoSℂ, ρ]
  rw [hcast]
  exact_mod_cast hsum_ne

lemma eval_denominatorPolynomial (S : Finset ℕ) (z : ℂ) :
    Polynomial.eval z (denominatorPolynomial S) = 1 - partPoly ℂ S z := by
  simp [denominatorPolynomial, partPoly, Polynomial.eval_finset_sum]

lemma denominatorPolynomial_ne_zero (S : Finset ℕ) (h0 : 0 ∉ S) :
    denominatorPolynomial S ≠ 0 := by
  intro h
  have heval := congrArg (fun p : Polynomial ℂ => Polynomial.eval 0 p) h
  have hleft : Polynomial.eval 0 (denominatorPolynomial S) = 1 := by
    rw [eval_denominatorPolynomial]
    simp [partPoly_zero_of_notMem_zero (R := ℂ) S h0]
  simp at heval
  rw [hleft] at heval
  exact one_ne_zero heval

lemma denominatorPolynomial_isRoot_iff (S : Finset ℕ) (z : ℂ) :
    Polynomial.IsRoot (denominatorPolynomial S) z ↔
      1 - partPoly ℂ S z = 0 := by
  simp [Polynomial.IsRoot, eval_denominatorPolynomial]

lemma roots_erase_rho_norm_gt
    (S : Finset ℕ) (hcard : 2 ≤ S.card) (h0 : 0 ∉ S)
    (hgcd : S.gcd id = 1) :
    ∀ z ∈ (denominatorPolynomial S).roots.toFinset.erase (rhoSℂ S hcard h0),
      rhoS S hcard h0 < ‖z‖ := by
  classical
  intro z hz
  have hzroots : z ∈ (denominatorPolynomial S).roots.toFinset :=
    (Finset.mem_erase.mp hz).2
  have hz_ne_rho : z ≠ rhoSℂ S hcard h0 :=
    (Finset.mem_erase.mp hz).1
  have hroot :
      1 - partPoly ℂ S z = 0 := by
    have hp : denominatorPolynomial S ≠ 0 := denominatorPolynomial_ne_zero S h0
    have hIsRoot : Polynomial.IsRoot (denominatorPolynomial S) z :=
      (Polynomial.mem_roots hp).mp (Multiset.mem_toFinset.mp hzroots)
    exact (denominatorPolynomial_isRoot_iff S z).mp hIsRoot
  by_contra hnot
  have hzle : ‖z‖ ≤ rhoS S hcard h0 := le_of_not_gt hnot
  have hzrho :
      z = rhoSℂ S hcard h0 := by
    simpa [rhoSℂ] using root_eq_rhoS_of_gcd hcard h0 hgcd hroot hzle
  exact hz_ne_rho hzrho

theorem exists_dominant_annulus
    (S : Finset ℕ) (hcard : 2 ≤ S.card) (h0 : 0 ∉ S)
    (hgcd : S.gcd id = 1) :
    ∃ R T : ℝ,
      ‖rhoSℂ S hcard h0‖ < R ∧ R < T ∧
        ∀ z ∈ Metric.closedBall (0 : ℂ) T,
          z ≠ rhoSℂ S hcard h0 → 1 - partPoly ℂ S z ≠ 0 := by
  classical
  let ρℂ : ℂ := rhoSℂ S hcard h0
  let ρ : ℝ := rhoS S hcard h0
  let badRoots : Finset ℂ := (denominatorPolynomial S).roots.toFinset.erase ρℂ
  have hρnorm : ‖ρℂ‖ = ρ := by
    change ‖rhoSℂ S hcard h0‖ = ρ
    rw [rhoSℂ]
    exact Complex.norm_of_nonneg (rhoS_pos hcard h0).le
  have hbad_gt : ∀ z ∈ badRoots, ρ < ‖z‖ := by
    intro z hz
    simpa [badRoots, ρ] using roots_erase_rho_norm_gt S hcard h0 hgcd z hz
  by_cases hbad_empty : badRoots = ∅
  · refine ⟨ρ + 2⁻¹, ρ + 1, ?_, ?_, ?_⟩
    · rw [hρnorm]
      linarith
    · linarith
    · intro z _hz hz_ne hroot
      have hp : denominatorPolynomial S ≠ 0 := denominatorPolynomial_ne_zero S h0
      have hzroots : z ∈ (denominatorPolynomial S).roots.toFinset := by
        exact Multiset.mem_toFinset.mpr
          ((Polynomial.mem_roots hp).mpr ((denominatorPolynomial_isRoot_iff S z).mpr hroot))
      have hzbad : z ∈ badRoots := by
        exact Finset.mem_erase.mpr ⟨hz_ne, hzroots⟩
      simp [hbad_empty] at hzbad
  · have hbad_nonempty : badRoots.Nonempty := Finset.nonempty_iff_ne_empty.mpr hbad_empty
    let badNorms : Finset ℝ := badRoots.image fun z => ‖z‖
    have hbadNorms_nonempty : badNorms.Nonempty := by
      rcases hbad_nonempty with ⟨z, hz⟩
      exact ⟨‖z‖, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    let m : ℝ := badNorms.min' hbadNorms_nonempty
    have hρm : ρ < m := by
      dsimp [m]
      rw [Finset.lt_min'_iff]
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
      exact hbad_gt z hz
    rcases exists_between hρm with ⟨T, hρT, hTm⟩
    rcases exists_between hρT with ⟨R, hρR, hRT⟩
    refine ⟨R, T, ?_, hRT, ?_⟩
    · rw [hρnorm]
      exact hρR
    · intro z hzclosed hz_ne hroot
      have hp : denominatorPolynomial S ≠ 0 := denominatorPolynomial_ne_zero S h0
      have hzroots : z ∈ (denominatorPolynomial S).roots.toFinset := by
        exact Multiset.mem_toFinset.mpr
          ((Polynomial.mem_roots hp).mpr ((denominatorPolynomial_isRoot_iff S z).mpr hroot))
      have hzbad : z ∈ badRoots := Finset.mem_erase.mpr ⟨hz_ne, hzroots⟩
      have hzNormMem : ‖z‖ ∈ badNorms := Finset.mem_image.mpr ⟨z, hzbad, rfl⟩
      have hm_le_z : m ≤ ‖z‖ := by
        exact Finset.min'_le badNorms ‖z‖ hzNormMem
      have hz_le_T : ‖z‖ ≤ T := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hzclosed
      linarith

end Close
end CompositionsGeneral
end Meromorphic
end Ch5
end AnalyticCombinatorics
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch5 AnalyticCombinatorics.Ch5.Meromorphic AnalyticCombinatorics.Ch5.Meromorphic.CompositionsGeneral AnalyticCombinatorics.Ch5.Meromorphic.CompositionsGeneral.Close
open Complex Filter Asymptotics
open scoped BigOperators ComplexOrder ENNReal NNReal PowerSeries Topology
theorem solution
    (S : Finset ℕ) (hcard : 2 ≤ S.card) (h0 : 0 ∉ S)
    (hgcd : S.gcd id = 1) :
    (fun n : ℕ => (compS S h0 n : ℂ)) ~[atTop]
      (fun n : ℕ =>
        compAsymptoticConstant S hcard h0 * (rhoSℂ S hcard h0)⁻¹ ^ n) := by
  classical
  rcases exists_dominant_annulus S hcard h0 hgcd with
    ⟨R, T, hρR, hRT, hden⟩
  have hρpos : 0 < ‖rhoSℂ S hcard h0‖ := by
    rw [rhoSℂ]
    rw [Complex.norm_of_nonneg (rhoS_pos hcard h0).le]
    exact rhoS_pos hcard h0
  have hCρ : partPoly ℂ S (rhoSℂ S hcard h0) = 1 :=
    partPoly_rhoSℂ S hcard h0
  have hCan : ∀ z ∈ Metric.closedBall (0 : ℂ) T, AnalyticAt ℂ (partPoly ℂ S) z :=
    fun z _hz => partPoly_analyticAt S z
  have hderiv : HasDerivAt (partPoly ℂ S)
      (partPolyDerivAt S (rhoSℂ S hcard h0)) (rhoSℂ S hcard h0) :=
    partPoly_hasDerivAt S (rhoSℂ S hcard h0)
  have hderiv_ne : partPolyDerivAt S (rhoSℂ S hcard h0) ≠ 0 :=
    partPolyDerivAt_rhoSℂ_ne_zero S hcard h0
  have hF :
      HasFPowerSeriesAt (fun z : ℂ => (1 - partPoly ℂ S z)⁻¹)
        (PowerSeries.toFMLS (compSeriesℂ S h0)) (0 : ℂ) :=
    compSeriesℂ_hasFPowerSeriesAt_zero S h0
  rcases SupercriticalSeqGenuine.supercriticalSeq_decomposition_from_supercritical_data
      (F := compSeriesℂ S h0) (Cfun := partPoly ℂ S)
      (ρ := rhoSℂ S hcard h0)
      (Cderiv := partPolyDerivAt S (rhoSℂ S hcard h0))
      (R := R) (S := T)
      hρpos hρR hRT hCρ hCan hderiv hderiv_ne hden hF with
    ⟨g, _hg_has, hgR, hdecomp⟩
  exact compS_isEquivalent_of_dominant_decomposition
    S hcard h0 g hρR hderiv_ne hgR
    (by simpa [residueConstant] using hdecomp)
