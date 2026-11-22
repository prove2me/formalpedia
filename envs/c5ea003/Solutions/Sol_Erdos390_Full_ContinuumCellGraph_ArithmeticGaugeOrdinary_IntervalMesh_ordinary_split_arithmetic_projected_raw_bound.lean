-- Prove2me | solution 1 for Erdos390.Full.ContinuumCellGraph.ArithmeticGaugeOrdinary.IntervalMesh.ordinary_split_arithmetic_projected_raw_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T13:14:34.819983+00:00
-- url     : https://prove2.me/submissions/b7e85b7f-be43-4e02-ae31-12733b33c837

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Definitions.Def_erdos390_analytic_foundations_001
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u_1 u_2 u_3

open Set
open scoped Interval

noncomputable section

namespace D45

open MeasureTheory
open Erdos390.Full Erdos390.Full.DickmanBasic Erdos390.Full.ConditionedPoissonLimit
open Erdos390.Full.PoissonDickmanDirichlet

theorem d_rho_pos {x : ℝ} (hx0 : 0 ≤ x) (hx5 : x ≤ 5) : 0 < rho x := by
  rw [← rhoGlobal_eq_rho hx5]
  exact rhoGlobal_pos hx0

theorem d_rho_U_pos : 0 < rho U := d_rho_pos (by norm_num [U]) (by norm_num [U])

theorem d_F_zero : F 0 = 1 := by
  unfold F
  rw [sub_zero]
  exact div_self (ne_of_gt d_rho_U_pos)

theorem d_mul_Q {s t : ℝ}
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
    _ = F (s + t) - F s * F t := by rw [zero_add, d_F_zero]; ring

lemma d_dickmanLogSlope_pos {u : ℝ} (hu2 : 2 ≤ u) (hu5 : u ≤ 5) :
    0 < dickmanLogSlope u := by
  unfold dickmanLogSlope
  exact div_pos
    (d_rho_pos (by linarith) (by linarith))
    (mul_pos (by linarith) (d_rho_pos (by linarith) hu5))

/-- Exact differential recurrence for the Dickman logarithmic slope.  Thus
strict log-concavity is equivalent to proving that the final parenthesis is
positive.  This identity is an unconditional step toward the first-failure
argument; it does not assume monotonicity of the slope. -/
lemma d_hasDerivAt_dickmanLogSlope {u : ℝ} (hu2 : 2 < u) (hu5 : u < 5) :
    HasDerivAt dickmanLogSlope
      (dickmanLogSlope u *
        (dickmanLogSlope u - dickmanLogSlope (u - 1) - 1 / u)) u := by
  have hu1 : 1 < u := by linarith
  have hu6 : u ≤ 6 := by linarith
  have hum1 : 1 < u - 1 := by linarith
  have hum1_le6 : u - 1 ≤ 6 := by linarith
  have hshift : HasDerivAt (fun x : ℝ => x - 1) 1 u := by
    simpa using (hasDerivAt_id u).sub_const 1
  have hnum : HasDerivAt (fun x : ℝ => rho (x - 1))
      (-rho (u - 2) / (u - 1)) u := by
    have h := (hasDerivAt_rho hum1 hum1_le6).comp u hshift
    simp only [Function.comp_def] at h
    ring_nf at h ⊢
    exact h
  have hu0 : u ≠ 0 := ne_of_gt (by linarith)
  have hden : HasDerivAt (fun x : ℝ => x * rho x)
      (rho u + u * (-rho (u - 1) / u)) u := by
    simpa [id] using (hasDerivAt_id u).mul (hasDerivAt_rho hu1 hu6)
  have hru : 0 < rho u := d_rho_pos (by linarith) hu5.le
  have hrum1 : 0 < rho (u - 1) :=
    d_rho_pos (by linarith) (by linarith)
  have hrum2 : 0 < rho (u - 2) :=
    d_rho_pos (by linarith) (by linarith)
  have hum10 : u - 1 ≠ 0 := ne_of_gt (by linarith)
  have hden0 : u * rho u ≠ 0 := mul_ne_zero hu0 (ne_of_gt hru)
  have hraw := hnum.div hden hden0
  apply hraw.congr_deriv
  unfold dickmanLogSlope
  field_simp [hu0, hum10, ne_of_gt hru, ne_of_gt hrum1, ne_of_gt hrum2]
  ring

lemma d_continuousOn_slopeGrowth_Icc :
    ContinuousOn slopeGrowth (Icc (2 : ℝ) (9 / 2 : ℝ)) := by
  unfold slopeGrowth dickmanLogSlope
  apply ContinuousOn.mul
  · apply ContinuousOn.div
    · exact (continuous_rho.comp
        (continuous_id.sub continuous_const)).continuousOn
    · exact (continuous_id.mul continuous_rho).continuousOn
    · intro x hx
      exact mul_ne_zero (ne_of_gt (by linarith [hx.1]))
        (ne_of_gt (d_rho_pos (by linarith [hx.1])
          (by norm_num at hx ⊢; linarith [hx.2])))
  · apply ContinuousOn.sub
    · apply ContinuousOn.sub
      · apply ContinuousOn.div
        · exact (continuous_rho.comp
            (continuous_id.sub continuous_const)).continuousOn
        · exact (continuous_id.mul continuous_rho).continuousOn
        · intro x hx
          exact mul_ne_zero (ne_of_gt (by linarith [hx.1]))
            (ne_of_gt (d_rho_pos (by linarith [hx.1])
              (by norm_num at hx ⊢; linarith [hx.2])))
      · apply ContinuousOn.div
        · exact (continuous_rho.comp
            ((continuous_id.sub continuous_const).sub continuous_const)).continuousOn
        · exact ((continuous_id.sub continuous_const).mul
            (continuous_rho.comp
              (continuous_id.sub continuous_const))).continuousOn
        · intro x hx
          exact mul_ne_zero (ne_of_gt (by linarith [hx.1]))
            (ne_of_gt (d_rho_pos (by linarith [hx.1])
              (by norm_num at hx ⊢; linarith [hx.2])))
    · exact continuous_const.continuousOn.div continuous_id.continuousOn
        (fun x hx => ne_of_gt (by linarith [hx.1]))

/-- The unit piece of the delay integral.  This is the exact finite-interval
identity used below; in particular, no differentiation under an integral
sign is needed in the first-failure step. -/
lemma d_neg_slopeGrowth_div_sq_eq_integral {u : ℝ}
    (hu2 : 2 < u) (hu5 : u ≤ 5) :
    -slopeGrowth u / dickmanLogSlope u ^ 2 =
      ∫ t in (0 : ℝ)..1,
        (rho (u - t) / rho (u - 1)) *
          (dickmanLogSlope (u - 1) - dickmanLogSlope (u - t)) := by
  have hru : 0 < rho u := d_rho_pos (by linarith) hu5
  have hrum1 : 0 < rho (u - 1) :=
    d_rho_pos (by linarith) (by linarith)
  have hrum2 : 0 < rho (u - 2) :=
    d_rho_pos (by linarith) (by linarith)
  have hu0 : u ≠ 0 := ne_of_gt (by linarith)
  have hum10 : u - 1 ≠ 0 := ne_of_gt (by linarith)
  let R : ℝ → ℝ := fun t => rho (u - t) / rho (u - 1)
  let D : ℝ → ℝ := fun t => rho (u - t - 1) / (u - t) / rho (u - 1)
  have hRcont : Continuous R := by
    dsimp [R]
    exact (continuous_rho.comp
      (continuous_const.sub continuous_id)).div_const _
  have hDcont : ContinuousOn D (Icc (0 : ℝ) 1) := by
    dsimp [D]
    apply ContinuousOn.div_const
    apply ContinuousOn.div
    · exact (continuous_rho.comp
        ((continuous_const.sub continuous_id).sub continuous_const)).continuousOn
    · exact (continuous_const.sub continuous_id).continuousOn
    · intro t ht
      exact ne_of_gt (by linarith [ht.2, hu2])
  have hRint : IntervalIntegrable R volume (0 : ℝ) 1 :=
    hRcont.intervalIntegrable 0 1
  have hDint : IntervalIntegrable D volume (0 : ℝ) 1 := by
    rw [← uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hDcont
    exact hDcont.intervalIntegrable
  have hpoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      R t * (dickmanLogSlope (u - 1) - dickmanLogSlope (u - t)) =
        dickmanLogSlope (u - 1) * R t - D t := by
    have hut0 : u - t ≠ 0 := ne_of_gt (by linarith [ht.2, hu2])
    have hrut : 0 < rho (u - t) :=
      d_rho_pos (by linarith [ht.2, hu2]) (by linarith [ht.1, hu5])
    dsimp [R, D]
    unfold dickmanLogSlope
    field_simp [hu0, hum10, hut0, ne_of_gt hru, ne_of_gt hrum1,
      ne_of_gt hrum2, ne_of_gt hrut]
  rw [show (∫ t in (0 : ℝ)..1,
      R t * (dickmanLogSlope (u - 1) - dickmanLogSlope (u - t))) =
        ∫ t in (0 : ℝ)..1, dickmanLogSlope (u - 1) * R t - D t by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hpoint t (by
        simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht)]
  rw [intervalIntegral.integral_sub
    (hRint.const_mul (dickmanLogSlope (u - 1))) hDint]
  rw [intervalIntegral.integral_const_mul]
  change -slopeGrowth u / dickmanLogSlope u ^ 2 =
    dickmanLogSlope (u - 1) *
        (∫ t in (0 : ℝ)..1, rho (u - t) / rho (u - 1)) -
      ∫ t in (0 : ℝ)..1, rho (u - t - 1) / (u - t) / rho (u - 1)
  rw [rho_ratio_average hu2.le hu5]
  rw [intervalIntegral.integral_div,
    rho_delay_unitIntegral hu2.le hu5]
  unfold slopeGrowth dickmanLogSlope
  field_simp [hu0, hum10, ne_of_gt hru, ne_of_gt hrum1, ne_of_gt hrum2]
  ring

lemma d_continuousOn_dickmanLogSlope_open :
    ContinuousOn dickmanLogSlope (Ioo (1 : ℝ) 5) := by
  unfold dickmanLogSlope
  apply ContinuousOn.div
  · exact (continuous_rho.comp
      (continuous_id.sub continuous_const)).continuousOn
  · exact (continuous_id.mul continuous_rho).continuousOn
  · intro x hx
    exact mul_ne_zero (ne_of_gt (by linarith [hx.1]))
      (ne_of_gt (d_rho_pos (by linarith [hx.1]) hx.2.le))

lemma d_continuousOn_dickmanLogSlope_one_to_nine_halves :
    ContinuousOn dickmanLogSlope (Icc (1 : ℝ) (9 / 2 : ℝ)) := by
  unfold dickmanLogSlope
  apply ContinuousOn.div
  · exact (continuous_rho.comp
      (continuous_id.sub continuous_const)).continuousOn
  · exact (continuous_id.mul continuous_rho).continuousOn
  · intro x hx
    exact mul_ne_zero (ne_of_gt (by linarith [hx.1]))
      (ne_of_gt (d_rho_pos (by linarith [hx.1])
        (by norm_num at hx ⊢; linarith [hx.2])))

/-- On the first nonconstant Dickman interval the numerator of the slope is
still `1`, so the derivative has this simpler exact form. -/
lemma d_hasDerivAt_dickmanLogSlope_one_two {u : ℝ}
    (hu1 : 1 < u) (hu2 : u < 2) :
    HasDerivAt dickmanLogSlope
      (dickmanLogSlope u * (dickmanLogSlope u - 1 / u)) u := by
  have heq : (fun z : ℝ => rho (z - 1)) =ᶠ[nhds u] (fun _ => (1 : ℝ)) := by
    filter_upwards [Iio_mem_nhds hu2] with z hz
    have hz' : z < 2 := by simpa only [mem_Iio] using hz
    exact rho_eq_one_of_le_one (by linarith [hz'])
  have hnum : HasDerivAt (fun z : ℝ => rho (z - 1)) 0 u := by
    simpa using (hasDerivAt_const u (1 : ℝ)).congr_of_eventuallyEq heq
  have hu0 : u ≠ 0 := ne_of_gt (by linarith)
  have hden : HasDerivAt (fun z : ℝ => z * rho z)
      (rho u + u * (-rho (u - 1) / u)) u := by
    simpa [id] using (hasDerivAt_id u).mul
      (hasDerivAt_rho hu1 (by linarith))
  have hru : 0 < rho u := d_rho_pos (by linarith) (by linarith)
  have hrum1 : rho (u - 1) = 1 := rho_eq_one_of_le_one (by linarith)
  have hden0 : u * rho u ≠ 0 := mul_ne_zero hu0 (ne_of_gt hru)
  have hraw := hnum.div hden hden0
  apply hraw.congr_deriv
  unfold dickmanLogSlope
  rw [hrum1]
  field_simp [hu0, ne_of_gt hru]
  ring

lemma d_strictMonoOn_dickmanLogSlope_one_two :
    StrictMonoOn dickmanLogSlope (Icc (1 : ℝ) 2) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (1 : ℝ) 2)
    (d_continuousOn_dickmanLogSlope_one_to_nine_halves.mono (by
      intro x hx
      exact ⟨hx.1, by norm_num at hx ⊢; linarith [hx.2]⟩))
  intro x hx
  rw [interior_Icc] at hx
  have hderiv := d_hasDerivAt_dickmanLogSlope_one_two hx.1 hx.2
  rw [hderiv.deriv]
  have hrho : 0 < rho x :=
    d_rho_pos (by linarith [hx.1]) (by linarith [hx.2])
  have hrho_lt : rho x < 1 := by
    have hanti := strictAntiOn_rhoGlobal_Ici_one
      (show (1 : ℝ) ∈ Ici 1 by simp)
      (show x ∈ Ici 1 by simpa using hx.1.le) hx.1
    rw [rhoGlobal_eq_one_of_le_one le_rfl,
      rhoGlobal_eq_rho (by linarith [hx.2])] at hanti
    exact hanti
  have hxpos : 0 < x := by linarith [hx.1]
  have hdenpos : 0 < x * rho x := mul_pos hxpos hrho
  have hdenlt : x * rho x < x := by nlinarith
  have hslope_gt : 1 / x < dickmanLogSlope x := by
    unfold dickmanLogSlope
    rw [rho_eq_one_of_le_one (by linarith [hx.2])]
    exact one_div_lt_one_div_of_lt hdenpos hdenlt
  have hslope_pos : 0 < dickmanLogSlope x := by
    unfold dickmanLogSlope
    rw [rho_eq_one_of_le_one (by linarith [hx.2])]
    exact div_pos zero_lt_one (mul_pos hxpos hrho)
  exact mul_pos hslope_pos (sub_pos.mpr hslope_gt)

lemma d_slopeGrowth_two_pos : 0 < slopeGrowth 2 := by
  have hrho2 : 0 < rho 2 := d_rho_pos (by norm_num) (by norm_num)
  have hrho2lt : rho 2 < 1 / 3 := by
    rw [rho_two_eq_one_sub_log_two]
    have hlog := Real.log_two_gt_d9
    norm_num at hlog ⊢
    nlinarith [hlog]
  unfold slopeGrowth dickmanLogSlope
  norm_num [rho_one, rho_zero]
  field_simp [ne_of_gt hrho2]
  nlinarith

/-- Positive recurrence growth after `2` propagates strict monotonicity of
the logarithmic slope from the explicit base interval `[1,2]`. -/
lemma d_strictMonoOn_dickmanLogSlope_of_growth_pos {x : ℝ}
    (hx2 : 2 ≤ x) (hx9 : x ≤ 9 / 2)
    (hgrowth : ∀ z ∈ Ioo (2 : ℝ) x, 0 < slopeGrowth z) :
    StrictMonoOn dickmanLogSlope (Icc (1 : ℝ) x) := by
  have hupper : StrictMonoOn dickmanLogSlope (Icc (2 : ℝ) x) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc (2 : ℝ) x)
    · exact d_continuousOn_dickmanLogSlope_one_to_nine_halves.mono (by
        intro z hz
        exact ⟨by linarith [hz.1], by linarith [hz.2, hx9]⟩)
    · intro z hz
      rw [interior_Icc] at hz
      have hderiv := d_hasDerivAt_dickmanLogSlope hz.1
        (by norm_num at hx9 ⊢; linarith [hz.2, hx9])
      rw [hderiv.deriv]
      exact hgrowth z hz
  intro a ha b hb hab
  by_cases hb2 : b ≤ 2
  · exact d_strictMonoOn_dickmanLogSlope_one_two
      ⟨ha.1, hab.le.trans hb2⟩ ⟨by linarith [ha.1], hb2⟩ hab
  by_cases ha2 : 2 ≤ a
  · exact hupper ⟨ha2, ha.2⟩ ⟨by linarith [hb2], hb.2⟩ hab
  · have hleft := d_strictMonoOn_dickmanLogSlope_one_two
      (show a ∈ Icc (1 : ℝ) 2 from ⟨ha.1, le_of_not_ge ha2⟩)
      (show (2 : ℝ) ∈ Icc (1 : ℝ) 2 by norm_num)
      (lt_of_not_ge ha2)
    have hright := hupper
      (show (2 : ℝ) ∈ Icc 2 x from ⟨le_rfl, hx2⟩)
      (show b ∈ Icc 2 x from ⟨le_of_not_ge hb2, hb.2⟩)
      (lt_of_not_ge hb2)
    exact hleft.trans hright

/-- Strict positivity of the Dickman log-slope growth on the whole range
needed by the covariance kernel.  The proof uses the compact first-failure
principle and the exact algebraic integral identity above. -/
theorem d_slopeGrowth_pos_on_two_nine_halves :
    ∀ u ∈ Icc (2 : ℝ) (9 / 2 : ℝ), 0 < slopeGrowth u := by
  apply FirstFailure.positiveOn_Icc_of_positive_at_first_failure
    slopeGrowth d_continuousOn_slopeGrowth_Icc
  intro u hu hprev
  rcases hu.1.eq_or_lt with rfl | hu2
  · exact d_slopeGrowth_two_pos
  · have hmono : StrictMonoOn dickmanLogSlope (Icc (1 : ℝ) u) :=
      d_strictMonoOn_dickmanLogSlope_of_growth_pos hu.1 hu.2 (by
        intro z hz
        exact hprev z ⟨hz.1.le, hz.2.le⟩ hz.2)
    let H : ℝ → ℝ := fun t =>
      -((rho (u - t) / rho (u - 1)) *
        (dickmanLogSlope (u - 1) - dickmanLogSlope (u - t)))
    have hRcont : Continuous (fun t : ℝ => rho (u - t) / rho (u - 1)) :=
      (continuous_rho.comp
        (continuous_const.sub continuous_id)).div_const _
    have hfcomp : ContinuousOn (fun t : ℝ => dickmanLogSlope (u - t))
        (Icc (0 : ℝ) 1) := by
      apply d_continuousOn_dickmanLogSlope_open.comp
        (continuous_const.sub continuous_id).continuousOn
      intro t ht
      change 1 < u - t ∧ u - t < 5
      exact ⟨by linarith [hu2, ht.2], by
        norm_num at hu ⊢
        linarith [hu.2, ht.1]⟩
    have hHcont : ContinuousOn H (Icc (0 : ℝ) 1) := by
      dsimp [H]
      exact (hRcont.continuousOn.mul
        (continuous_const.continuousOn.sub hfcomp)).neg
    have hHnonneg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ H t := by
      have hratio : 0 < rho (u - t) / rho (u - 1) :=
        div_pos
          (d_rho_pos (by linarith [hu2, ht.2])
            (by norm_num at hu ⊢; linarith [hu.2, ht.1]))
          (d_rho_pos (by linarith [hu2])
            (by norm_num at hu ⊢; linarith [hu.2]))
      have hslope : dickmanLogSlope (u - 1) ≤ dickmanLogSlope (u - t) :=
        hmono.monotoneOn
          ⟨by linarith [hu2], by linarith⟩
          ⟨by linarith [hu2, ht.2], by linarith [ht.1]⟩
          (by linarith [ht.2])
      dsimp [H]
      exact neg_nonneg.mpr
        (mul_nonpos_of_nonneg_of_nonpos hratio.le (sub_nonpos.mpr hslope))
    have hHhalf : 0 < H (1 / 2 : ℝ) := by
      have hratio : 0 < rho (u - (1 / 2 : ℝ)) / rho (u - 1) :=
        div_pos
          (d_rho_pos (by linarith [hu2])
            (by norm_num at hu ⊢; linarith [hu.2]))
          (d_rho_pos (by linarith [hu2])
            (by norm_num at hu ⊢; linarith [hu.2]))
      have hslope : dickmanLogSlope (u - 1) <
          dickmanLogSlope (u - (1 / 2 : ℝ)) :=
        hmono
          ⟨by linarith [hu2], by linarith⟩
          ⟨by linarith [hu2], by linarith⟩
          (by norm_num)
      dsimp [H]
      exact neg_pos.mpr (mul_neg_of_pos_of_neg hratio (sub_neg.mpr hslope))
    have hHIntegral : 0 < ∫ t in (0 : ℝ)..1, H t := by
      apply intervalIntegral.integral_pos (show (0 : ℝ) < 1 by norm_num)
        hHcont
      · intro t ht
        exact hHnonneg t ⟨ht.1.le, ht.2⟩
      · exact ⟨(1 / 2 : ℝ), by norm_num, hHhalf⟩
    have hintegralNeg :
        (∫ t in (0 : ℝ)..1,
          (rho (u - t) / rho (u - 1)) *
            (dickmanLogSlope (u - 1) - dickmanLogSlope (u - t))) < 0 := by
      dsimp [H] at hHIntegral
      rw [intervalIntegral.integral_neg] at hHIntegral
      linarith
    have hid := d_neg_slopeGrowth_div_sq_eq_integral hu2
      (by norm_num at hu ⊢; linarith [hu.2])
    have hquot : -slopeGrowth u / dickmanLogSlope u ^ 2 < 0 := by
      rw [hid]
      exact hintegralNeg
    have hslopePos : 0 < dickmanLogSlope u :=
      d_dickmanLogSlope_pos hu2.le (by norm_num at hu ⊢; linarith [hu.2])
    have hden : 0 < dickmanLogSlope u ^ 2 := sq_pos_of_pos hslopePos
    have hnum : -slopeGrowth u < 0 := by
      rcases (div_neg_iff.mp hquot) with hbad | hgood
      · exact False.elim ((not_lt_of_ge hden.le) hbad.2)
      · exact hgood.1
    linarith

theorem d_strictMonoOn_dickmanLogSlope_one_nine_halves :
    StrictMonoOn dickmanLogSlope (Icc (1 : ℝ) (9 / 2 : ℝ)) := by
  apply d_strictMonoOn_dickmanLogSlope_of_growth_pos (by norm_num) le_rfl
  intro z hz
  exact d_slopeGrowth_pos_on_two_nine_halves z ⟨hz.1.le, hz.2.le⟩

lemma d_hasDerivAt_log_rho_eq_neg_slope {x : ℝ} (hx1 : 1 < x) (hx5 : x < 5) :
    HasDerivAt (fun z : ℝ => Real.log (rho z)) (-dickmanLogSlope x) x := by
  have hrho : 0 < rho x :=
    d_rho_pos (by linarith) hx5.le
  have hraw := (hasDerivAt_rho hx1 (by linarith)).log (ne_of_gt hrho)
  apply hraw.congr_deriv
  unfold dickmanLogSlope
  have hx0 : x ≠ 0 := ne_of_gt (by linarith)
  field_simp [hx0, ne_of_gt hrho]

/-- Fundamental-theorem form of the logarithmic derivative, on the entire
range used by the one- and two-point Dickman translates. -/
lemma d_log_rho_sub_eq_neg_slopeIntegral {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hb : b < 5) :
    Real.log (rho b) - Real.log (rho a) =
      -(∫ x in a..b, dickmanLogSlope x) := by
  have hcontLog : ContinuousOn (fun x : ℝ => Real.log (rho x)) (Icc a b) := by
    apply ContinuousOn.log continuous_rho.continuousOn
    intro x hx
    exact ne_of_gt (d_rho_pos
      (by linarith [ha, hx.1]) (by linarith [hb, hx.2]))
  have hcontSlope : ContinuousOn (fun x : ℝ => -dickmanLogSlope x)
      (Icc a b) :=
    (d_continuousOn_dickmanLogSlope_open.mono (by
      intro x hx
      exact ⟨by linarith [ha, hx.1], by linarith [hb, hx.2]⟩)).neg
  have hFTC :
      (∫ x in a..b, -dickmanLogSlope x) =
        Real.log (rho b) - Real.log (rho a) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcontLog
    · intro x hx
      exact d_hasDerivAt_log_rho_eq_neg_slope
        (by linarith [ha, hx.1]) (by linarith [hb, hx.2])
    · exact hcontSlope.intervalIntegrable_of_Icc hab
  rw [intervalIntegral.integral_neg] at hFTC
  linarith

 lemma d_slopeIntegral_shift_lt_closed {s t : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ x in (U - s - t)..(U - s), dickmanLogSlope x) <
      ∫ x in (U - t)..U, dickmanLogSlope x := by
  have hab : U - s - t < U - s := by linarith [ht.1]
  have hxmem (x : ℝ) (hx : x ∈ Icc (U - s - t) (U - s)) :
      x ∈ Icc (1 : ℝ) (9 / 2 : ℝ) := by
    constructor
    · norm_num [U] at hs ht hx ⊢
      linarith [hs.2, ht.2, hx.1]
    · norm_num [U] at hs ht hx ⊢
      linarith [hs.1, hx.2]
  have hxsmem (x : ℝ) (hx : x ∈ Icc (U - s - t) (U - s)) :
      x + s ∈ Icc (1 : ℝ) (9 / 2 : ℝ) := by
    constructor
    · norm_num [U] at hs ht hx ⊢
      linarith [ht.2, hx.1]
    · norm_num [U] at hs hx ⊢
      linarith [hs.2, hx.2]
  have hcont₁ : ContinuousOn dickmanLogSlope (Icc (U - s - t) (U - s)) :=
    d_continuousOn_dickmanLogSlope_one_to_nine_halves.mono hxmem
  have hcont₂ : ContinuousOn (fun x : ℝ => dickmanLogSlope (x + s))
      (Icc (U - s - t) (U - s)) := by
    apply d_continuousOn_dickmanLogSlope_one_to_nine_halves.comp
      (continuous_id.add continuous_const).continuousOn
    exact hxsmem
  have hle : ∀ x ∈ Ioc (U - s - t) (U - s),
      dickmanLogSlope x ≤ dickmanLogSlope (x + s) := by
    intro x hx
    apply d_strictMonoOn_dickmanLogSlope_one_nine_halves.monotoneOn
    · exact hxmem x ⟨hx.1.le, hx.2⟩
    · exact hxsmem x ⟨hx.1.le, hx.2⟩
    · linarith [hs.1]
  have hexists : ∃ c ∈ Icc (U - s - t) (U - s),
      dickmanLogSlope c < dickmanLogSlope (c + s) := by
    refine ⟨U - s - t, left_mem_Icc.mpr hab.le, ?_⟩
    apply d_strictMonoOn_dickmanLogSlope_one_nine_halves
    · exact hxmem _ (left_mem_Icc.mpr hab.le)
    · exact hxsmem _ (left_mem_Icc.mpr hab.le)
    · linarith [hs.1]
  have hint := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hab hcont₁ hcont₂ hle hexists
  rw [intervalIntegral.integral_comp_add_right] at hint
  convert hint using 1
  all_goals ring

lemma d_log_rho_four_point_lt_closed {s t : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1) :
    Real.log (rho (U - s - t)) + Real.log (rho U) <
      Real.log (rho (U - s)) + Real.log (rho (U - t)) := by
  have h₁ := d_log_rho_sub_eq_neg_slopeIntegral
    (a := U - s - t) (b := U - s)
    (by norm_num [U] at hs ht ⊢; linarith [hs.2, ht.2])
    (by linarith [ht.1])
    (by norm_num [U] at hs ⊢; linarith [hs.1])
  have h₂ := d_log_rho_sub_eq_neg_slopeIntegral
    (a := U - t) (b := U)
    (by norm_num [U] at ht ⊢; linarith [ht.2])
    (by linarith [ht.1]) (by norm_num [U])
  have hint := d_slopeIntegral_shift_lt_closed hs ht
  linarith

lemma d_rho_four_point_lt_closed {s t : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1) :
    rho (U - s - t) * rho U < rho (U - s) * rho (U - t) := by
  have ha : 0 < rho (U - s - t) :=
    d_rho_pos
      (by norm_num [U] at hs ht ⊢; linarith [hs.2, ht.2])
      (by norm_num [U] at hs ht ⊢; linarith [hs.1, ht.1])
  have hb : 0 < rho U := d_rho_U_pos
  have hc : 0 < rho (U - s) :=
    d_rho_pos
      (by norm_num [U] at hs ⊢; linarith [hs.2])
      (by norm_num [U] at hs ⊢; linarith [hs.1])
  have hd : 0 < rho (U - t) :=
    d_rho_pos
      (by norm_num [U] at ht ⊢; linarith [ht.2])
      (by norm_num [U] at ht ⊢; linarith [ht.1])
  have h := Real.exp_lt_exp.mpr (d_log_rho_four_point_lt_closed hs ht)
  rw [Real.exp_add, Real.exp_add, Real.exp_log ha, Real.exp_log hb,
    Real.exp_log hc, Real.exp_log hd] at h
  exact h

theorem d_covarianceKernel_neg_closed {s t : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1) :
    covarianceKernel s t < 0 := by
  have hprod := d_rho_four_point_lt_closed hs ht
  have hU : 0 < rho U := d_rho_U_pos
  have hden : 0 < rho U * rho U := mul_pos hU hU
  have hscaled := (div_lt_div_iff_of_pos_right hden).2 hprod
  unfold covarianceKernel F
  apply sub_neg.mpr
  calc
    rho (U - (s + t)) / rho U =
        (rho (U - s - t) * rho U) / (rho U * rho U) := by
      rw [show U - (s + t) = U - s - t by ring]
      field_simp [ne_of_gt hU]
    _ < (rho (U - s) * rho (U - t)) / (rho U * rho U) := hscaled
    _ = rho (U - s) / rho U * (rho (U - t) / rho U) := by
      field_simp [ne_of_gt hU]



section MeshB

open Erdos390.Full.ContinuumCellGraph

variable {Band : Type*} [Fintype Band] {epsilon : ℝ}

theorem hm_eq (M : IntervalMesh epsilon Band) (i : Band) :
    M.harmonicMass i = Real.log (M.upper i / M.lower i) := by
  unfold IntervalMesh.harmonicMass
  exact integral_one_div_of_pos (M.lower_pos i)
    (lt_trans (M.lower_pos i) (M.lower_lt_upper i))

theorem hm_pos (M : IntervalMesh epsilon Band) (i : Band) : 0 < M.harmonicMass i := by
  rw [hm_eq]
  apply Real.log_pos
  rw [one_lt_div (M.lower_pos i)]
  exact M.lower_lt_upper i

theorem len_pos (M : IntervalMesh epsilon Band) (i : Band) : 0 < M.length i :=
  sub_pos.mpr (M.lower_lt_upper i)

theorem c_pos (M : IntervalMesh epsilon Band) (i : Band) : 0 < M.center i :=
  div_pos (len_pos M i) (hm_pos M i)

theorem h_mul_c (M : IntervalMesh epsilon Band) (i : Band) :
    M.harmonicMass i * M.center i = M.length i := by
  have hh := ne_of_gt (hm_pos M i)
  unfold IntervalMesh.center
  field_simp

def psi (m s t : ℝ) : ℝ :=
  covarianceKernel (max t m) (max s m) / (max s m * max t m)

theorem psi_cont (m : ℝ) (hm : 0 < m) : Continuous (Function.uncurry (psi m)) := by
  show Continuous (fun p : ℝ × ℝ => psi m p.1 p.2)
  unfold psi covarianceKernel
  have h1 : Continuous (fun p : ℝ × ℝ => max p.1 m) := continuous_fst.max continuous_const
  have h2 : Continuous (fun p : ℝ × ℝ => max p.2 m) := continuous_snd.max continuous_const
  refine Continuous.div ?_ (h1.mul h2) ?_
  · exact (continuous_F.comp (h2.add h1)).sub
      ((continuous_F.comp h2).mul (continuous_F.comp h1))
  · intro p
    exact mul_ne_zero (ne_of_gt (lt_of_lt_of_le hm (le_max_right _ _)))
      (ne_of_gt (lt_of_lt_of_le hm (le_max_right _ _)))

theorem psi_symm (m s t : ℝ) : psi m s t = psi m t s := by
  unfold psi covarianceKernel
  rw [add_comm (max t m) (max s m), mul_comm (F (max t m)) (F (max s m)),
    mul_comm (max s m) (max t m)]

theorem Qdiv_eq {s t : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    covarianceKernelQuotient t s / t = covarianceKernel t s / (s * t) := by
  have h := d_mul_Q (s := t) (t := s) ⟨ht0.le, ht1⟩ ⟨hs0.le, hs1⟩
  rw [← h]
  field_simp

def Gm (M : IntervalMesh epsilon Band) (i j : Band) : ℝ :=
  ∫ s in M.lower i..M.upper i, ∫ t in M.lower j..M.upper j,
    covarianceKernelQuotient t s / t

theorem Gm_psi (M : IntervalMesh epsilon Band) (i j : Band) :
    Gm M i j = ∫ s in M.lower i..M.upper i, ∫ t in M.lower j..M.upper j,
      psi (min (M.lower i) (M.lower j)) s t := by
  unfold Gm
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le (M.lower_lt_upper i).le] at hs
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (M.lower_lt_upper j).le] at ht
  have hs0 : 0 < s := lt_of_lt_of_le (M.lower_pos i) hs.1
  have ht0 : 0 < t := lt_of_lt_of_le (M.lower_pos j) ht.1
  have hs1 : s ≤ 1 := hs.2.trans (M.upper_le_one i)
  have ht1 : t ≤ 1 := ht.2.trans (M.upper_le_one j)
  show covarianceKernelQuotient t s / t = psi (min (M.lower i) (M.lower j)) s t
  unfold psi
  rw [max_eq_left ((min_le_left _ _).trans hs.1), max_eq_left ((min_le_right _ _).trans ht.1)]
  exact Qdiv_eq hs0 hs1 ht0 ht1

theorem swap_ii (f : ℝ → ℝ → ℝ) (hf : Continuous (Function.uncurry f)) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ s in a..b, ∫ t in c..d, f s t) = ∫ t in c..d, ∫ s in a..b, f s t := by
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  apply MeasureTheory.integral_integral_swap
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

theorem Gm_symm (M : IntervalMesh epsilon Band) (i j : Band) : Gm M i j = Gm M j i := by
  rw [Gm_psi M i j, Gm_psi M j i, min_comm (M.lower j) (M.lower i)]
  have hm : 0 < min (M.lower i) (M.lower j) := lt_min (M.lower_pos i) (M.lower_pos j)
  rw [swap_ii _ (psi_cont _ hm) (M.lower_lt_upper i).le (M.lower_lt_upper j).le]
  apply intervalIntegral.integral_congr
  intro t _
  apply intervalIntegral.integral_congr
  intro s _
  exact psi_symm _ _ _

theorem abs_Gm_le (M : IntervalMesh epsilon Band) {C : ℝ}
    (hcov : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, |covarianceKernel s t| ≤ C * s * t)
    (i j : Band) :
    |Gm M i j| ≤ C * M.length i * M.length j := by
  unfold Gm
  have hinner : ∀ s ∈ Ι (M.lower i) (M.upper i),
      ‖∫ t in M.lower j..M.upper j, covarianceKernelQuotient t s / t‖ ≤
        C * |M.upper j - M.lower j| := by
    intro s hs
    rw [uIoc_of_le (M.lower_lt_upper i).le] at hs
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [uIoc_of_le (M.lower_lt_upper j).le] at ht
    have hs0 : 0 < s := lt_trans (M.lower_pos i) hs.1
    have ht0 : 0 < t := lt_trans (M.lower_pos j) ht.1
    have hs1 : s ≤ 1 := hs.2.trans (M.upper_le_one i)
    have ht1 : t ≤ 1 := ht.2.trans (M.upper_le_one j)
    rw [Qdiv_eq hs0 hs1 ht0 ht1, Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hs0 ht0),
      div_le_iff₀ (mul_pos hs0 ht0)]
    have := hcov t ⟨ht0.le, ht1⟩ s ⟨hs0.le, hs1⟩
    calc |covarianceKernel t s| ≤ C * t * s := this
      _ = C * (s * t) := by ring
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hinner
  rw [Real.norm_eq_abs] at h
  unfold IntervalMesh.length
  rw [abs_of_pos (sub_pos.mpr (M.lower_lt_upper j)),
    abs_of_pos (sub_pos.mpr (M.lower_lt_upper i))] at h
  refine h.trans (le_of_eq ?_)
  ring

theorem E_eq (M : IntervalMesh epsilon Band) (i j : Band) :
    M.sharpKernelEdge i j = -(M.center j / M.length i) * Gm M i j := by
  unfold IntervalMesh.sharpKernelEdge Gm
  simp only [neg_div, intervalIntegral.integral_neg]
  ring

theorem E_nonneg (M : IntervalMesh epsilon Band) (i j : Band) : 0 ≤ M.sharpKernelEdge i j := by
  unfold IntervalMesh.sharpKernelEdge
  apply mul_nonneg (div_nonneg (c_pos M j).le (len_pos M i).le)
  apply intervalIntegral.integral_nonneg (M.lower_lt_upper i).le
  intro s hs
  apply intervalIntegral.integral_nonneg (M.lower_lt_upper j).le
  intro t ht
  have hs0 : 0 < s := lt_of_lt_of_le (M.lower_pos i) hs.1
  have ht0 : 0 < t := lt_of_lt_of_le (M.lower_pos j) ht.1
  have hs1 : s ≤ 1 := hs.2.trans (M.upper_le_one i)
  have ht1 : t ≤ 1 := ht.2.trans (M.upper_le_one j)
  have hneg := d_covarianceKernel_neg_closed (s := t) (t := s) ⟨ht0, ht1⟩ ⟨hs0, hs1⟩
  rw [neg_div, Qdiv_eq hs0 hs1 ht0 ht1, ← neg_div]
  exact div_nonneg (neg_nonneg.mpr hneg.le) (mul_pos hs0 ht0).le

theorem E_ge (M : IntervalMesh epsilon Band) {kappa : ℝ}
    (hk : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc epsilon (1 - epsilon),
      kappa ≤ -covarianceKernelQuotient t s)
    (i j : Band) (hj : j ∈ M.interiorCells) :
    kappa * M.length j ≤ M.sharpKernelEdge i j := by
  have hli := M.lower_lt_upper i
  have hlj := M.lower_lt_upper j
  have hm : 0 < min (M.lower i) (M.lower j) := lt_min (M.lower_pos i) (M.lower_pos j)
  have hinner_eq : EqOn (fun s => ∫ t in M.lower j..M.upper j, -covarianceKernelQuotient t s / t)
      (fun s => ∫ t in M.lower j..M.upper j, -psi (min (M.lower i) (M.lower j)) s t)
      (Icc (M.lower i) (M.upper i)) := by
    intro s hs
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hlj.le] at ht
    have hs0 : 0 < s := lt_of_lt_of_le (M.lower_pos i) hs.1
    have ht0 : 0 < t := lt_of_lt_of_le (M.lower_pos j) ht.1
    have hs1 : s ≤ 1 := hs.2.trans (M.upper_le_one i)
    have ht1 : t ≤ 1 := ht.2.trans (M.upper_le_one j)
    show -covarianceKernelQuotient t s / t = -psi (min (M.lower i) (M.lower j)) s t
    rw [neg_div]
    congr 1
    unfold psi
    rw [max_eq_left ((min_le_left _ _).trans hs.1), max_eq_left ((min_le_right _ _).trans ht.1)]
    exact Qdiv_eq hs0 hs1 ht0 ht1
  have hinner_ge : ∀ s ∈ Icc (M.lower i) (M.upper i),
      kappa * M.harmonicMass j ≤
        ∫ t in M.lower j..M.upper j, -covarianceKernelQuotient t s / t := by
    intro s hs
    unfold IntervalMesh.harmonicMass
    rw [← intervalIntegral.integral_const_mul]
    have hpos : ∀ t ∈ uIcc (M.lower j) (M.upper j), t ≠ 0 := by
      intro t ht
      rw [uIcc_of_le hlj.le] at ht
      exact ne_of_gt (lt_of_lt_of_le (M.lower_pos j) ht.1)
    apply intervalIntegral.integral_mono_on hlj.le
    · apply ContinuousOn.intervalIntegrable
      exact continuousOn_const.mul (continuousOn_const.div continuousOn_id hpos)
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div _ continuousOn_id hpos
      exact ((continuous_uncurry_covarianceKernelQuotient.comp
        (continuous_id.prodMk continuous_const)).neg).continuousOn
    · intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le (M.lower_pos j) ht.1
      have hke := hk s ⟨(M.lower_pos i).le.trans hs.1, hs.2.trans (M.upper_le_one i)⟩ t
        ⟨(M.interior_lower j hj).trans ht.1, ht.2.trans (M.interior_upper j hj)⟩
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right hke ht0.le
  have hcont : ContinuousOn
      (fun s => ∫ t in M.lower j..M.upper j, -covarianceKernelQuotient t s / t)
      (Icc (M.lower i) (M.upper i)) := by
    have hc0 : Continuous (Function.uncurry
        (fun s t => -psi (min (M.lower i) (M.lower j)) s t)) := (psi_cont _ hm).neg
    have hc : Continuous
        (fun s => ∫ t in M.lower j..M.upper j, -psi (min (M.lower i) (M.lower j)) s t) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc0 _ _
    exact hc.continuousOn.congr hinner_eq
  have houter : kappa * M.harmonicMass j * M.length i ≤
      ∫ s in M.lower i..M.upper i, ∫ t in M.lower j..M.upper j,
        -covarianceKernelQuotient t s / t := by
    have := intervalIntegral.integral_mono_on (μ := volume) hli.le intervalIntegrable_const
      (hcont.intervalIntegrable_of_Icc hli.le) hinner_ge
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    unfold IntervalMesh.length
    calc kappa * M.harmonicMass j * (M.upper i - M.lower i)
        = (M.upper i - M.lower i) * (kappa * M.harmonicMass j) := by ring
      _ ≤ _ := this
  unfold IntervalMesh.sharpKernelEdge
  have hcj := h_mul_c M j
  have hli0 := len_pos M i
  calc kappa * M.length j
      = M.center j / M.length i * (kappa * M.harmonicMass j * M.length i) := by
        rw [← hcj]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left houter (div_nonneg (c_pos M j).le hli0.le)

end MeshB


section MeshC

open Erdos390.Full.ContinuumCellGraph Erdos390.Full.PaperWeightedInverseExport

variable {Band : Type*} [Fintype Band] {epsilon : ℝ}

theorem Ac_eq (M : IntervalMesh epsilon Band) (b : Band → ℝ) (i : Band) :
    rawOperator M.normalizedDiagonalCell M.normalizedKernelCell b i =
      b i * M.rowResidual i +
        M.center i * ∑ j, M.sharpKernelEdge i j * (b i / M.center i - b j / M.center j) := by
  have hci := ne_of_gt (c_pos M i)
  have hhi := ne_of_gt (hm_pos M i)
  have hl : M.length i = M.harmonicMass i * M.center i := (h_mul_c M i).symm
  have hsum : ∑ j, M.normalizedKernelCell i j * b j =
      b i * ∑ j, M.normalizedKernelCell i j * (M.center j / M.center i) +
        M.center i * ∑ j, M.sharpKernelEdge i j * (b i / M.center i - b j / M.center j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hcj := ne_of_gt (c_pos M j)
    have hK : M.normalizedKernelCell i j = Gm M i j / M.harmonicMass i := rfl
    rw [hK, E_eq, hl]
    field_simp
    ring
  unfold rawOperator IntervalMesh.rowResidual
  rw [hsum]
  ring

theorem sum_len_Ac (M : IntervalMesh epsilon Band) (b : Band → ℝ) :
    ∑ k, M.length k * rawOperator M.normalizedDiagonalCell M.normalizedKernelCell b k =
      ∑ k, M.length k * M.rowResidual k * b k := by
  have hL : ∀ k, M.length k * rawOperator M.normalizedDiagonalCell M.normalizedKernelCell b k =
      M.length k * M.normalizedDiagonalCell k * b k + ∑ j, M.center k * Gm M k j * b j := by
    intro k
    have hhk := ne_of_gt (hm_pos M k)
    have hl : M.length k = M.harmonicMass k * M.center k := (h_mul_c M k).symm
    unfold rawOperator
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j _
      have hK : M.normalizedKernelCell k j = Gm M k j / M.harmonicMass k := rfl
      rw [hK, hl]
      field_simp
  have hR : ∀ k, M.length k * M.rowResidual k * b k =
      M.length k * M.normalizedDiagonalCell k * b k + ∑ j, b k * Gm M k j * M.center j := by
    intro k
    have hhk := ne_of_gt (hm_pos M k)
    have hck := ne_of_gt (c_pos M k)
    have hl : M.length k = M.harmonicMass k * M.center k := (h_mul_c M k).symm
    unfold IntervalMesh.rowResidual
    rw [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have hK : M.normalizedKernelCell k j = Gm M k j / M.harmonicMass k := rfl
    rw [hK, hl]
    field_simp
  simp only [hL, hR, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  rw [Gm_symm M j k]
  ring

end MeshC

theorem maxp {Low High : Type*} [Fintype Low] [Fintype High] [Nonempty High]
    (edge : Low ⊕ High → Low ⊕ High → ℝ) (c q ω : Low ⊕ High → ℝ) (anchor : High → ℝ)
    {kappa amin amax G Xc b0 g : ℝ}
    (hk : 0 < kappa) (hA : 0 < ∑ j, anchor j)
    (hdom : ∀ i j, kappa * anchor j ≤ edge (Sum.inr i) (Sum.inr j))
    (hcmin : ∀ i, amin ≤ c (Sum.inr i)) (hamin : 0 < amin)
    (hcmax : ∀ i, c (Sum.inr i) ≤ amax)
    (hG : ∀ i, |c (Sum.inr i) * ∑ y, edge (Sum.inr i) y * (q (Sum.inr i) - q y)| ≤ G)
    (hcross : ∀ i, |∑ l, edge (Sum.inr i) (Sum.inl l) * (q (Sum.inr i) - q (Sum.inl l))| ≤ Xc)
    (hω : ∀ i, 0 ≤ ω (Sum.inr i)) (hΩ : 0 < ∑ i, ω (Sum.inr i))
    (hgauge : ∑ x, ω x * q x = 0)
    (hlowg : |∑ l, ω (Sum.inl l) * q (Sum.inl l)| ≤ g * (∑ i, ω (Sum.inr i)) * b0) :
    ∀ i, |c (Sum.inr i) * q (Sum.inr i)| ≤
      amax * (2 * (1 / (kappa * ∑ j, anchor j)) * (G / amin + Xc) + g * b0) := by
  classical
  set A := ∑ j, anchor j with hAdef
  set Ω := ∑ i, ω (Sum.inr i) with hΩdef
  have hLq : ∀ i, |∑ y, edge (Sum.inr i) y * (q (Sum.inr i) - q y)| ≤ G / amin := by
    intro i
    have hc : 0 < c (Sum.inr i) := lt_of_lt_of_le hamin (hcmin i)
    have h1 := hG i
    rw [abs_mul, abs_of_pos hc] at h1
    rw [le_div_iff₀ hamin]
    calc |∑ y, edge (Sum.inr i) y * (q (Sum.inr i) - q y)| * amin
        ≤ |∑ y, edge (Sum.inr i) y * (q (Sum.inr i) - q y)| * c (Sum.inr i) :=
          mul_le_mul_of_nonneg_left (hcmin i) (abs_nonneg _)
      _ = c (Sum.inr i) * |∑ y, edge (Sum.inr i) y * (q (Sum.inr i) - q y)| := mul_comm _ _
      _ ≤ G := h1
  have hsplit : ∀ i, ∑ y, edge (Sum.inr i) y * (q (Sum.inr i) - q y) =
      ∑ l, edge (Sum.inr i) (Sum.inl l) * (q (Sum.inr i) - q (Sum.inl l)) +
      ∑ j, edge (Sum.inr i) (Sum.inr j) * (q (Sum.inr i) - q (Sum.inr j)) :=
    fun i => Fintype.sum_sum_type _
  obtain ⟨imax, -, himax⟩ :=
    Finset.exists_max_image Finset.univ (fun i => q (Sum.inr i)) Finset.univ_nonempty
  obtain ⟨imin, -, himin⟩ :=
    Finset.exists_min_image Finset.univ (fun i => q (Sum.inr i)) Finset.univ_nonempty
  have hmax : ∀ j, q (Sum.inr j) ≤ q (Sum.inr imax) := fun j => himax j (Finset.mem_univ j)
  have hmin : ∀ j, q (Sum.inr imin) ≤ q (Sum.inr j) := fun j => himin j (Finset.mem_univ j)
  have hHmax : kappa * ∑ j, anchor j * (q (Sum.inr imax) - q (Sum.inr j)) ≤
      ∑ j, edge (Sum.inr imax) (Sum.inr j) * (q (Sum.inr imax) - q (Sum.inr j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hd : 0 ≤ q (Sum.inr imax) - q (Sum.inr j) := sub_nonneg.mpr (hmax j)
    calc kappa * (anchor j * (q (Sum.inr imax) - q (Sum.inr j)))
        = (kappa * anchor j) * (q (Sum.inr imax) - q (Sum.inr j)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hdom imax j) hd
  have hHmin : kappa * ∑ j, anchor j * (q (Sum.inr j) - q (Sum.inr imin)) ≤
      -∑ j, edge (Sum.inr imin) (Sum.inr j) * (q (Sum.inr imin) - q (Sum.inr j)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro j _
    have hd : 0 ≤ q (Sum.inr j) - q (Sum.inr imin) := sub_nonneg.mpr (hmin j)
    calc kappa * (anchor j * (q (Sum.inr j) - q (Sum.inr imin)))
        = (kappa * anchor j) * (q (Sum.inr j) - q (Sum.inr imin)) := by ring
      _ ≤ edge (Sum.inr imin) (Sum.inr j) * (q (Sum.inr j) - q (Sum.inr imin)) :=
          mul_le_mul_of_nonneg_right (hdom imin j) hd
      _ = _ := by ring
  have hsumA : ∑ j, anchor j * (q (Sum.inr imax) - q (Sum.inr j)) +
      ∑ j, anchor j * (q (Sum.inr j) - q (Sum.inr imin)) =
      A * (q (Sum.inr imax) - q (Sum.inr imin)) := by
    rw [← Finset.sum_add_distrib, hAdef, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h1 := hLq imax
  have h2 := hLq imin
  rw [hsplit] at h1 h2
  have e1 := abs_le.mp h1
  have e2 := abs_le.mp h2
  have f1 := abs_le.mp (hcross imax)
  have f2 := abs_le.mp (hcross imin)
  have hkA : 0 < kappa * A := mul_pos hk hA
  have hk1 : kappa * (A * (q (Sum.inr imax) - q (Sum.inr imin))) =
      kappa * ∑ j, anchor j * (q (Sum.inr imax) - q (Sum.inr j)) +
        kappa * ∑ j, anchor j * (q (Sum.inr j) - q (Sum.inr imin)) := by
    rw [← hsumA]; ring
  have hoscb : kappa * (A * (q (Sum.inr imax) - q (Sum.inr imin))) ≤ 2 * (G / amin + Xc) := by
    linarith
  have hosc : q (Sum.inr imax) - q (Sum.inr imin) ≤ 2 * (1 / (kappa * A)) * (G / amin + Xc) := by
    have : q (Sum.inr imax) - q (Sum.inr imin) ≤ 2 * (G / amin + Xc) / (kappa * A) := by
      rw [le_div_iff₀ hkA]
      linarith
    calc _ ≤ 2 * (G / amin + Xc) / (kappa * A) := this
      _ = _ := by ring
  intro i
  have hgsplit : ∑ l, ω (Sum.inl l) * q (Sum.inl l) + ∑ j, ω (Sum.inr j) * q (Sum.inr j) = 0 := by
    rw [← Fintype.sum_sum_type (fun x => ω x * q x)]
    exact hgauge
  have hdiff : |∑ j, ω (Sum.inr j) * (q (Sum.inr i) - q (Sum.inr j))| ≤
      Ω * (q (Sum.inr imax) - q (Sum.inr imin)) := by
    calc _ ≤ ∑ j, |ω (Sum.inr j) * (q (Sum.inr i) - q (Sum.inr j))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, ω (Sum.inr j) * (q (Sum.inr imax) - q (Sum.inr imin)) := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul, abs_of_nonneg (hω j)]
          apply mul_le_mul_of_nonneg_left _ (hω j)
          rw [abs_le]
          constructor <;> linarith [hmax i, hmin i, hmax j, hmin j]
      _ = Ω * (q (Sum.inr imax) - q (Sum.inr imin)) := by rw [hΩdef, Finset.sum_mul]
  have hqi : Ω * q (Sum.inr i) =
      ∑ j, ω (Sum.inr j) * (q (Sum.inr i) - q (Sum.inr j)) -
        ∑ l, ω (Sum.inl l) * q (Sum.inl l) := by
    have : ∑ j, ω (Sum.inr j) * (q (Sum.inr i) - q (Sum.inr j)) =
        Ω * q (Sum.inr i) - ∑ j, ω (Sum.inr j) * q (Sum.inr j) := by
      rw [hΩdef, Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    linarith
  have d1 := abs_le.mp hdiff
  have d2 := abs_le.mp hlowg
  have hq : |q (Sum.inr i)| ≤ (q (Sum.inr imax) - q (Sum.inr imin)) + g * b0 := by
    rw [abs_le]
    constructor
    · have : Ω * (-((q (Sum.inr imax) - q (Sum.inr imin)) + g * b0)) ≤ Ω * q (Sum.inr i) := by
        rw [hqi]
        linarith
      exact le_of_mul_le_mul_left this hΩ
    · have : Ω * q (Sum.inr i) ≤ Ω * ((q (Sum.inr imax) - q (Sum.inr imin)) + g * b0) := by
        rw [hqi]
        linarith
      exact le_of_mul_le_mul_left this hΩ
  have hc : 0 < c (Sum.inr i) := lt_of_lt_of_le hamin (hcmin i)
  have hamax0 : 0 ≤ amax := le_trans hc.le (hcmax i)
  rw [abs_mul, abs_of_pos hc]
  calc c (Sum.inr i) * |q (Sum.inr i)| ≤ amax * |q (Sum.inr i)| :=
        mul_le_mul_of_nonneg_right (hcmax i) (abs_nonneg _)
    _ ≤ amax * ((q (Sum.inr imax) - q (Sum.inr imin)) + g * b0) :=
        mul_le_mul_of_nonneg_left hq hamax0
    _ ≤ amax * (2 * (1 / (kappa * A)) * (G / amin + Xc) + g * b0) :=
        mul_le_mul_of_nonneg_left (by linarith) hamax0


section Main

open Erdos390.Full.ContinuumCellGraph Erdos390.Full.PaperWeightedInverseExport
open Erdos390.Full.MovingLowGaugeTransfer

theorem abs_K_le {Band : Type*} [Fintype Band] {epsilon : ℝ} (M : IntervalMesh epsilon Band)
    {C : ℝ}
    (hcov : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, |covarianceKernel s t| ≤ C * s * t)
    (i j : Band) : |M.normalizedKernelCell i j| ≤ C * M.center i * M.length j := by
  have hK : M.normalizedKernelCell i j = Gm M i j / M.harmonicMass i := rfl
  rw [hK, abs_div, abs_of_pos (hm_pos M i), div_le_iff₀ (hm_pos M i)]
  calc |Gm M i j| ≤ C * M.length i * M.length j := abs_Gm_le M hcov i j
    _ = C * M.center i * M.length j * M.harmonicMass i := by rw [← h_mul_c M i]; ring

theorem abs_E_le {Band : Type*} [Fintype Band] {epsilon : ℝ} (M : IntervalMesh epsilon Band)
    {C : ℝ}
    (hcov : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, |covarianceKernel s t| ≤ C * s * t)
    (i j : Band) : |M.sharpKernelEdge i j| ≤ C * M.center j * M.length j := by
  rw [E_eq, abs_mul, abs_neg, abs_of_pos (div_pos (c_pos M j) (len_pos M i))]
  calc M.center j / M.length i * |Gm M i j|
      ≤ M.center j / M.length i * (C * M.length i * M.length j) :=
        mul_le_mul_of_nonneg_left (abs_Gm_le M hcov i j)
          (div_nonneg (c_pos M j).le (len_pos M i).le)
    _ = C * M.center j * M.length j := by
        rw [div_mul_eq_mul_div, div_eq_iff (ne_of_gt (len_pos M i))]
        ring

theorem main {Band Low High : Type*} [Fintype Band] [Fintype Low] [Fintype High] {epsilon : ℝ}
    (M : IntervalMesh epsilon Band) [DecidableEq Band] [Nonempty Band] [Nonempty High]
    (e : Low ⊕ High ≃ Band) (diagonalA : Band → ℝ) (kernelA : Band → Band → ℝ)
    (H alphaA : Band → ℝ)
    {C kappa amin amax alphaAMax lowCenter lowLength totalLength gaugeRatio d residual rowError
      R rho : ℝ}
    (hC : 0 ≤ C)
    (hcov : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, |covarianceKernel s t| ≤ C * s * t)
    (hk : 0 < kappa)
    (hkq : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc epsilon (1 - epsilon),
      kappa ≤ -covarianceKernelQuotient t s)
    (hA : 0 < ∑ i, M.splitHighAnchor e i)
    (hamin : 0 < amin)
    (hcmin : ∀ i : High, amin ≤ M.center (e (Sum.inr i)))
    (hcmax : ∀ i : High, M.center (e (Sum.inr i)) ≤ amax)
    (hamax : 0 ≤ amax) (hc0 : 0 ≤ lowCenter)
    (hclow : ∀ l : Low, M.center (e (Sum.inl l)) ≤ lowCenter)
    (hL0 : 0 ≤ lowLength)
    (hlowlen : ∑ l, M.length (e (Sum.inl l)) ≤ lowLength)
    (hLt : 0 ≤ totalLength)
    (htot : ∑ i, M.length i ≤ totalLength)
    (hH : ∀ i, 0 < H i) (hAlphaA : ∀ i, 0 < alphaA i)
    (halphamax : ∀ i, alphaA i ≤ alphaAMax)
    (hgr : ∑ l, H (e (Sum.inl l)) * alphaA (e (Sum.inl l)) ≤
      gaugeRatio * ∑ i, H (e (Sum.inr i)) * alphaA (e (Sum.inr i)) * M.center (e (Sum.inr i)))
    (hd : d < 1)
    (hdiag : ∀ l, |M.normalizedDiagonalCell (e (Sum.inl l)) - 1| ≤ d)
    (hres0 : 0 ≤ residual)
    (hres : ∀ i, |M.rowResidual i| ≤ residual)
    (hrow0 : 0 ≤ rowError)
    (hrow : ∀ (b : RawGaugeSpace H alphaA) (i : Band),
      |rawOperator diagonalA kernelA b i -
        rawOperator M.normalizedDiagonalCell M.normalizedKernelCell b i| ≤ rowError * ‖b‖)
    (hR0 : 0 ≤ R)
    (hRS : alphaAMax * ∑ i, H i * alphaA i ≤ R * sharpWeightTotal H alphaA)
    (hrhoh : rho ≤ 1 / 2)
    (hrho : alphaAMax * ∑ i, |H i * alphaA i - M.harmonicMass i * M.center i| ≤
      rho * sharpWeightTotal H alphaA)
    (hsmall1 : max ((residual + C * lowCenter * totalLength) / (1 - d))
        (amax * (2 * (1 / (kappa * ∑ i, M.splitHighAnchor e i)) *
          (C * lowCenter * lowLength / amin +
            C * lowLength * ((residual + C * lowCenter * totalLength) / (1 - d))) +
          gaugeRatio * ((residual + C * lowCenter * totalLength) / (1 - d)))) ≤ 1 / 2)
    (hsmall2 : 4 * max (1 / (1 - d)) (amax * (2 * (1 / (kappa * ∑ i, M.splitHighAnchor e i)) *
          (1 / amin + C * lowLength * (1 / (1 - d))) + gaugeRatio * (1 / (1 - d)))) *
        ((1 + R) * (rowError + residual)) ≤ 1 / 2)
    (hTot : sharpWeightTotal H alphaA ≠ 0)
    (b : RawGaugeSpace H alphaA) :
    ‖b‖ ≤ 8 * max (1 / (1 - d)) (amax * (2 * (1 / (kappa * ∑ i, M.splitHighAnchor e i)) *
          (1 / amin + C * lowLength * (1 / (1 - d))) + gaugeRatio * (1 / (1 - d)))) *
        ‖projectedRawLinearMap diagonalA kernelA H alphaA hTot b‖ := by
  classical
  set Clow := 1 / (1 - d) with hClow
  set epsLow := (residual + C * lowCenter * totalLength) / (1 - d) with hepsLow
  set Aanc := ∑ i, M.splitHighAnchor e i with hAanc
  set Cmain := max Clow (amax * (2 * (1 / (kappa * Aanc)) * (1 / amin + C * lowLength * Clow) +
    gaugeRatio * Clow)) with hCmain
  set E0 := max epsLow (amax * (2 * (1 / (kappa * Aanc)) *
    (C * lowCenter * lowLength / amin + C * lowLength * epsLow) + gaugeRatio * epsLow)) with hE0
  set Tb := projectedRawLinearMap diagonalA kernelA H alphaA hTot b with hTbdef
  set N := ‖Tb‖ with hNdef
  set B := ‖b‖ with hBdef
  set bf : Band → ℝ := (b : Band → ℝ) with hbf
  have hd1 : 0 < 1 - d := sub_pos.mpr hd
  have hClow0 : 0 < Clow := by rw [hClow]; exact one_div_pos.mpr hd1
  have hB0 : 0 ≤ B := norm_nonneg _
  have hN0 : 0 ≤ N := norm_nonneg _
  have hbB : ∀ i, |bf i| ≤ B := by
    intro i
    have h := norm_le_pi_norm bf i
    rw [Real.norm_eq_abs] at h
    exact h
  have hTbN : ∀ i, |(Tb : Band → ℝ) i| ≤ N := by
    intro i
    have h := norm_le_pi_norm (Tb : Band → ℝ) i
    rw [Real.norm_eq_abs] at h
    exact h
  -- the operators
  set Ab := rawOperator diagonalA kernelA bf with hAb
  set Ac := rawOperator M.normalizedDiagonalCell M.normalizedKernelCell bf with hAc
  set S := sharpWeightTotal H alphaA with hSdef
  have hS : 0 < S := by
    rw [hSdef]
    unfold sharpWeightTotal sharpWeight
    exact Finset.sum_pos (fun i _ => mul_pos (hH i) (pow_pos (hAlphaA i) 2)) Finset.univ_nonempty
  have hamax' : 0 ≤ alphaAMax :=
    le_trans (hAlphaA (Classical.arbitrary Band)).le (halphamax _)
  set P := ∑ k, H k * alphaA k * Ab k with hPdef
  have hTb_eq : ∀ i, (Tb : Band → ℝ) i = Ab i - alphaA i * (P / S) := fun i => rfl
  set Z := ‖Ac‖ with hZdef
  have hZ0 : 0 ≤ Z := norm_nonneg _
  have hAcZ : ∀ i, |Ac i| ≤ Z := by
    intro i
    have h := norm_le_pi_norm Ac i
    rw [Real.norm_eq_abs] at h
    exact h
  have hrowb : ∀ i, |Ab i - Ac i| ≤ rowError * B := hrow b
  -- the sum of lengths
  have hlen_le : ∀ k, M.length k ≤ H k * alphaA k + |H k * alphaA k - M.harmonicMass k * M.center k| := by
    intro k
    rw [← h_mul_c M k]
    have := neg_abs_le (H k * alphaA k - M.harmonicMass k * M.center k)
    linarith
  have hsumlen : alphaAMax * ∑ k, M.length k ≤ (R + rho) * S := by
    have h1 : ∑ k, M.length k ≤ ∑ k, H k * alphaA k +
        ∑ k, |H k * alphaA k - M.harmonicMass k * M.center k| := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun k _ => hlen_le k)
    have h2 := mul_le_mul_of_nonneg_left h1 hamax'
    linarith
  -- decomposition of P
  have hPdecomp : P = ∑ k, M.length k * Ac k +
      ∑ k, (H k * alphaA k - M.harmonicMass k * M.center k) * Ac k +
      ∑ k, H k * alphaA k * (Ab k - Ac k) := by
    rw [hPdef, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [← h_mul_c M k]
    ring
  have hP1 : |∑ k, M.length k * Ac k| ≤ residual * B * ∑ k, M.length k := by
    rw [hAc, sum_len_Ac M bf]
    calc |∑ k, M.length k * M.rowResidual k * bf k|
        ≤ ∑ k, |M.length k * M.rowResidual k * bf k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, M.length k * (residual * B) := by
          apply Finset.sum_le_sum
          intro k _
          rw [abs_mul, abs_mul, abs_of_pos (len_pos M k), mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (len_pos M k).le
          exact mul_le_mul (hres k) (hbB k) (abs_nonneg _) hres0
      _ = residual * B * ∑ k, M.length k := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  have hP2 : |∑ k, (H k * alphaA k - M.harmonicMass k * M.center k) * Ac k| ≤
      Z * ∑ k, |H k * alphaA k - M.harmonicMass k * M.center k| := by
    calc _ ≤ ∑ k, |(H k * alphaA k - M.harmonicMass k * M.center k) * Ac k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, |H k * alphaA k - M.harmonicMass k * M.center k| * Z := by
          apply Finset.sum_le_sum
          intro k _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hAcZ k) (abs_nonneg _)
      _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  have hP3 : |∑ k, H k * alphaA k * (Ab k - Ac k)| ≤ rowError * B * ∑ k, H k * alphaA k := by
    calc _ ≤ ∑ k, |H k * alphaA k * (Ab k - Ac k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, H k * alphaA k * (rowError * B) := by
          apply Finset.sum_le_sum
          intro k _
          rw [abs_mul, abs_of_pos (mul_pos (hH k) (hAlphaA k))]
          exact mul_le_mul_of_nonneg_left (hrowb k) (mul_pos (hH k) (hAlphaA k)).le
      _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  have hPabs : alphaAMax * |P| ≤ ((R + rho) * residual * B + rho * Z + R * rowError * B) * S := by
    have htri : |P| ≤ residual * B * ∑ k, M.length k +
        Z * ∑ k, |H k * alphaA k - M.harmonicMass k * M.center k| +
        rowError * B * ∑ k, H k * alphaA k := by
      rw [hPdecomp]
      refine le_trans (abs_add_le _ _) ?_
      refine le_trans (add_le_add (abs_add_le _ _) le_rfl) ?_
      linarith [hP1, hP2, hP3]
    have hm := mul_le_mul_of_nonneg_left htri hamax'
    have hrB : 0 ≤ residual * B := mul_nonneg hres0 hB0
    have hwB : 0 ≤ rowError * B := mul_nonneg hrow0 hB0
    have k1 : residual * B * (alphaAMax * ∑ k, M.length k) ≤ residual * B * ((R + rho) * S) :=
      mul_le_mul_of_nonneg_left hsumlen hrB
    have k2 : Z * (alphaAMax * ∑ k, |H k * alphaA k - M.harmonicMass k * M.center k|) ≤
        Z * (rho * S) := mul_le_mul_of_nonneg_left hrho hZ0
    have k3 : rowError * B * (alphaAMax * ∑ k, H k * alphaA k) ≤ rowError * B * (R * S) :=
      mul_le_mul_of_nonneg_left hRS hwB
    linarith only [hm, k1, k2, k3]
  have hlam : alphaAMax * |P / S| ≤ (R + rho) * residual * B + rho * Z + R * rowError * B := by
    rw [abs_div, abs_of_pos hS, ← mul_div_assoc, div_le_iff₀ hS]
    exact hPabs
  have hAb_le : ∀ i, |Ab i| ≤ N + alphaAMax * |P / S| := by
    intro i
    have h1 : Ab i = (Tb : Band → ℝ) i + alphaA i * (P / S) := by rw [hTb_eq]; ring
    rw [h1]
    calc |(Tb : Band → ℝ) i + alphaA i * (P / S)| ≤ |(Tb : Band → ℝ) i| + |alphaA i * (P / S)| :=
          abs_add_le _ _
      _ ≤ N + alphaAMax * |P / S| := by
          rw [abs_mul, abs_of_pos (hAlphaA i)]
          exact add_le_add (hTbN i) (mul_le_mul_of_nonneg_right (halphamax i) (abs_nonneg _))
  have hZle : Z ≤ N + ((R + rho) * residual * B + rho * Z + R * rowError * B) + rowError * B := by
    have hr : 0 ≤ N + ((R + rho) * residual * B + rho * Z + R * rowError * B) + rowError * B := by
      have := mul_nonneg hrow0 hB0
      have := mul_nonneg hamax' (abs_nonneg (P / S))
      linarith [hlam, hN0]
    rw [hZdef, pi_norm_le_iff_of_nonneg hr]
    intro i
    rw [Real.norm_eq_abs]
    have h1 := hAb_le i
    have h2 := hrowb i
    have h3 : |Ac i| ≤ |Ab i| + |Ab i - Ac i| := by
      have := abs_sub_abs_le_abs_sub (Ac i) (Ab i)
      rw [abs_sub_comm (Ac i) (Ab i)] at this
      linarith
    linarith
  have hZ2 : Z ≤ 2 * N + 2 * (R + rho) * residual * B + 2 * (R + 1) * rowError * B := by
    have : rho * Z ≤ 1 / 2 * Z := mul_le_mul_of_nonneg_right hrhoh hZ0
    linarith only [hZle, this]
  -- G
  set G := Z + residual * B with hGdef
  have hG0 : 0 ≤ G := add_nonneg hZ0 (mul_nonneg hres0 hB0)
  have hGle : G ≤ 2 * N + 2 * (1 + R) * (rowError + residual) * B := by
    have : rho * (residual * B) ≤ 1 / 2 * (residual * B) :=
      mul_le_mul_of_nonneg_right hrhoh (mul_nonneg hres0 hB0)
    linarith only [hZ2, this, hGdef]
  -- graph operator bound
  set q : Band → ℝ := fun i => bf i / M.center i with hq
  have hGx : ∀ i, |M.center i * ∑ j, M.sharpKernelEdge i j * (q i - q j)| ≤ G := by
    intro i
    have h := Ac_eq M bf i
    have h' : M.center i * ∑ j, M.sharpKernelEdge i j * (q i - q j) = Ac i - bf i * M.rowResidual i := by
      rw [hAc, h]; simp only [hq]; ring
    rw [h', hGdef]
    calc |Ac i - bf i * M.rowResidual i| ≤ |Ac i| + |bf i * M.rowResidual i| := abs_sub _ _
      _ ≤ Z + B * residual := by
          rw [abs_mul]
          exact add_le_add (hAcZ i) (mul_le_mul (hbB i) (hres i) (abs_nonneg _) hB0)
      _ = Z + residual * B := by ring
  -- low bound
  set b0 := Clow * G + epsLow * B with hb0
  have hepsLow0 : 0 ≤ epsLow := by
    rw [hepsLow]
    apply div_nonneg _ hd1.le
    have := mul_nonneg (mul_nonneg hC hc0) hLt
    linarith
  have hb00 : 0 ≤ b0 := add_nonneg (mul_nonneg hClow0.le hG0) (mul_nonneg hepsLow0 hB0)
  have hlow : ∀ l, |bf (e (Sum.inl l))| ≤ b0 := by
    intro l
    set i := e (Sum.inl l) with hi
    have hDi : 1 - d ≤ M.normalizedDiagonalCell i := by
      have := abs_le.mp (hdiag l)
      linarith [this.1]
    have hDpos : 0 < M.normalizedDiagonalCell i := lt_of_lt_of_le hd1 hDi
    have hKsum : |∑ j, M.normalizedKernelCell i j * bf j| ≤ C * lowCenter * totalLength * B := by
      calc _ ≤ ∑ j, |M.normalizedKernelCell i j * bf j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, C * M.center i * M.length j * B := by
            apply Finset.sum_le_sum
            intro j _
            rw [abs_mul]
            exact mul_le_mul (abs_K_le M hcov i j) (hbB j) (abs_nonneg _)
              (mul_nonneg (mul_nonneg hC (c_pos M i).le) (len_pos M j).le)
        _ = C * M.center i * B * ∑ j, M.length j := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
        _ ≤ C * lowCenter * B * totalLength := by
            apply mul_le_mul _ htot (Finset.sum_nonneg (fun j _ => (len_pos M j).le))
              (mul_nonneg (mul_nonneg hC hc0) hB0)
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hclow l) hC) hB0
        _ = C * lowCenter * totalLength * B := by ring
    have hid : M.normalizedDiagonalCell i * bf i =
        bf i * M.rowResidual i + M.center i * ∑ j, M.sharpKernelEdge i j * (q i - q j) -
          ∑ j, M.normalizedKernelCell i j * bf j := by
      have h := Ac_eq M bf i
      have h2 : Ac i = M.normalizedDiagonalCell i * bf i + ∑ j, M.normalizedKernelCell i j * bf j := rfl
      rw [hAc] at h2
      simp only [hq]
      linarith
    have hmain : |bf i| * (1 - d) ≤ B * residual + G + C * lowCenter * totalLength * B := by
      calc |bf i| * (1 - d) ≤ |bf i| * M.normalizedDiagonalCell i :=
            mul_le_mul_of_nonneg_left hDi (abs_nonneg _)
        _ = |M.normalizedDiagonalCell i * bf i| := by
            rw [abs_mul, abs_of_pos hDpos, mul_comm]
        _ ≤ |bf i * M.rowResidual i| + |M.center i * ∑ j, M.sharpKernelEdge i j * (q i - q j)| +
              |∑ j, M.normalizedKernelCell i j * bf j| := by
            rw [hid]
            have t1 := abs_sub (bf i * M.rowResidual i + M.center i * ∑ j, M.sharpKernelEdge i j * (q i - q j))
              (∑ j, M.normalizedKernelCell i j * bf j)
            have t2 := abs_add_le (bf i * M.rowResidual i) (M.center i * ∑ j, M.sharpKernelEdge i j * (q i - q j))
            linarith
        _ ≤ B * residual + G + C * lowCenter * totalLength * B := by
            rw [abs_mul]
            have := mul_le_mul (hbB i) (hres i) (abs_nonneg _) hB0
            linarith [hGx i]
    rw [hb0, hClow, hepsLow]
    have : |bf i| ≤ (B * residual + G + C * lowCenter * totalLength * B) / (1 - d) := by
      rw [le_div_iff₀ hd1]; exact hmain
    calc |bf i| ≤ (B * residual + G + C * lowCenter * totalLength * B) / (1 - d) := this
      _ = 1 / (1 - d) * G + (residual + C * lowCenter * totalLength) / (1 - d) * B := by
          field_simp
          ring
  -- cross bound
  set Xc := C * lowCenter * lowLength * B / amin + C * lowLength * b0 with hXc
  have hcross : ∀ i : High, |∑ l, M.sharpKernelEdge (e (Sum.inr i)) (e (Sum.inl l)) *
      (q (e (Sum.inr i)) - q (e (Sum.inl l)))| ≤ Xc := by
    intro i
    have hci : 0 < M.center (e (Sum.inr i)) := lt_of_lt_of_le hamin (hcmin i)
    have hqi : M.center (e (Sum.inr i)) * |q (e (Sum.inr i))| ≤ B := by
      simp only [hq]
      rw [abs_div, abs_of_pos hci, mul_div_cancel₀ _ (ne_of_gt hci)]
      exact hbB _
    have hqi' : |q (e (Sum.inr i))| ≤ B / amin := by
      rw [le_div_iff₀ hamin]
      calc |q (e (Sum.inr i))| * amin ≤ |q (e (Sum.inr i))| * M.center (e (Sum.inr i)) :=
            mul_le_mul_of_nonneg_left (hcmin i) (abs_nonneg _)
        _ ≤ B := by rw [mul_comm]; exact hqi
    have hterm : ∀ l, |M.sharpKernelEdge (e (Sum.inr i)) (e (Sum.inl l)) *
        (q (e (Sum.inr i)) - q (e (Sum.inl l)))| ≤
          C * M.length (e (Sum.inl l)) * (lowCenter * (B / amin) + b0) := by
      intro l
      have hcl : 0 < M.center (e (Sum.inl l)) := c_pos M _
      have hql : M.center (e (Sum.inl l)) * |q (e (Sum.inl l))| ≤ b0 := by
        simp only [hq]
        rw [abs_div, abs_of_pos hcl, mul_div_cancel₀ _ (ne_of_gt hcl)]
        exact hlow l
      have hE := abs_E_le M hcov (e (Sum.inr i)) (e (Sum.inl l))
      rw [abs_mul]
      have hsub : |q (e (Sum.inr i)) - q (e (Sum.inl l))| ≤
          |q (e (Sum.inr i))| + |q (e (Sum.inl l))| := abs_sub _ _
      have hCl : 0 ≤ C * M.length (e (Sum.inl l)) := mul_nonneg hC (len_pos M _).le
      calc |M.sharpKernelEdge (e (Sum.inr i)) (e (Sum.inl l))| *
            |q (e (Sum.inr i)) - q (e (Sum.inl l))|
          ≤ (C * M.center (e (Sum.inl l)) * M.length (e (Sum.inl l))) *
              (|q (e (Sum.inr i))| + |q (e (Sum.inl l))|) :=
            mul_le_mul hE hsub (abs_nonneg _) (le_trans (abs_nonneg _) hE)
        _ = C * M.length (e (Sum.inl l)) *
              (M.center (e (Sum.inl l)) * |q (e (Sum.inr i))| +
                M.center (e (Sum.inl l)) * |q (e (Sum.inl l))|) := by ring
        _ ≤ C * M.length (e (Sum.inl l)) * (lowCenter * (B / amin) + b0) := by
            apply mul_le_mul_of_nonneg_left _ hCl
            apply add_le_add _ hql
            exact mul_le_mul (hclow l) hqi' (abs_nonneg _) hc0
    have hnn : 0 ≤ lowCenter * (B / amin) + b0 :=
      add_nonneg (mul_nonneg hc0 (div_nonneg hB0 hamin.le)) hb00
    calc _ ≤ ∑ l, |M.sharpKernelEdge (e (Sum.inr i)) (e (Sum.inl l)) *
          (q (e (Sum.inr i)) - q (e (Sum.inl l)))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l, C * M.length (e (Sum.inl l)) * (lowCenter * (B / amin) + b0) :=
          Finset.sum_le_sum (fun l _ => hterm l)
      _ = C * (lowCenter * (B / amin) + b0) * ∑ l, M.length (e (Sum.inl l)) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; ring
      _ ≤ C * (lowCenter * (B / amin) + b0) * lowLength :=
          mul_le_mul_of_nonneg_left hlowlen (mul_nonneg hC hnn)
      _ = Xc := by rw [hXc]; ring
  -- maximum principle
  have hhigh := maxp (Low := Low) (High := High)
    (fun x y => M.sharpKernelEdge (e x) (e y)) (fun x => M.center (e x)) (fun x => q (e x))
    (fun x => H (e x) * alphaA (e x) * M.center (e x)) (M.splitHighAnchor e)
    (kappa := kappa) (amin := amin) (amax := amax) (G := G) (Xc := Xc) (b0 := b0)
    (g := gaugeRatio) hk hA
    (by
      intro i j
      unfold IntervalMesh.splitHighAnchor IntervalMesh.anchor
      split_ifs with hj
      · exact E_ge M hkq _ _ hj
      · rw [mul_zero]; exact E_nonneg M _ _)
    hcmin hamin hcmax
    (by
      intro i
      have h := hGx (e (Sum.inr i))
      rw [← Equiv.sum_comp e (fun j => M.sharpKernelEdge (e (Sum.inr i)) j *
        (q (e (Sum.inr i)) - q j))] at h
      exact h)
    hcross
    (fun i => (mul_pos (mul_pos (hH _) (hAlphaA _)) (c_pos M _)).le)
    (Finset.sum_pos (fun i _ => mul_pos (mul_pos (hH _) (hAlphaA _)) (c_pos M _))
      Finset.univ_nonempty)
    (by
      have hgb : ∑ j, H j * alphaA j * bf j = 0 := b.2
      rw [← Equiv.sum_comp e (fun j => H j * alphaA j * bf j)] at hgb
      rw [← hgb]
      apply Finset.sum_congr rfl
      intro x _
      simp only [hq]
      have := ne_of_gt (c_pos M (e x))
      field_simp)
    (by
      have heq : ∑ l, H (e (Sum.inl l)) * alphaA (e (Sum.inl l)) * M.center (e (Sum.inl l)) *
          q (e (Sum.inl l)) = ∑ l, H (e (Sum.inl l)) * alphaA (e (Sum.inl l)) * bf (e (Sum.inl l)) := by
        apply Finset.sum_congr rfl
        intro l _
        simp only [hq]
        have := ne_of_gt (c_pos M (e (Sum.inl l)))
        field_simp
      show |∑ l, H (e (Sum.inl l)) * alphaA (e (Sum.inl l)) * M.center (e (Sum.inl l)) *
          q (e (Sum.inl l))| ≤ gaugeRatio *
          (∑ i, H (e (Sum.inr i)) * alphaA (e (Sum.inr i)) * M.center (e (Sum.inr i))) * b0
      rw [heq]
      calc _ ≤ ∑ l, |H (e (Sum.inl l)) * alphaA (e (Sum.inl l)) * bf (e (Sum.inl l))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ l, H (e (Sum.inl l)) * alphaA (e (Sum.inl l)) * b0 := by
            apply Finset.sum_le_sum
            intro l _
            rw [abs_mul, abs_of_pos (mul_pos (hH _) (hAlphaA _))]
            exact mul_le_mul_of_nonneg_left (hlow l) (mul_pos (hH _) (hAlphaA _)).le
        _ = b0 * ∑ l, H (e (Sum.inl l)) * alphaA (e (Sum.inl l)) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; ring
        _ ≤ b0 * (gaugeRatio * ∑ i, H (e (Sum.inr i)) * alphaA (e (Sum.inr i)) *
              M.center (e (Sum.inr i))) := mul_le_mul_of_nonneg_left hgr hb00
        _ = _ := by ring)
  -- every coordinate
  have hall : ∀ j, |bf j| ≤ Cmain * G + E0 * B := by
    intro j
    obtain ⟨x, rfl⟩ := e.surjective j
    cases x with
    | inl l =>
        calc |bf (e (Sum.inl l))| ≤ b0 := hlow l
          _ = Clow * G + epsLow * B := hb0
          _ ≤ Cmain * G + E0 * B :=
              add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hG0)
                (mul_le_mul_of_nonneg_right (le_max_left _ _) hB0)
    | inr i =>
        have h := hhigh i
        have hcq : M.center (e (Sum.inr i)) * q (e (Sum.inr i)) = bf (e (Sum.inr i)) := by
          simp only [hq]
          exact mul_div_cancel₀ _ (ne_of_gt (c_pos M _))
        simp only at h
        rw [hcq] at h
        calc |bf (e (Sum.inr i))| ≤ _ := h
          _ = G * (amax * (2 * (1 / (kappa * Aanc)) * (1 / amin + C * lowLength * Clow) +
                gaugeRatio * Clow)) +
              B * (amax * (2 * (1 / (kappa * Aanc)) *
                (C * lowCenter * lowLength / amin + C * lowLength * epsLow) +
                gaugeRatio * epsLow)) := by
              rw [hXc, hb0]; ring
          _ ≤ Cmain * G + E0 * B := by
              rw [mul_comm G, mul_comm B]
              exact add_le_add (mul_le_mul_of_nonneg_right (le_max_right _ _) hG0)
                (mul_le_mul_of_nonneg_right (le_max_right _ _) hB0)
  have hCmain0 : 0 ≤ Cmain := le_trans hClow0.le (le_max_left _ _)
  have hBle : B ≤ Cmain * G + E0 * B := by
    have hr : 0 ≤ Cmain * G + E0 * B := le_trans (abs_nonneg _) (hall (Classical.arbitrary Band))
    have h : ‖bf‖ ≤ Cmain * G + E0 * B := by
      rw [pi_norm_le_iff_of_nonneg hr]
      intro j
      rw [Real.norm_eq_abs]
      exact hall j
    exact h
  have hE0B : E0 * B ≤ 1 / 2 * B := mul_le_mul_of_nonneg_right hsmall1 hB0
  have hB2 : B ≤ 2 * (Cmain * G) := by linarith
  have hCG : Cmain * G ≤ Cmain * (2 * N + 2 * (1 + R) * (rowError + residual) * B) :=
    mul_le_mul_of_nonneg_left hGle hCmain0
  have hsm : 4 * Cmain * ((1 + R) * (rowError + residual)) * B ≤ 1 / 2 * B :=
    mul_le_mul_of_nonneg_right hsmall2 hB0
  linarith only [hB2, hCG, hsm]

end Main

end D45

set_option maxHeartbeats 4000000 in
open BigOperators in
theorem solution :
∀ {Band : Type u_1} {Low : Type u_2} {High : Type u_3} [inst : Fintype.{u_1} Band] [inst_1 : Fintype.{u_2} Low]
  [inst_2 : Fintype.{u_3} High] {epsilon : Real} (M : Erdos390.Full.ContinuumCellGraph.IntervalMesh.{u_1} epsilon Band)
  [inst_3 : DecidableEq.{u_1 + 1} Band] [inst_4 : Nonempty.{u_1 + 1} Band] [Nonempty.{u_3 + 1} High]
  (e : Equiv.{max (u_3 + 1) (u_2 + 1), u_1 + 1} (Sum.{u_2, u_3} Low High) Band) (diagonalA : Band → Real)
  (kernelA : Band → Band → Real) (H alphaA : Band → Real)
  {C kappa amin amax alphaAMax lowCenter lowLength totalLength gaugeRatio d residual rowError R rho : Real},
  LE.le.{0} (0 : Real) C →
    (∀ (s : Real),
        Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) s →
          ∀ (t : Real),
            Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) t →
              LE.le.{0} (abs.{0} (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel s t))
                (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C s) t)) →
      LT.lt.{0} (0 : Real) kappa →
        (∀ (s : Real),
            Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) s →
              ∀ (t : Real),
                Membership.mem.{0, 0} (Set.Icc.{0} epsilon (HSub.hSub.{0, 0, 0} (1 : Real) epsilon)) t →
                  LE.le.{0} kappa (Neg.neg.{0} (Erdos390.Full.ConditionedPoissonLimit.covarianceKernelQuotient t s))) →
          LT.lt.{0} (0 : Real)
              (∑ i, Erdos390.Full.ContinuumCellGraph.IntervalMesh.splitHighAnchor.{u_1, u_2, u_3} M e i) →
            LT.lt.{0} (0 : Real) amin →
              (∀ (i : High),
                  LE.le.{0} amin
                    (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M (e (Sum.inr.{u_2, u_3} i)))) →
                (∀ (i : High),
                    LE.le.{0} (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M (e (Sum.inr.{u_2, u_3} i)))
                      amax) →
                  LE.le.{0} (0 : Real) amax →
                    LE.le.{0} (0 : Real) lowCenter →
                      (∀ (l : Low),
                          LE.le.{0}
                            (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M (e (Sum.inl.{u_2, u_3} l)))
                            lowCenter) →
                        LE.le.{0} (0 : Real) lowLength →
                          LE.le.{0}
                              (∑ l,
                                Erdos390.Full.ContinuumCellGraph.IntervalMesh.length.{u_1} M (e (Sum.inl.{u_2, u_3} l)))
                              lowLength →
                            LE.le.{0} (0 : Real) totalLength →
                              LE.le.{0} (∑ i, Erdos390.Full.ContinuumCellGraph.IntervalMesh.length.{u_1} M i)
                                  totalLength →
                                ∀ (hH : ∀ (i : Band), LT.lt.{0} (0 : Real) (H i))
                                  (hAlphaA : ∀ (i : Band), LT.lt.{0} (0 : Real) (alphaA i)),
                                  (∀ (i : Band), LE.le.{0} (alphaA i) alphaAMax) →
                                    LE.le.{0}
                                        (∑ l,
                                          HMul.hMul.{0, 0, 0} (H (e (Sum.inl.{u_2, u_3} l)))
                                            (alphaA (e (Sum.inl.{u_2, u_3} l))))
                                        (HMul.hMul.{0, 0, 0} gaugeRatio
                                          (∑ i,
                                            HMul.hMul.{0, 0, 0}
                                              (HMul.hMul.{0, 0, 0} (H (e (Sum.inr.{u_2, u_3} i)))
                                                (alphaA (e (Sum.inr.{u_2, u_3} i))))
                                              (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M
                                                (e (Sum.inr.{u_2, u_3} i))))) →
                                      LT.lt.{0} d (1 : Real) →
                                        (∀ (l : Low),
                                            LE.le.{0}
                                              (abs.{0}
                                                (HSub.hSub.{0, 0, 0}
                                                  (Erdos390.Full.ContinuumCellGraph.IntervalMesh.normalizedDiagonalCell.{u_1}
                                                    M (e (Sum.inl.{u_2, u_3} l)))
                                                  (1 : Real)))
                                              d) →
                                          LE.le.{0} (0 : Real) residual →
                                            (∀ (i : Band),
                                                LE.le.{0}
                                                  (abs.{0}
                                                    (Erdos390.Full.ContinuumCellGraph.IntervalMesh.rowResidual.{u_1} M
                                                      i))
                                                  residual) →
                                              LE.le.{0} (0 : Real) rowError →
                                                (∀
                                                    (b :
                                                      ↥(Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{u_1} H
                                                          alphaA))
                                                    (i : Band),
                                                    LE.le.{0}
                                                      (abs.{0}
                                                        (HSub.hSub.{0, 0, 0}
                                                          (Erdos390.Full.PaperWeightedInverseExport.rawOperator.{u_1}
                                                            diagonalA kernelA (↑b) i)
                                                          (Erdos390.Full.PaperWeightedInverseExport.rawOperator.{u_1}
                                                            (Erdos390.Full.ContinuumCellGraph.IntervalMesh.normalizedDiagonalCell.{u_1}
                                                              M)
                                                            (Erdos390.Full.ContinuumCellGraph.IntervalMesh.normalizedKernelCell.{u_1}
                                                              M)
                                                            (↑b) i)))
                                                      (HMul.hMul.{0, 0, 0} rowError (Norm.norm.{u_1} b))) →
                                                  LE.le.{0} (0 : Real) R →
                                                    LE.le.{0}
                                                        (HMul.hMul.{0, 0, 0} alphaAMax
                                                          (∑ i, HMul.hMul.{0, 0, 0} (H i) (alphaA i)))
                                                        (HMul.hMul.{0, 0, 0} R
                                                          (Erdos390.Full.MovingLowGaugeTransfer.sharpWeightTotal.{u_1} H
                                                            alphaA)) →
                                                      LE.le.{0} rho (1 / 2 : Real) →
                                                        LE.le.{0}
                                                            (HMul.hMul.{0, 0, 0} alphaAMax
                                                              (∑ i,
                                                                abs.{0}
                                                                  (HSub.hSub.{0, 0, 0}
                                                                    (HMul.hMul.{0, 0, 0} (H i) (alphaA i))
                                                                    (HMul.hMul.{0, 0, 0}
                                                                      (Erdos390.Full.ContinuumCellGraph.IntervalMesh.harmonicMass.{u_1}
                                                                        M i)
                                                                      (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1}
                                                                        M i)))))
                                                            (HMul.hMul.{0, 0, 0} rho
                                                              (Erdos390.Full.MovingLowGaugeTransfer.sharpWeightTotal.{u_1}
                                                                H alphaA)) →
                                                          (have epsLow :=
                                                              HDiv.hDiv.{0, 0, 0}
                                                                (HAdd.hAdd.{0, 0, 0} residual
                                                                  (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C lowCenter)
                                                                    totalLength))
                                                                (HSub.hSub.{0, 0, 0} (1 : Real) d);
                                                            LE.le.{0}
                                                              (Max.max.{0} epsLow
                                                                (HMul.hMul.{0, 0, 0} amax
                                                                  (HAdd.hAdd.{0, 0, 0}
                                                                    (HMul.hMul.{0, 0, 0}
                                                                      (HMul.hMul.{0, 0, 0} (2 : Real)
                                                                        (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                          (HMul.hMul.{0, 0, 0} kappa
                                                                            (∑ i,
                                                                              Erdos390.Full.ContinuumCellGraph.IntervalMesh.splitHighAnchor.{u_1,
                                                                                  u_2, u_3}
                                                                                M e i))))
                                                                      (HAdd.hAdd.{0, 0, 0}
                                                                        (HDiv.hDiv.{0, 0, 0}
                                                                          (HMul.hMul.{0, 0, 0}
                                                                            (HMul.hMul.{0, 0, 0} C lowCenter) lowLength)
                                                                          amin)
                                                                        (HMul.hMul.{0, 0, 0}
                                                                          (HMul.hMul.{0, 0, 0} C lowLength) epsLow)))
                                                                    (HMul.hMul.{0, 0, 0} gaugeRatio epsLow))))
                                                              (1 / 2 : Real)) →
                                                            (have Clow :=
                                                                HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                  (HSub.hSub.{0, 0, 0} (1 : Real) d);
                                                              have Cmain :=
                                                                Max.max.{0} Clow
                                                                  (HMul.hMul.{0, 0, 0} amax
                                                                    (HAdd.hAdd.{0, 0, 0}
                                                                      (HMul.hMul.{0, 0, 0}
                                                                        (HMul.hMul.{0, 0, 0} (2 : Real)
                                                                          (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                            (HMul.hMul.{0, 0, 0} kappa
                                                                              (∑ i,
                                                                                Erdos390.Full.ContinuumCellGraph.IntervalMesh.splitHighAnchor.{u_1,
                                                                                    u_2, u_3}
                                                                                  M e i))))
                                                                        (HAdd.hAdd.{0, 0, 0}
                                                                          (HDiv.hDiv.{0, 0, 0} (1 : Real) amin)
                                                                          (HMul.hMul.{0, 0, 0}
                                                                            (HMul.hMul.{0, 0, 0} C lowLength) Clow)))
                                                                      (HMul.hMul.{0, 0, 0} gaugeRatio Clow)));
                                                              LE.le.{0}
                                                                (HMul.hMul.{0, 0, 0}
                                                                  (HMul.hMul.{0, 0, 0} (4 : Real) Cmain)
                                                                  (HMul.hMul.{0, 0, 0}
                                                                    (HAdd.hAdd.{0, 0, 0} (1 : Real) R)
                                                                    (HAdd.hAdd.{0, 0, 0} rowError residual)))
                                                                (1 / 2 : Real)) →
                                                              ∀
                                                                (b :
                                                                  ↥(Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{u_1}
                                                                      H alphaA)),
                                                                LE.le.{0} (Norm.norm.{u_1} b)
                                                                  (HMul.hMul.{0, 0, 0}
                                                                    (HMul.hMul.{0, 0, 0} (8 : Real)
                                                                      (Max.max.{0}
                                                                        (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                          (HSub.hSub.{0, 0, 0} (1 : Real) d))
                                                                        (HMul.hMul.{0, 0, 0} amax
                                                                          (HAdd.hAdd.{0, 0, 0}
                                                                            (HMul.hMul.{0, 0, 0}
                                                                              (HMul.hMul.{0, 0, 0} (2 : Real)
                                                                                (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                                  (HMul.hMul.{0, 0, 0} kappa
                                                                                    (∑ i,
                                                                                      Erdos390.Full.ContinuumCellGraph.IntervalMesh.splitHighAnchor.{u_1,
                                                                                          u_2, u_3}
                                                                                        M e i))))
                                                                              (HAdd.hAdd.{0, 0, 0}
                                                                                (HDiv.hDiv.{0, 0, 0} (1 : Real) amin)
                                                                                (HMul.hMul.{0, 0, 0}
                                                                                  (HMul.hMul.{0, 0, 0} C lowLength)
                                                                                  (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                                    (HSub.hSub.{0, 0, 0} (1 : Real)
                                                                                      d)))))
                                                                            (HMul.hMul.{0, 0, 0} gaugeRatio
                                                                              (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                                (HSub.hSub.{0, 0, 0} (1 : Real) d)))))))
                                                                    (Norm.norm.{u_1}
                                                                      ((Erdos390.Full.PaperWeightedInverseExport.projectedRawLinearMap.{u_1}
                                                                          diagonalA kernelA H alphaA
                                                                          (ne_of_gt.{0}
                                                                            (id.{0}
                                                                              (id.{0}
                                                                                (Finset.sum_pos.{u_1, 0}
                                                                                  (fun i _hi =>
                                                                                    mul_pos.{0} (hH i)
                                                                                      (sq_pos_of_pos.{0} (hAlphaA i)))
                                                                                  Finset.univ_nonempty.{u_1})))))
                                                                        b))) := by
  intro Band Low High _ _ _ epsilon M _ _ _ e diagonalA kernelA H alphaA C kappa amin amax alphaAMax
    lowCenter lowLength totalLength gaugeRatio d residual rowError R rho hC hcov hk hkq hA hamin
    hcmin hcmax hamax hc0 hclow hL0 hlowlen hLt htot hH hAlphaA halphamax hgr hd hdiag hres0 hres
    hrow0 hrow hR0 hRS hrhoh hrho hsmall1 hsmall2 b
  exact D45.main M e diagonalA kernelA H alphaA hC hcov hk hkq hA hamin hcmin hcmax hamax hc0 hclow
    hL0 hlowlen hLt htot hH hAlphaA halphamax hgr hd hdiag hres0 hres hrow0 hrow hR0 hRS hrhoh hrho
    hsmall1 hsmall2 _ b
