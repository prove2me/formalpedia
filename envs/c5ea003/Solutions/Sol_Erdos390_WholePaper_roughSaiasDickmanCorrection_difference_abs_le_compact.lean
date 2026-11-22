-- Prove2me | solution 1 for Erdos390.WholePaper.roughSaiasDickmanCorrection_difference_abs_le_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:48:52.54017+00:00
-- url     : https://prove2.me/submissions/22f2b66d-d65a-4465-90f1-341c165a2d4a

import Definitions.Def_erdos390_remaining_analytic_propositions_008
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006

/- Source module: Erdos390.WholePaper.RoughBalancedFriableResidualReduction -/
section


/-!
# Residual cancellation in the balanced four-endpoint friable block

The closed de Bruijn theorem controls the endpoint residual

`R(X,y) = Psi(X,y) - X * rho(log X / log y)`

by `O(X / log y)`.  Applying that estimate independently at four
endpoints loses one logarithm.  This file avoids that lossy triangle
inequality.  It proves that the literal four-endpoint residual is exactly
two *short residual increments* plus one broad increment whose coefficient
already contains `1/L`.

It also records the exact reverse Buchstab recurrence for `R`, using one
common prime interval for both endpoints.  The remaining missing analytic
input is thereby reduced to a local regularity inequality for `R`; it is
strictly an estimate for the genuine friable counting function and contains
no selector, row, rounding, or feasibility conclusion.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## The genuine endpoint residual -/















/-! ## Exact reverse Buchstab recurrence for the residual -/













/-! ## Verified regularity of the Dickman main term -/

/-- Symmetric compact one-Lipschitz control of the already constructed
Dickman function. -/
theorem roughRho_abs_sub_le_abs_of_le_five
    {a b : ℝ} (ha5 : a ≤ 5) (hb5 : b ≤ 5) :
    |rho a - rho b| ≤ |a - b| := by
  by_cases hab : a ≤ b
  · have h := FriableAsymptotic.rho_lipschitz_of_le_five hab hb5
    rw [abs_sub_comm (rho a), abs_sub_comm a]
    exact h.trans_eq (abs_of_nonneg (sub_nonneg.mpr hab)).symm
  · have hba : b ≤ a := le_of_not_ge hab
    have h := FriableAsymptotic.rho_lipschitz_of_le_five hba ha5
    exact h.trans_eq (abs_of_nonneg (sub_nonneg.mpr hba)).symm





/-! ## The literal four-endpoint residual collapse -/











/-! ## The one remaining analytic inequality -/







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasNormalization -/
section


/-!
# The finite de Bruijn--Saias normal form on the five Dickman faces

Section 8.5 of the paper uses the integration-by-parts identity

`Lambda(z,y) = z * G_y(log z / log y) - fract z`,

where

`G_y(u) = rho(u) - integral rho'(u-v) * fract(y^v) * y^(-v) dv`.

This file formalizes the finite normal form, its exact initial face, the
compact bounded-variation datum behind the asserted Lipschitz estimate, and
the exact way in which this normalization enters the already isolated rough
prime-transition ledger.

The cited Hildebrand--Tenenbaum--Saias estimate for `Psi - Lambda` is not
proved in the paper.  Accordingly, no theorem below declares that estimate
as an axiom.  Its precise endpoint-shaped consequence is exposed as a `Prop`
which can be passed to a reduction theorem.  In particular, the endpoint
error remains proportional to `A+B`, not to the short gap `B-A`.
-/

open scoped BigOperators Interval ENNReal

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## The finite `G_y` normal form -/













theorem roughSaiasDickmanDerivative_of_one_le
    {u : ℝ} (hu : 1 ≤ u) :
    roughSaiasDickmanDerivative u = -rho (u - 1) / u := by
  simp [roughSaiasDickmanDerivative, not_lt.mpr hu]



theorem measurable_roughSaiasDickmanDerivative :
    Measurable roughSaiasDickmanDerivative := by
  unfold roughSaiasDickmanDerivative
  apply Measurable.ite measurableSet_Iio measurable_const
  exact (continuous_rho.measurable.comp
    (measurable_id.sub_const 1)).neg.div measurable_id

theorem continuous_roughSaiasBaseRpow {y : ℕ} (hy : 0 < y) :
    Continuous (fun v : ℝ => (y : ℝ) ^ v) := by
  exact Real.continuous_const_rpow (by positivity)

theorem measurable_roughSaiasFractionalWeight {y : ℕ} (hy : 0 < y) :
    Measurable (roughSaiasFractionalWeight y) := by
  have hpow : Continuous (fun v : ℝ => (y : ℝ) ^ v) :=
    continuous_roughSaiasBaseRpow hy
  have hpowNeg : Continuous (fun v : ℝ => (y : ℝ) ^ (-v)) :=
    hpow.comp continuous_neg
  exact hpow.measurable.fract.mul hpowNeg.measurable

/-- The fractional Saias weight is uniformly between zero and one on the
integration interval. -/
theorem roughSaiasFractionalWeight_mem_unitInterval
    {y : ℕ} (hy : 1 ≤ y) {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ roughSaiasFractionalWeight y v ∧
      roughSaiasFractionalWeight y v ≤ 1 := by
  have hbase : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hpowNonneg : 0 ≤ (y : ℝ) ^ (-v) :=
    Real.rpow_nonneg (by positivity) _
  have hpowLe : (y : ℝ) ^ (-v) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
  have hfractNonneg : 0 ≤ Int.fract ((y : ℝ) ^ v) :=
    Int.fract_nonneg _
  have hfractLe : Int.fract ((y : ℝ) ^ v) ≤ 1 :=
    (Int.fract_lt_one _).le
  unfold roughSaiasFractionalWeight
  constructor
  · exact mul_nonneg hfractNonneg hpowNonneg
  · calc
      Int.fract ((y : ℝ) ^ v) * (y : ℝ) ^ (-v) ≤
          1 * (y : ℝ) ^ (-v) :=
        mul_le_mul_of_nonneg_right hfractLe hpowNonneg
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hpowLe (by norm_num)
      _ = 1 := mul_one _

/-- The right-limit Dickman derivative has absolute value at most one on
the whole compact interval that can occur in the convolution. -/
theorem roughSaiasDickmanDerivative_abs_le_one
    {u : ℝ} (hu5 : u ≤ 5) :
    |roughSaiasDickmanDerivative u| ≤ 1 := by
  by_cases hu1 : u < 1
  · simp [roughSaiasDickmanDerivative, hu1]
  · have hu1' : 1 ≤ u := le_of_not_gt hu1
    have hb := FriableAsymptotic.rho_delay_integrand_bounds hu1' hu5
    rw [roughSaiasDickmanDerivative_of_one_le hu1', neg_div, abs_neg,
      abs_of_nonneg hb.1]
    exact hb.2

/-- The unweighted translated derivative is interval-integrable on the
fixed compact interval. -/
theorem roughSaiasDickmanDerivative_translate_intervalIntegrable
    {u : ℝ} (hu5 : u ≤ 5) :
    IntervalIntegrable
      (fun v : ℝ => roughSaiasDickmanDerivative (u - v))
      volume 0 5 := by
  have hmeas : Measurable
      (fun v : ℝ => roughSaiasDickmanDerivative (u - v)) :=
    measurable_roughSaiasDickmanDerivative.comp
      (measurable_const.sub measurable_id)
  have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 5 :=
    continuous_const.intervalIntegrable 0 5
  apply hone.mono_fun' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with v hv
  have hv' : v ∈ Icc (0 : ℝ) 5 := by
    have hvIoc : v ∈ Ioc (0 : ℝ) 5 := by
      simpa [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 5)] using hv
    exact ⟨hvIoc.1.le, hvIoc.2⟩
  simpa only [Real.norm_eq_abs, norm_one] using
    roughSaiasDickmanDerivative_abs_le_one
      (u := u - v) (by linarith [hv'.1])

/-- The complete integrand in the finite Saias normal form is
interval-integrable. -/
theorem roughSaiasIntegrand_intervalIntegrable
    {y : ℕ} (hy2 : 2 ≤ y) {u : ℝ} (hu5 : u ≤ 5) :
    IntervalIntegrable
      (fun v : ℝ => roughSaiasDickmanDerivative (u - v) *
        roughSaiasFractionalWeight y v)
      volume 0 5 := by
  have hmeas : Measurable
      (fun v : ℝ => roughSaiasDickmanDerivative (u - v) *
        roughSaiasFractionalWeight y v) :=
    (measurable_roughSaiasDickmanDerivative.comp
      (measurable_const.sub measurable_id)).mul
        (measurable_roughSaiasFractionalWeight (by omega))
  have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 5 :=
    continuous_const.intervalIntegrable 0 5
  apply hone.mono_fun' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with v hv
  have hv' : v ∈ Icc (0 : ℝ) 5 := by
    have hvIoc : v ∈ Ioc (0 : ℝ) 5 := by
      simpa [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 5)] using hv
    exact ⟨hvIoc.1.le, hvIoc.2⟩
  have hderiv := roughSaiasDickmanDerivative_abs_le_one
    (u := u - v) (by linarith [hv'.1])
  have hweight := roughSaiasFractionalWeight_mem_unitInterval
    (y := y) (by omega) hv'.1
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hweight.1]
  calc
    |roughSaiasDickmanDerivative (u - v)| *
        roughSaiasFractionalWeight y v ≤
      1 * roughSaiasFractionalWeight y v :=
        mul_le_mul_of_nonneg_right hderiv hweight.1
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hweight.2 (by norm_num)
    _ = 1 := mul_one _











/-! ## The bounded-variation datum and compact Lipschitz reduction -/

/-- The finite Dickman function is antitone on the whole nonnegative compact
range.  The existing library theorem starts at `1`; the initial interval is
filled in here using the exact constant branch. -/
theorem roughRho_antitoneOn_zero_five :
    AntitoneOn rho (Icc (0 : ℝ) 5) := by
  intro a ha b hb hab
  by_cases hb1 : b ≤ 1
  · rw [rho_eq_one_of_le_one hb1,
      rho_eq_one_of_le_one (hab.trans hb1)]
  by_cases ha1 : 1 ≤ a
  · exact antitoneOn_rho_one_five
      ⟨ha1, ha.2⟩ ⟨(le_of_not_ge hb1), hb.2⟩ hab
  · rw [rho_eq_one_of_le_one (le_of_not_ge ha1)]
    exact FriableAsymptotic.rho_le_one_of_le_five hb.2

/-- On the left of its single jump, the right-limit derivative extension is
antitone. -/
theorem roughSaiasDickmanDerivative_antitoneOn_left :
    AntitoneOn roughSaiasDickmanDerivative (Icc (-5 : ℝ) 1) := by
  intro a ha b hb hab
  by_cases hb1 : b < 1
  · have ha1 : a < 1 := hab.trans_lt hb1
    simp [roughSaiasDickmanDerivative_of_lt_one ha1,
      roughSaiasDickmanDerivative_of_lt_one hb1]
  · have hbEq : b = 1 := le_antisymm hb.2 (le_of_not_gt hb1)
    subst b
    by_cases ha1 : a < 1
    · rw [roughSaiasDickmanDerivative_of_lt_one ha1,
        roughSaiasDickmanDerivative_one]
      norm_num
    · have haEq : a = 1 :=
        le_antisymm hab (le_of_not_gt ha1)
      subst a
      exact le_rfl

/-- To the right of the jump, the Dickman derivative increases from `-1`
towards zero. -/
theorem roughSaiasDickmanDerivative_monotoneOn_right :
    MonotoneOn roughSaiasDickmanDerivative (Icc (1 : ℝ) 5) := by
  intro a ha b hb hab
  have hrho : rho (b - 1) ≤ rho (a - 1) := by
    apply roughRho_antitoneOn_zero_five
    · constructor <;> linarith [ha.1, ha.2]
    · constructor <;> linarith [hb.1, hb.2]
    · linarith
  have hrhoA : 0 ≤ rho (a - 1) :=
    (rho_pos_on_zero_five (by linarith [ha.1])
      (by linarith [ha.2])).le
  have hfirst : rho (b - 1) / b ≤ rho (a - 1) / b :=
    div_le_div_of_nonneg_right hrho (by linarith [hb.1])
  have hsecond : rho (a - 1) / b ≤ rho (a - 1) / a :=
    div_le_div_of_nonneg_left hrhoA (by linarith [ha.1]) hab
  have hratio : rho (b - 1) / b ≤ rho (a - 1) / a :=
    hfirst.trans hsecond
  rw [roughSaiasDickmanDerivative_of_one_le ha.1,
    roughSaiasDickmanDerivative_of_one_le hb.1]
  calc
    -rho (a - 1) / a = -(rho (a - 1) / a) := by ring
    _ ≤ -(rho (b - 1) / b) := neg_le_neg hratio
    _ = -rho (b - 1) / b := by ring

/-- Negation does not change total variation of a real-valued function. -/
theorem eVariationOn_neg_real (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => -f x) s = eVariationOn f s := by
  simp only [eVariationOn, edist_neg_neg]

/-- The exact compact variation datum used by the proof in the paper.  The
single jump contributes one and the monotone right branch contributes at
most one, so the total variation is at most two. -/
theorem roughSaiasDickmanDerivative_eVariationOn_le_two :
    eVariationOn roughSaiasDickmanDerivative (Icc (-5 : ℝ) 5) ≤
      ENNReal.ofReal 2 := by
  have hleftMono : MonotoneOn
      (fun u : ℝ => -roughSaiasDickmanDerivative u)
      (Icc (-5 : ℝ) 1) := by
    intro a ha b hb hab
    exact neg_le_neg
      (roughSaiasDickmanDerivative_antitoneOn_left ha hb hab)
  have hleftNeg :
      eVariationOn (fun u : ℝ => -roughSaiasDickmanDerivative u)
          (Icc (-5 : ℝ) 1) ≤ ENNReal.ofReal 1 := by
    have hraw := hleftMono.eVariationOn_le
      (a := (-5 : ℝ)) (b := (1 : ℝ))
      (by norm_num) (by norm_num)
    norm_num [roughSaiasDickmanDerivative] at hraw
    simpa only [roughSaiasDickmanDerivative, ENNReal.ofReal_one] using hraw
  have hleft :
      eVariationOn roughSaiasDickmanDerivative (Icc (-5 : ℝ) 1) ≤
        ENNReal.ofReal 1 := by
    rw [← eVariationOn_neg_real roughSaiasDickmanDerivative
      (Icc (-5 : ℝ) 1)]
    exact hleftNeg
  have hrightRaw :=
    roughSaiasDickmanDerivative_monotoneOn_right.eVariationOn_le
      (a := (1 : ℝ)) (b := (5 : ℝ))
      (by norm_num) (by norm_num)
  have hrightRaw' :
      eVariationOn roughSaiasDickmanDerivative (Icc (1 : ℝ) 5) ≤
        ENNReal.ofReal
          (roughSaiasDickmanDerivative 5 -
            roughSaiasDickmanDerivative 1) := by
    simpa using hrightRaw
  have hq5 : roughSaiasDickmanDerivative 5 ≤ 0 := by
    rw [roughSaiasDickmanDerivative_of_one_le (by norm_num)]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr
        (rho_pos_on_zero_five (by norm_num) (by norm_num)).le)
      (by norm_num)
  have hright :
      eVariationOn roughSaiasDickmanDerivative (Icc (1 : ℝ) 5) ≤
        ENNReal.ofReal 1 := by
    apply hrightRaw'.trans
    apply ENNReal.ofReal_le_ofReal
    rw [roughSaiasDickmanDerivative_one]
    linarith
  have hadd :
      eVariationOn roughSaiasDickmanDerivative (Icc (-5 : ℝ) 1) +
        eVariationOn roughSaiasDickmanDerivative (Icc (1 : ℝ) 5) =
      eVariationOn roughSaiasDickmanDerivative (Icc (-5 : ℝ) 5) := by
    simpa only [univ_inter] using
      (eVariationOn.Icc_add_Icc
        (f := roughSaiasDickmanDerivative) (s := (Set.univ : Set ℝ))
        (a := (-5 : ℝ)) (b := (1 : ℝ)) (c := (5 : ℝ))
        (by norm_num) (by norm_num) (by simp))
  calc
    eVariationOn roughSaiasDickmanDerivative (Icc (-5 : ℝ) 5) =
        eVariationOn roughSaiasDickmanDerivative (Icc (-5 : ℝ) 1) +
          eVariationOn roughSaiasDickmanDerivative (Icc (1 : ℝ) 5) :=
      hadd.symm
    _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal 1 := add_le_add hleft hright
    _ = ENNReal.ofReal 2 := by norm_num





/-- Application of the standard compact BV translation principle to the
actual Dickman derivative, using the proved variation constant `2`. -/
theorem roughSaiasDickmanDerivative_translation_le_two
    (hBV : RoughCompactBVTranslationPrinciple)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 5)
    (hb : b ∈ Icc (0 : ℝ) 5) :
    (∫ v in (0 : ℝ)..5,
      |roughSaiasDickmanDerivative (a - v) -
        roughSaiasDickmanDerivative (b - v)|) ≤
      2 * |a - b| := by
  exact hBV roughSaiasDickmanDerivative
    roughSaiasDickmanDerivative_eVariationOn_le_two ha hb

/-- The finite `G_y` normal form is explicitly `3`-Lipschitz on `0 <= u <= 5`
once the standard compact BV translation principle is supplied. -/
theorem roughSaiasG_lipschitz_three
    (hBV : RoughCompactBVTranslationPrinciple)
    {y : ℕ} (hy2 : 2 ≤ y)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 5)
    (hb : b ∈ Icc (0 : ℝ) 5) :
    |roughSaiasG y a - roughSaiasG y b| ≤ 3 * |a - b| := by
  let Fa : ℝ → ℝ := fun v =>
    roughSaiasDickmanDerivative (a - v) *
      roughSaiasFractionalWeight y v
  let Fb : ℝ → ℝ := fun v =>
    roughSaiasDickmanDerivative (b - v) *
      roughSaiasFractionalWeight y v
  let qa : ℝ → ℝ := fun v => roughSaiasDickmanDerivative (a - v)
  let qb : ℝ → ℝ := fun v => roughSaiasDickmanDerivative (b - v)
  have hFa : IntervalIntegrable Fa volume 0 5 := by
    simpa only [Fa] using
      roughSaiasIntegrand_intervalIntegrable hy2 ha.2
  have hFb : IntervalIntegrable Fb volume 0 5 := by
    simpa only [Fb] using
      roughSaiasIntegrand_intervalIntegrable hy2 hb.2
  have hqa : IntervalIntegrable qa volume 0 5 := by
    simpa only [qa] using
      roughSaiasDickmanDerivative_translate_intervalIntegrable ha.2
  have hqb : IntervalIntegrable qb volume 0 5 := by
    simpa only [qb] using
      roughSaiasDickmanDerivative_translate_intervalIntegrable hb.2
  have hdiff :
      (∫ v in (0 : ℝ)..5, Fa v) - ∫ v in (0 : ℝ)..5, Fb v =
        ∫ v in (0 : ℝ)..5, Fa v - Fb v := by
    exact (intervalIntegral.integral_sub hFa hFb).symm
  have hintegral :
      |(∫ v in (0 : ℝ)..5, Fa v) - ∫ v in (0 : ℝ)..5, Fb v| ≤
        ∫ v in (0 : ℝ)..5, |qa v - qb v| := by
    rw [hdiff]
    calc
      |(∫ v in (0 : ℝ)..5, Fa v - Fb v)| ≤
          ∫ v in (0 : ℝ)..5, |Fa v - Fb v| :=
        intervalIntegral.abs_integral_le_integral_abs (by norm_num)
      _ ≤ ∫ v in (0 : ℝ)..5, |qa v - qb v| := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (hFa.sub hFb).abs (hqa.sub hqb).abs
        intro v hv
        have hweight := roughSaiasFractionalWeight_mem_unitInterval
          (y := y) (by omega) hv.1
        change
          |qa v * roughSaiasFractionalWeight y v -
              qb v * roughSaiasFractionalWeight y v| ≤
            |qa v - qb v|
        rw [← sub_mul, abs_mul, abs_of_nonneg hweight.1]
        exact mul_le_of_le_one_right (abs_nonneg (qa v - qb v)) hweight.2
  have htranslate :
      (∫ v in (0 : ℝ)..5, |qa v - qb v|) ≤ 2 * |a - b| := by
    simpa only [qa, qb] using
      roughSaiasDickmanDerivative_translation_le_two hBV ha hb
  have hrho : |rho a - rho b| ≤ |a - b| :=
    roughRho_abs_sub_le_abs_of_le_five ha.2 hb.2
  change
    |(rho a - ∫ v in (0 : ℝ)..5, Fa v) -
      (rho b - ∫ v in (0 : ℝ)..5, Fb v)| ≤ 3 * |a - b|
  calc
    |(rho a - ∫ v in (0 : ℝ)..5, Fa v) -
        (rho b - ∫ v in (0 : ℝ)..5, Fb v)| =
      |(rho a - rho b) -
        ((∫ v in (0 : ℝ)..5, Fa v) -
          ∫ v in (0 : ℝ)..5, Fb v)| := by
        congr 1
        ring
    _ ≤ |rho a - rho b| +
        |(∫ v in (0 : ℝ)..5, Fa v) -
          ∫ v in (0 : ℝ)..5, Fb v| := abs_sub _ _
    _ ≤ |a - b| + ∫ v in (0 : ℝ)..5, |qa v - qb v| :=
      add_le_add hrho hintegral
    _ ≤ |a - b| + 2 * |a - b| := add_le_add_right htranslate _
    _ = 3 * |a - b| := by ring



/-! ## The explicit `1 / log y` normalization correction -/

theorem roughSaiasFractionalWeight_le_rpow_neg
    {y : ℕ} (hy : 0 < y) {v : ℝ} :
    roughSaiasFractionalWeight y v ≤ (y : ℝ) ^ (-v) := by
  have hpow : 0 ≤ (y : ℝ) ^ (-v) :=
    Real.rpow_nonneg (by positivity) _
  have hfractLe : Int.fract ((y : ℝ) ^ v) ≤ 1 :=
    (Int.fract_lt_one _).le
  unfold roughSaiasFractionalWeight
  exact mul_le_of_le_one_left hpow hfractLe

/-- Exact elementary integral of the exponential envelope for the
fractional Saias weight. -/
theorem roughSaias_integral_rpow_neg
    {y : ℕ} (hy : 1 < y) :
    (∫ v in (0 : ℝ)..5, (y : ℝ) ^ (-v)) =
      (1 - (y : ℝ) ^ (-(5 : ℝ))) / Real.log (y : ℝ) := by
  have hypos : (0 : ℝ) < (y : ℝ) := by positivity
  have hlogpos : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast hy)
  have hc : -Real.log (y : ℝ) ≠ 0 := by linarith
  have hpointwise : ∀ v : ℝ,
      (y : ℝ) ^ (-v) =
        Real.exp ((-Real.log (y : ℝ)) * v) := by
    intro v
    rw [Real.rpow_def_of_pos hypos]
    congr 1
    ring
  have hexpFive :
      Real.exp ((-Real.log (y : ℝ)) * 5) =
        (y : ℝ) ^ (-(5 : ℝ)) := by
    rw [Real.rpow_def_of_pos hypos]
    congr 1
    ring
  calc
    (∫ v in (0 : ℝ)..5, (y : ℝ) ^ (-v)) =
        ∫ v in (0 : ℝ)..5,
          Real.exp ((-Real.log (y : ℝ)) * v) := by
      apply intervalIntegral.integral_congr
      intro v _hv
      exact hpointwise v
    _ = (-Real.log (y : ℝ))⁻¹ *
        (Real.exp ((-Real.log (y : ℝ)) * 5) - 1) := by
      rw [intervalIntegral.integral_comp_mul_left
        (f := Real.exp) (a := (0 : ℝ)) (b := (5 : ℝ)) hc]
      simp only [integral_exp, smul_eq_mul, mul_zero, Real.exp_zero]
    _ = (1 - (y : ℝ) ^ (-(5 : ℝ))) /
        Real.log (y : ℝ) := by
      rw [hexpFive]
      field_simp [hlogpos.ne']
      ring

theorem roughSaias_integral_rpow_neg_le_inv_log
    {y : ℕ} (hy : 1 < y) :
    (∫ v in (0 : ℝ)..5, (y : ℝ) ^ (-v)) ≤
      1 / Real.log (y : ℝ) := by
  have hlogpos : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast hy)
  rw [roughSaias_integral_rpow_neg hy]
  apply div_le_div_of_nonneg_right _ hlogpos.le
  have hpow : 0 ≤ (y : ℝ) ^ (-(5 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  linarith

/-- On the five-face compact range, the entire difference between `G_y`
and `rho` is at most `1 / log y`. -/
theorem roughSaiasG_sub_rho_abs_le_inv_log
    {y : ℕ} (hy2 : 2 ≤ y) {u : ℝ} (hu5 : u ≤ 5) :
    |roughSaiasG y u - rho u| ≤ 1 / Real.log (y : ℝ) := by
  let f : ℝ → ℝ := fun v =>
    roughSaiasDickmanDerivative (u - v) *
      roughSaiasFractionalWeight y v
  let e : ℝ → ℝ := fun v => (y : ℝ) ^ (-v)
  have hf : IntervalIntegrable f volume 0 5 := by
    simpa only [f] using
      roughSaiasIntegrand_intervalIntegrable hy2 hu5
  have he : IntervalIntegrable e volume 0 5 := by
    have hpow : Continuous (fun v : ℝ => (y : ℝ) ^ v) :=
      continuous_roughSaiasBaseRpow (by omega)
    exact (hpow.comp continuous_neg).intervalIntegrable 0 5
  have hmono :
      (∫ v in (0 : ℝ)..5, |f v|) ≤ ∫ v in (0 : ℝ)..5, e v := by
    apply intervalIntegral.integral_mono_on (by norm_num) hf.abs he
    intro v hv
    have hq := roughSaiasDickmanDerivative_abs_le_one
      (u := u - v) (by linarith [hv.1])
    have hw := roughSaiasFractionalWeight_mem_unitInterval
      (y := y) (by omega) hv.1
    change
      |roughSaiasDickmanDerivative (u - v) *
          roughSaiasFractionalWeight y v| ≤ e v
    rw [abs_mul, abs_of_nonneg hw.1]
    calc
      |roughSaiasDickmanDerivative (u - v)| *
          roughSaiasFractionalWeight y v ≤
        1 * roughSaiasFractionalWeight y v :=
          mul_le_mul_of_nonneg_right hq hw.1
      _ = roughSaiasFractionalWeight y v := one_mul _
      _ ≤ e v := roughSaiasFractionalWeight_le_rpow_neg
        (y := y) (by omega)
  have habs : |(∫ v in (0 : ℝ)..5, f v)| ≤
      ∫ v in (0 : ℝ)..5, e v := by
    exact (intervalIntegral.abs_integral_le_integral_abs
      (f := f) (by norm_num)).trans hmono
  have henv := roughSaias_integral_rpow_neg_le_inv_log
    (y := y) (by omega)
  have hrewrite : roughSaiasG y u - rho u =
      -(∫ v in (0 : ℝ)..5, f v) := by
    unfold roughSaiasG
    change
      (rho u - ∫ v in (0 : ℝ)..5, f v) - rho u =
        -(∫ v in (0 : ℝ)..5, f v)
    ring
  rw [hrewrite, abs_neg]
  exact habs.trans henv

/-- Since `G_y` is `3`-Lipschitz and `rho` is `1`-Lipschitz, their
difference is explicitly `4`-Lipschitz. -/
theorem roughSaiasG_sub_rho_lipschitz_four
    (hBV : RoughCompactBVTranslationPrinciple)
    {y : ℕ} (hy2 : 2 ≤ y)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 5)
    (hb : b ∈ Icc (0 : ℝ) 5) :
    |(roughSaiasG y a - rho a) - (roughSaiasG y b - rho b)| ≤
      4 * |a - b| := by
  have hG := roughSaiasG_lipschitz_three hBV hy2 ha hb
  have hrho : |rho a - rho b| ≤ |a - b| :=
    roughRho_abs_sub_le_abs_of_le_five ha.2 hb.2
  calc
    |(roughSaiasG y a - rho a) - (roughSaiasG y b - rho b)| =
        |(roughSaiasG y a - roughSaiasG y b) - (rho a - rho b)| := by
      congr 1
      ring
    _ ≤ |roughSaiasG y a - roughSaiasG y b| + |rho a - rho b| :=
      abs_sub _ _
    _ ≤ 3 * |a - b| + |a - b| := add_le_add hG hrho
    _ = 4 * |a - b| := by ring

/-! ## Exact connection to the genuine friable residual -/













/-- The normal-form correction has the desired short-gap scale, with the
explicit constant five.  Thus any remaining loss in the residual increment
comes only from the genuine endpoint errors `Psi - Lambda_normalForm`. -/
theorem roughSaiasDickmanCorrection_difference_abs_le
    (hBV : RoughCompactBVTranslationPrinciple)
    {A B y : ℕ} (hA : 0 < A) (hAB : A ≤ B) (hy2 : 2 ≤ y)
    (hB5 : FriableAsymptotic.dickmanU B y ≤ 5) :
    |roughSaiasDickmanCorrection B y -
        roughSaiasDickmanCorrection A y| ≤
      5 * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) := by
  let a : ℝ := FriableAsymptotic.dickmanU A y
  let b : ℝ := FriableAsymptotic.dickmanU B y
  let H : ℝ → ℝ := fun u => roughSaiasG y u - rho u
  have hB : 0 < B := hA.trans_le hAB
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogAB : Real.log (A : ℝ) ≤ Real.log (B : ℝ) :=
    Real.log_le_log (by exact_mod_cast hA) (by exact_mod_cast hAB)
  have hab : a ≤ b := by
    dsimp [a, b, FriableAsymptotic.dickmanU]
    exact div_le_div_of_nonneg_right hlogAB hlogy.le
  have ha0 : 0 ≤ a := by
    dsimp [a, FriableAsymptotic.dickmanU]
    exact div_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ A by omega))) hlogy.le
  have hb0 : 0 ≤ b := ha0.trans hab
  have hb5 : b ≤ 5 := by simpa only [b] using hB5
  have ha5 : a ≤ 5 := hab.trans hb5
  have hHbound : |H b| ≤ 1 / Real.log (y : ℝ) := by
    simpa only [H] using
      roughSaiasG_sub_rho_abs_le_inv_log hy2 hb5
  have hHlip : |H b - H a| ≤ 4 * (b - a) := by
    have h := roughSaiasG_sub_rho_lipschitz_four hBV hy2
      (show b ∈ Icc (0 : ℝ) 5 from ⟨hb0, hb5⟩)
      (show a ∈ Icc (0 : ℝ) 5 from ⟨ha0, ha5⟩)
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at h
    simpa only [H] using h
  have hlogQuotient :
      Real.log (B : ℝ) - Real.log (A : ℝ) ≤
        (B : ℝ) / (A : ℝ) - 1 := by
    have hBcast : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
    have hAcast : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
    have h := Real.log_le_sub_one_of_pos
      (div_pos hBcast hAcast)
    rw [Real.log_div hBcast.ne' hAcast.ne'] at h
    exact h
  have hscaled :
      (A : ℝ) * (Real.log (B : ℝ) - Real.log (A : ℝ)) ≤
        (B : ℝ) - (A : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlogQuotient
      (by positivity : (0 : ℝ) ≤ (A : ℝ))
    calc
      (A : ℝ) * (Real.log (B : ℝ) - Real.log (A : ℝ)) ≤
          (A : ℝ) * ((B : ℝ) / (A : ℝ) - 1) := h
      _ = (B : ℝ) - (A : ℝ) := by field_simp
  have hcoordinate :
      (A : ℝ) * (b - a) ≤
        ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) := by
    have hdiv := div_le_div_of_nonneg_right hscaled hlogy.le
    rw [Nat.cast_sub hAB]
    dsimp [a, b, FriableAsymptotic.dickmanU]
    convert hdiv using 1
    ring
  have hsecond :
      (A : ℝ) * (4 * (b - a)) ≤
        4 * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) := by
    calc
      (A : ℝ) * (4 * (b - a)) = 4 * ((A : ℝ) * (b - a)) := by
        ring
      _ ≤ 4 * (((B - A : ℕ) : ℝ) / Real.log (y : ℝ)) :=
        mul_le_mul_of_nonneg_left hcoordinate (by norm_num)
      _ = 4 * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) := by
        ring
  have hgapNonneg : 0 ≤ ((B - A : ℕ) : ℝ) := by positivity
  have hAcastNonneg : 0 ≤ (A : ℝ) := by positivity
  unfold roughSaiasDickmanCorrection
  change |(B : ℝ) * H b - (A : ℝ) * H a| ≤
    5 * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ)
  have hexpand :
      (B : ℝ) * H b - (A : ℝ) * H a =
        ((B - A : ℕ) : ℝ) * H b + (A : ℝ) * (H b - H a) := by
    rw [Nat.cast_sub hAB]
    ring
  rw [hexpand]
  calc
    |((B - A : ℕ) : ℝ) * H b + (A : ℝ) * (H b - H a)| ≤
        |((B - A : ℕ) : ℝ) * H b| +
          |(A : ℝ) * (H b - H a)| := abs_add_le _ _
    _ = ((B - A : ℕ) : ℝ) * |H b| +
        (A : ℝ) * |H b - H a| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hgapNonneg,
        abs_of_nonneg hAcastNonneg]
    _ ≤ ((B - A : ℕ) : ℝ) *
          (1 / Real.log (y : ℝ)) +
        (A : ℝ) * (4 * (b - a)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hHbound hgapNonneg)
        (mul_le_mul_of_nonneg_left hHlip hAcastNonneg)
    _ ≤ ((B - A : ℕ) : ℝ) *
          (1 / Real.log (y : ℝ)) +
        4 * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) :=
      add_le_add_right hsecond _
    _ = 5 * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) := by
      ring









end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_026 := by
  exact @Erdos390.WholePaper.roughSaiasDickmanCorrection_difference_abs_le
