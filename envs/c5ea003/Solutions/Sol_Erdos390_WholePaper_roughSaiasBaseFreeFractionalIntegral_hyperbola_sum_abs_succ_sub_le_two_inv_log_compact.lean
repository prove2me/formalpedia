-- Prove2me | solution 1 for Erdos390.WholePaper.roughSaiasBaseFreeFractionalIntegral_hyperbola_sum_abs_succ_sub_le_two_inv_log_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:49:33.007079+00:00
-- url     : https://prove2.me/submissions/a8883346-ba80-41a7-83ad-ca8204d4bc4e

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
import Definitions.Def_erdos390_analytic_foundations_008
import Theorems.Thm_Erdos390_WholePaper_roughSaiasBaseFreeFractionalIntegral_quotient_succ_sub_eq_common_compact
import Theorems.Thm_Erdos390_WholePaper_roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_le_two_inv_log_of_cutoff_compact



section
theorem Erdos390.WholePaper.roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_le_two_inv_log_of_cutoff : Erdos390.RemainingAnalyticGoal008_032 := @Erdos390.WholePaper.roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_le_two_inv_log_of_cutoff_compact
end
section
theorem Erdos390.WholePaper.roughSaiasBaseFreeFractionalIntegral_quotient_succ_sub_eq_common : Erdos390.RemainingAnalyticGoal008_025 := @Erdos390.WholePaper.roughSaiasBaseFreeFractionalIntegral_quotient_succ_sub_eq_common_compact
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





















/-! ## The explicit `1 / log y` normalization correction -/











/-! ## Exact connection to the genuine friable residual -/























end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasBaseChange -/
section


/-!
# Base-free sawtooth coordinates for the Saias correction

The difficult base variation in `roughSaiasG m` contains
`fract(m^v) * m^(-v)`.  This file records the exact substitution `t=m^v`
before any absolute value is taken.  After multiplication by the Jacobian,
the sawtooth is `fract(t)`, independent of `m`; all base dependence is left
in the logarithmic Dickman kernel and the factor `1 / log m`.

This is an exact identity for the finite `[0,5]` integral.  The one-variable
Jacobian theorem is used because its monotone form permits the discontinuous
fractional-part integrand.
-/

open scoped Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section







/-- The transformed coordinate is a single log difference divided by the
base logarithm. -/
theorem roughSaiasBaseFreeDickmanCoordinate_eq_sub_div
    (q m : ℕ) (t : ℝ) :
    roughSaiasBaseFreeDickmanCoordinate q m t =
      (Real.log (q : ℝ) - Real.log t) / Real.log (m : ℝ) := by
  unfold roughSaiasBaseFreeDickmanCoordinate
  ring

/-- On the positive segment `t ≤ q`, increasing the base decreases the
transformed Dickman coordinate.  This is the monotone piece relevant on the
effective support `t ≤ q/m`. -/
theorem roughSaiasBaseFreeDickmanCoordinate_succ_le
    {q m : ℕ} (hm2 : 2 ≤ m) {t : ℝ}
    (htpos : 0 < t) (htq : t ≤ (q : ℝ)) :
    roughSaiasBaseFreeDickmanCoordinate q (m + 1) t ≤
      roughSaiasBaseFreeDickmanCoordinate q m t := by
  have hmpos : 0 < (m : ℝ) := by
    positivity
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have hlogNumerator : 0 ≤ Real.log (q : ℝ) - Real.log t :=
    sub_nonneg.mpr (Real.log_le_log htpos htq)
  have hlogBase :
      Real.log (m : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) :=
    Real.log_le_log hmpos
      (by exact_mod_cast (show m ≤ m + 1 by omega))
  rw [roughSaiasBaseFreeDickmanCoordinate_eq_sub_div,
    roughSaiasBaseFreeDickmanCoordinate_eq_sub_div]
  exact div_le_div_of_nonneg_left hlogNumerator
    (Real.log_pos hmone) hlogBase





/-- The sawtooth factor is common to all bases.  Every base-dependent term
is confined to `roughSaiasScaledDickmanKernel`. -/
theorem roughSaiasBaseFreeFractionalKernel_eq_sawtooth_mul_scaled
    (q m : ℕ) (t : ℝ) :
    roughSaiasBaseFreeFractionalKernel q m t =
      (Int.fract t / t ^ (2 : ℕ)) *
        roughSaiasScaledDickmanKernel q m t := by
  unfold roughSaiasBaseFreeFractionalKernel
    roughSaiasScaledDickmanKernel
    roughSaiasBaseFreeDickmanCoordinate
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring







/-- For a positive natural quotient, its logarithmic coordinate decreases
when the base is incremented. -/
theorem roughSaiasNatQuotientLogRatio_succ_le
    {q m : ℕ} (hq1 : 1 ≤ q) (hm2 : 2 ≤ m) :
    Real.log (q : ℝ) / Real.log ((m + 1 : ℕ) : ℝ) ≤
      Real.log (q : ℝ) / Real.log (m : ℝ) := by
  have h := roughSaiasBaseFreeDickmanCoordinate_succ_le
    (q := q) hm2 (t := (1 : ℝ)) (by norm_num)
      (by exact_mod_cast hq1)
  simpa [roughSaiasBaseFreeDickmanCoordinate] using h





/-- Pointwise Jacobian cancellation for `t=m^v`.  This is the algebraic
heart of the base-free representation and retains the signed sawtooth. -/
theorem roughSaiasBaseFreeFractionalKernel_rpow_mul_jacobian
    {q m : ℕ} (hm2 : 2 ≤ m) (v : ℝ) :
    (Real.log (m : ℝ) * (m : ℝ) ^ v) *
        roughSaiasBaseFreeFractionalKernel q m ((m : ℝ) ^ v) =
      roughSaiasDickmanDerivative
          (Real.log (q : ℝ) / Real.log (m : ℝ) - v) *
        roughSaiasFractionalWeight m v := by
  have hmpos : 0 < (m : ℝ) := by
    positivity
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have hlogm : Real.log (m : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos hmone)
  have hrpow : (m : ℝ) ^ v ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hmpos v)
  have hcancel :
      v * Real.log (m : ℝ) / Real.log (m : ℝ) = v := by
    field_simp [hlogm]
  unfold roughSaiasBaseFreeFractionalKernel
    roughSaiasFractionalWeight
  rw [Real.log_rpow hmpos, hcancel, Real.rpow_neg hmpos.le]
  field_simp [hlogm, hrpow]





/-- Integrability of the transformed kernel on its finite interval, obtained
from the already proved integrability of the original Saias integrand and
the same monotone Jacobian. -/
theorem roughSaiasBaseFreeFractionalKernel_intervalIntegrable
    {q m : ℕ} (hm2 : 2 ≤ m)
    (hu5 : Real.log (q : ℝ) / Real.log (m : ℝ) ≤ 5) :
    IntervalIntegrable (roughSaiasBaseFreeFractionalKernel q m)
      volume (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
  let f : ℝ → ℝ := fun v => (m : ℝ) ^ v
  let f' : ℝ → ℝ := fun v =>
    Real.log (m : ℝ) * (m : ℝ) ^ v
  have hmpos : 0 < (m : ℝ) := by
    positivity
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have hfderiv : ∀ v ∈ Icc (0 : ℝ) 5,
      HasDerivWithinAt f (f' v) (Icc (0 : ℝ) 5) v := by
    intro v _hv
    simpa [f, f'] using
      ((hasDerivAt_id v).const_rpow hmpos).hasDerivWithinAt
  have hfmono : MonotoneOn f (Icc (0 : ℝ) 5) :=
    (Real.strictMono_rpow_of_base_gt_one hmone).monotone.monotoneOn _
  have hfcont : ContinuousOn f (Icc (0 : ℝ) 5) :=
    (Real.continuous_const_rpow hmpos.ne').continuousOn
  have hfimage :
      f '' Icc (0 : ℝ) 5 =
        Icc (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
    calc
      f '' Icc (0 : ℝ) 5 = Icc (f 0) (f 5) :=
        hfcont.image_Icc_of_monotoneOn (by norm_num) hfmono
      _ = Icc (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
        simp [f]
  have horiginal : IntervalIntegrable
      (fun v : ℝ =>
        roughSaiasDickmanDerivative
            (Real.log (q : ℝ) / Real.log (m : ℝ) - v) *
          roughSaiasFractionalWeight m v)
      volume 0 5 :=
    roughSaiasIntegrand_intervalIntegrable hm2 hu5
  have horiginalIcc : IntegrableOn
      (fun v : ℝ =>
        roughSaiasDickmanDerivative
            (Real.log (q : ℝ) / Real.log (m : ℝ) - v) *
          roughSaiasFractionalWeight m v)
      (Icc (0 : ℝ) 5) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp
      horiginal
  have hjacobianIcc : IntegrableOn
      (fun v : ℝ =>
        f' v • roughSaiasBaseFreeFractionalKernel q m (f v))
      (Icc (0 : ℝ) 5) := by
    apply horiginalIcc.congr_fun _ measurableSet_Icc
    intro v _hv
    simpa [f, f', smul_eq_mul] using
      (roughSaiasBaseFreeFractionalKernel_rpow_mul_jacobian
        (q := q) hm2 v).symm
  have hkernelImage : IntegrableOn
      (roughSaiasBaseFreeFractionalKernel q m)
      (f '' Icc (0 : ℝ) 5) :=
    (MeasureTheory.integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
      measurableSet_Icc hfderiv hfmono
        (roughSaiasBaseFreeFractionalKernel q m)).mpr hjacobianIcc
  rw [hfimage] at hkernelImage
  have hu : (1 : ℝ) ≤ (m : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ m by omega)) (by norm_num)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hu).mpr hkernelImage













/-! ## Exact floor/base pairing in the transformed coordinate -/











/-! ## The signed center as a base-free quotient-block sum -/







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasSharpVariation -/
section


/-!
# Sharp active-face variation of the base-free Saias kernel

On the active Dickman faces the apparently competing changes in the
Dickman coordinate and in `1 / log m` cancel algebraically.  If

`u_m(t) = (log q - log t) / log m`,

then

`rho'(u_m(t)) / log m = -rho (u_m(t) - 1) / (log q - log t)`.

The denominator on the right is independent of `m`.  Consequently, while
`t <= q / m` and the coordinates remain on the five constructed faces, the
scaled kernel is antitone as the base increases.  Its absolute consecutive
variation on an all-active finite block therefore telescopes exactly.  No
triangle inequality between the coordinate and coefficient changes is used.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-- Elementary evaluation of the inverse-square majorant on a positive
interval.  This is proved directly from the fundamental theorem so the
sharp-variation argument does not depend on a particular exported name for
the integer-power integral formula. -/
private theorem roughSaias_integral_one_div_sq_eq
    {A : ℝ} (hA : 1 ≤ A) :
    (∫ t in (1 : ℝ)..A, 1 / t ^ (2 : ℕ)) = 1 - 1 / A := by
  have hzeroNotMem : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) A :=
    Set.notMem_uIcc_of_lt (by norm_num) (zero_lt_one.trans_le hA)
  have hint : IntervalIntegrable (fun t : ℝ => 1 / t ^ (2 : ℕ))
      volume (1 : ℝ) A := by
    simpa [one_div, zpow_neg] using
      (intervalIntegral.intervalIntegrable_zpow
        (a := (1 : ℝ)) (b := A) (n := (-2 : ℤ))
        (Or.inr hzeroNotMem))
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => -(x⁻¹))
    (f' := fun x : ℝ => 1 / x ^ (2 : ℕ))
    (a := (1 : ℝ)) (b := A) (fun x hx => by
      rw [Set.uIcc_of_le hA] at hx
      have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans_le hx.1)
      convert (hasDerivAt_inv hx0).neg using 1
      all_goals simp [one_div]) hint
  simp only [one_div]
  calc
    (∫ t in (1 : ℝ)..A, (t ^ (2 : ℕ))⁻¹) = -A⁻¹ + 1 := by
      simpa [one_div] using hfund
    _ = 1 - A⁻¹ := by ring











/-- The scaled kernel itself vanishes beyond its natural support `q / m`.
This is the smooth-factor analogue of
`roughSaiasBaseFreeFractionalKernel_eq_zero_of_div_lt`; it does not use the
sawtooth factor. -/
theorem roughSaiasScaledDickmanKernel_eq_zero_of_div_lt
    {q m : ℕ} (hq1 : 1 ≤ q) (hm2 : 2 ≤ m) {t : ℝ}
    (ht : (q : ℝ) / (m : ℝ) < t) :
    roughSaiasScaledDickmanKernel q m t = 0 := by
  have hqpos : 0 < (q : ℝ) := by
    exact_mod_cast (show 0 < q by omega)
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (show 0 < m by omega)
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have htpos : 0 < t :=
    (div_pos hqpos hmpos).trans ht
  have hq_lt_tm : (q : ℝ) < t * (m : ℝ) :=
    (div_lt_iff₀ hmpos).mp ht
  have hloglt :
      Real.log (q : ℝ) < Real.log t + Real.log (m : ℝ) := by
    have h := Real.strictMonoOn_log hqpos (mul_pos htpos hmpos) hq_lt_tm
    rwa [Real.log_mul htpos.ne' hmpos.ne'] at h
  have harg : roughSaiasBaseFreeDickmanCoordinate q m t < 1 := by
    rw [roughSaiasBaseFreeDickmanCoordinate_eq_sub_div,
      div_lt_one (Real.log_pos hmone)]
    linarith
  unfold roughSaiasScaledDickmanKernel
  rw [roughSaiasDickmanDerivative_of_lt_one harg]
  simp







/-- The preceding exact common-range identity specialized to the natural
hyperbola path. -/
theorem roughSaiasBaseFreeFractionalIntegral_hyperbola_succ_sub_eq_common
    {X m : ℕ} (hm2 : 2 ≤ m) (hnextX : m + 1 ≤ X)
    (hum5 : Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) ≤ 5) :
    roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1) -
        roughSaiasBaseFreeFractionalIntegral (X / m) m =
      ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
        (Int.fract t / t ^ (2 : ℕ)) *
          (roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
            roughSaiasScaledDickmanKernel (X / m) m t) := by
  have hmPos : 0 < m := by omega
  have hnextPos : 0 < m + 1 := by omega
  have hqNext : 1 ≤ X / (m + 1) :=
    Nat.div_pos hnextX hnextPos
  have hqLe : X / (m + 1) ≤ X / m :=
    Nat.div_le_div_left (a := X) (Nat.le_succ m) hmPos
  exact roughSaiasBaseFreeFractionalIntegral_quotient_succ_sub_eq_common
    hqNext hqLe hm2 hum5

/-- Integrability of the common sawtooth transition on one hyperbola edge. -/
theorem roughSaiasHyperbolaFractionalTransition_intervalIntegrable
    {X m : ℕ} (hm2 : 2 ≤ m) (hnextX : m + 1 ≤ X)
    (hum5 : Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) ≤ 5) :
    IntervalIntegrable
      (fun t : ℝ => (Int.fract t / t ^ (2 : ℕ)) *
        (roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
          roughSaiasScaledDickmanKernel (X / m) m t))
      volume (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
  have hmPos : 0 < m := by omega
  have hnextPos : 0 < m + 1 := by omega
  have hqNext : 1 ≤ X / (m + 1) :=
    Nat.div_pos hnextX hnextPos
  have hqLe : X / (m + 1) ≤ X / m :=
    Nat.div_le_div_left (a := X) (Nat.le_succ m) hmPos
  have hqNextPosR : 0 < ((X / (m + 1) : ℕ) : ℝ) := by positivity
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogq : Real.log ((X / (m + 1) : ℕ) : ℝ) ≤
      Real.log ((X / m : ℕ) : ℝ) :=
    Real.log_le_log hqNextPosR (by exact_mod_cast hqLe)
  have huNextNow5 : Real.log ((X / (m + 1) : ℕ) : ℝ) /
      Real.log (m : ℝ) ≤ 5 :=
    (div_le_div_of_nonneg_right hlogq hlogm.le).trans hum5
  have huNext5 : Real.log ((X / (m + 1) : ℕ) : ℝ) /
      Real.log ((m + 1 : ℕ) : ℝ) ≤ 5 :=
    (roughSaiasNatQuotientLogRatio_succ_le hqNext hm2).trans huNextNow5
  have hnow := roughSaiasBaseFreeFractionalKernel_intervalIntegrable
    (q := X / m) hm2 hum5
  have hnext := roughSaiasBaseFreeFractionalKernel_intervalIntegrable
    (q := X / (m + 1)) (m := m + 1) (by omega) huNext5
  have huNow : (1 : ℝ) ≤ (m : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ m by omega)) (by norm_num)
  have huNext : (1 : ℝ) ≤
      ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow
      (by exact_mod_cast (show 1 ≤ m + 1 by omega)) (by norm_num)
  have hupper : (m : ℝ) ^ (5 : ℝ) ≤
      ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ) :=
    Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast (show m ≤ m + 1 by omega)) (by norm_num)
  have hnextCommon : IntervalIntegrable
      (roughSaiasBaseFreeFractionalKernel (X / (m + 1)) (m + 1))
      volume (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
    apply hnext.mono_set
    rw [uIcc_of_le huNow, uIcc_of_le huNext]
    exact Icc_subset_Icc le_rfl hupper
  apply (hnextCommon.sub hnow).congr
  intro t _ht
  change
    roughSaiasBaseFreeFractionalKernel (X / (m + 1)) (m + 1) t -
        roughSaiasBaseFreeFractionalKernel (X / m) m t =
      (Int.fract t / t ^ (2 : ℕ)) *
        (roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
          roughSaiasScaledDickmanKernel (X / m) m t)
  rw [roughSaiasBaseFreeFractionalKernel_eq_sawtooth_mul_scaled
      (X / (m + 1)) (m + 1) t,
    roughSaiasBaseFreeFractionalKernel_eq_sawtooth_mul_scaled
      (X / m) m t]
  ring







/-- The natural support scale `(X / m) / m` is antitone in `m`. -/
theorem roughSaiasNaturalHyperbolaSupport_antitone
    {X m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    ((X / n : ℕ) : ℝ) / (n : ℝ) ≤
      ((X / m : ℕ) : ℝ) / (m : ℝ) := by
  have hn : 0 < n := hm.trans_le hmn
  have hq : X / n ≤ X / m :=
    Nat.div_le_div_left (a := X) hmn hm
  calc
    ((X / n : ℕ) : ℝ) / (n : ℝ) ≤
        ((X / m : ℕ) : ℝ) / (n : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hq)
        (by exact_mod_cast hn.le)
    _ ≤ ((X / m : ℕ) : ℝ) / (m : ℝ) :=
      div_le_div_of_nonneg_left (by positivity)
        (by exact_mod_cast hm) (by exact_mod_cast hmn)

/-- The global five-face hypothesis at the first base propagates to every
natural hyperbola quotient and every sawtooth variable `t ≥ 1`. -/
theorem roughSaiasBaseFreeDickmanCoordinate_natHyperbola_le_five
    {X a m : ℕ} (ha2 : 2 ≤ a) (ham : a ≤ m) (hmX : m ≤ X)
    {t : ℝ} (ht1 : 1 ≤ t)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    roughSaiasBaseFreeDickmanCoordinate (X / m) m t ≤ 5 := by
  have hm2 : 2 ≤ m := ha2.trans ham
  have hmposNat : 0 < m := by omega
  have hqpos : 0 < X / m := Nat.div_pos hmX hmposNat
  have hqX : X / m ≤ X := Nat.div_le_self X m
  have hapos : 0 < (a : ℝ) := by positivity
  have hqposR : 0 < ((X / m : ℕ) : ℝ) := by exact_mod_cast hqpos
  have hXposR : 0 < (X : ℝ) := by exact_mod_cast (hmposNat.trans_le hmX)
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogX0 : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hlogqX : Real.log ((X / m : ℕ) : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log hqposR (by exact_mod_cast hqX)
  have hlogam : Real.log (a : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log hapos (by exact_mod_cast ham)
  rw [roughSaiasBaseFreeDickmanCoordinate_eq_sub_div]
  calc
    (Real.log ((X / m : ℕ) : ℝ) - Real.log t) /
          Real.log (m : ℝ) ≤
        Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hlogm.le
    _ ≤ Real.log (X : ℝ) / Real.log (m : ℝ) :=
      div_le_div_of_nonneg_right hlogqX hlogm.le
    _ ≤ Real.log (X : ℝ) / Real.log (a : ℝ) :=
      div_le_div_of_nonneg_left hlogX0 hloga hlogam
    _ ≤ 5 := hu5

/-- The five-face hypothesis at `a` gives its equivalent real power cap. -/
theorem roughSaiasNat_le_rpow_five
    {X a : ℕ} (hX : 0 < X) (ha2 : 2 ≤ a)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    (X : ℝ) ≤ (a : ℝ) ^ (5 : ℝ) := by
  have hXR : 0 < (X : ℝ) := by exact_mod_cast hX
  have haR : 0 < (a : ℝ) := by positivity
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hpow : 0 < (a : ℝ) ^ (5 : ℝ) :=
    Real.rpow_pos_of_pos haR 5
  apply (Real.log_le_log_iff hXR hpow).mp
  rw [Real.log_rpow haR]
  exact (div_le_iff₀ hloga).mp hu5

/-- Log-ratio form of five-face propagation along natural hyperbola
quotients. -/
theorem roughSaiasNatHyperbolaLogRatio_le_five
    {X a m : ℕ} (ha2 : 2 ≤ a) (ham : a ≤ m) (hmX : m ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) ≤ 5 := by
  simpa [roughSaiasBaseFreeDickmanCoordinate] using
    (roughSaiasBaseFreeDickmanCoordinate_natHyperbola_le_five
      ha2 ham hmX (t := (1 : ℝ)) (by norm_num) hu5)

/-- Every hyperbola transition may be placed on the single smallest cap
`a^5`.  The part between `a^5` and the edge's native cap `m^5` is beyond
both natural supports and hence vanishes identically. -/
theorem roughSaiasBaseFreeFractionalIntegral_hyperbola_succ_sub_eq_firstCap
    {X a b m : ℕ} (ha2 : 2 ≤ a) (_hab : a ≤ b) (hbX : b ≤ X)
    (hm : m ∈ Finset.Ico a b)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1) -
        roughSaiasBaseFreeFractionalIntegral (X / m) m =
      ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
        (Int.fract t / t ^ (2 : ℕ)) *
          (roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
            roughSaiasScaledDickmanKernel (X / m) m t) := by
  have hmData := Finset.mem_Ico.mp hm
  have hm2 : 2 ≤ m := ha2.trans hmData.1
  have hnextX : m + 1 ≤ X := by omega
  have hum5 : Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) ≤ 5 :=
    roughSaiasNatHyperbolaLogRatio_le_five
      ha2 hmData.1 (by omega) hu5
  have hedge :=
    roughSaiasBaseFreeFractionalIntegral_hyperbola_succ_sub_eq_common
      hm2 hnextX hum5
  let f : ℝ → ℝ := fun t => (Int.fract t / t ^ (2 : ℕ)) *
    (roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
      roughSaiasScaledDickmanKernel (X / m) m t)
  have hf : IntervalIntegrable f volume (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
    simpa only [f] using roughSaiasHyperbolaFractionalTransition_intervalIntegrable
      hm2 hnextX hum5
  have haCapOne : (1 : ℝ) ≤ (a : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ a by omega)) (by norm_num)
  have haCapM : (a : ℝ) ^ (5 : ℝ) ≤ (m : ℝ) ^ (5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hmData.1) (by norm_num)
  have htailInt : IntervalIntegrable f volume
      ((a : ℝ) ^ (5 : ℝ)) ((m : ℝ) ^ (5 : ℝ)) := by
    apply hf.mono_set
    rw [uIcc_of_le haCapM, uIcc_of_le
      (haCapOne.trans haCapM)]
    exact Icc_subset_Icc haCapOne le_rfl
  have hXpos : 0 < X := by omega
  have hXcap : (X : ℝ) ≤ (a : ℝ) ^ (5 : ℝ) :=
    roughSaiasNat_le_rpow_five hXpos ha2 hu5
  have hXrealPos : 0 < (X : ℝ) := by exact_mod_cast hXpos
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have hqNowLeX : ((X / m : ℕ) : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast Nat.div_le_self X m
  have hsupportNow : ((X / m : ℕ) : ℝ) / (m : ℝ) <
      (a : ℝ) ^ (5 : ℝ) := by
    calc
      ((X / m : ℕ) : ℝ) / (m : ℝ) ≤
          (X : ℝ) / (m : ℝ) :=
        div_le_div_of_nonneg_right hqNowLeX (by positivity)
      _ < (X : ℝ) := div_lt_self hXrealPos hmone
      _ ≤ (a : ℝ) ^ (5 : ℝ) := hXcap
  have hsupportNext :
      ((X / (m + 1) : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) <
        (a : ℝ) ^ (5 : ℝ) :=
    (roughSaiasNaturalHyperbolaSupport_antitone
      (by omega) (Nat.le_succ m)).trans_lt hsupportNow
  have hqNow : 1 ≤ X / m := Nat.div_pos (by omega) (by omega)
  have hqNext : 1 ≤ X / (m + 1) := Nat.div_pos hnextX (by omega)
  have htailZero :
      (∫ t in (a : ℝ) ^ (5 : ℝ)..(m : ℝ) ^ (5 : ℝ), f t) = 0 := by
    calc
      (∫ t in (a : ℝ) ^ (5 : ℝ)..(m : ℝ) ^ (5 : ℝ), f t) =
          ∫ _t in (a : ℝ) ^ (5 : ℝ)..(m : ℝ) ^ (5 : ℝ),
            (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have htI : t ∈ Set.Icc ((a : ℝ) ^ (5 : ℝ))
            ((m : ℝ) ^ (5 : ℝ)) := by
          simpa only [Set.uIcc_of_le haCapM] using ht
        have hnowZero : roughSaiasScaledDickmanKernel (X / m) m t = 0 :=
          roughSaiasScaledDickmanKernel_eq_zero_of_div_lt
            hqNow hm2 (hsupportNow.trans_le htI.1)
        have hnextZero :
            roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t = 0 :=
          roughSaiasScaledDickmanKernel_eq_zero_of_div_lt
            hqNext (by omega) (hsupportNext.trans_le htI.1)
        simp [f, hnowZero, hnextZero]
      _ = 0 := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hf.mono_set (by
      rw [uIcc_of_le haCapOne, uIcc_of_le (haCapOne.trans haCapM)]
      exact Icc_subset_Icc le_rfl haCapM)) htailInt
  rw [hedge]
  change (∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ), f t) =
    ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ), f t
  rw [← hsplit, htailZero, add_zero]

/-- Unconditional pointwise hyperbola-path variation on the full compact
range.  The active indices automatically form an initial segment because
the support scale is antitone; no cutoff index is required as input. -/
theorem roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_le_two_inv_log
    {X a b : ℕ} (ha2 : 2 ≤ a) (_hab : a ≤ b) (hbX : b ≤ X)
    {t : ℝ} (ht1 : 1 ≤ t)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
          roughSaiasScaledDickmanKernel (X / m) m t|) ≤
      2 / Real.log (a : ℝ) := by
  classical
  let active : Finset ℕ := (Finset.Icc a b).filter
    (fun m => t ≤ ((X / m : ℕ) : ℝ) / (m : ℝ))
  have htpos : 0 < t := zero_lt_one.trans_le ht1
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  by_cases hactiveNonempty : active.Nonempty
  · let c : ℕ := active.max' hactiveNonempty
    have hcActive : c ∈ active := Finset.max'_mem active hactiveNonempty
    have hcData : c ∈ Finset.Icc a b ∧
        t ≤ ((X / c : ℕ) : ℝ) / (c : ℝ) := by
      simpa only [active, Finset.mem_filter] using hcActive
    have hac : a ≤ c := (Finset.mem_Icc.mp hcData.1).1
    have hcb : c ≤ b := (Finset.mem_Icc.mp hcData.1).2
    have hactive : ∀ m ∈ Finset.Icc a c,
        t ≤ ((X / m : ℕ) : ℝ) / (m : ℝ) := by
      intro m hm
      have hmData := Finset.mem_Icc.mp hm
      exact hcData.2.trans
        (roughSaiasNaturalHyperbolaSupport_antitone
          (by omega) hmData.2)
    have hface : ∀ m ∈ Finset.Icc a c,
        roughSaiasBaseFreeDickmanCoordinate (X / m) m t ≤ 5 := by
      intro m hm
      have hmData := Finset.mem_Icc.mp hm
      exact roughSaiasBaseFreeDickmanCoordinate_natHyperbola_le_five
        ha2 hmData.1 (hmData.2.trans (hcb.trans hbX)) ht1 hu5
    have hinactive : ∀ m ∈ Finset.Ioc c b,
        ((X / m : ℕ) : ℝ) / (m : ℝ) < t := by
      intro m hm
      rw [Finset.mem_Ioc] at hm
      apply lt_of_not_ge
      intro hmActive
      have hmMem : m ∈ active := by
        simp only [active, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hac.trans hm.1.le, hm.2⟩, hmActive⟩
      have hmc : m ≤ c := Finset.le_max' active m hmMem
      omega
    exact
      roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_le_two_inv_log_of_cutoff
        ha2 hac hcb hbX htpos hactive hface hinactive
  · have hzero : ∀ m ∈ Finset.Ico a b,
        |roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
          roughSaiasScaledDickmanKernel (X / m) m t| = 0 := by
      intro m hm
      have hmData := Finset.mem_Ico.mp hm
      have hmNow : m ∈ Finset.Icc a b := by
        rw [Finset.mem_Icc]
        omega
      have hmNext : m + 1 ∈ Finset.Icc a b := by
        rw [Finset.mem_Icc]
        omega
      have hmNotActive :
          ¬t ≤ ((X / m : ℕ) : ℝ) / (m : ℝ) := by
        intro hmActive
        apply hactiveNonempty
        exact ⟨m, by
          simp only [active, Finset.mem_filter]
          exact ⟨hmNow, hmActive⟩⟩
      have hmNextNotActive :
          ¬t ≤ ((X / (m + 1) : ℕ) : ℝ) /
            ((m + 1 : ℕ) : ℝ) := by
        intro hmActive
        apply hactiveNonempty
        exact ⟨m + 1, by
          simp only [active, Finset.mem_filter]
          exact ⟨hmNext, hmActive⟩⟩
      have hqm : 1 ≤ X / m := Nat.div_pos (by omega) (by omega)
      have hqmNext : 1 ≤ X / (m + 1) :=
        Nat.div_pos (by omega) (by omega)
      rw [roughSaiasScaledDickmanKernel_eq_zero_of_div_lt
          hqm (by omega) (lt_of_not_ge hmNotActive),
        roughSaiasScaledDickmanKernel_eq_zero_of_div_lt
          hqmNext (by omega) (lt_of_not_ge hmNextNotActive),
        sub_self, abs_zero]
    rw [Finset.sum_eq_zero hzero]
    positivity





/-- Total variation of the transformed fractional correction along a
natural hyperbola block.  All edge integrals are first moved to the same
smallest cap `a^5`; finite summation then passes under the integral, where
the pointwise `2 / log a` kernel-variation estimate applies. -/
theorem roughSaiasBaseFreeFractionalIntegral_hyperbola_sum_abs_succ_sub_le_two_inv_log
    {X a b : ℕ} (ha2 : 2 ≤ a) (hab : a ≤ b) (hbX : b ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1) -
          roughSaiasBaseFreeFractionalIntegral (X / m) m|) ≤
      2 / Real.log (a : ℝ) := by
  let f : ℕ → ℝ → ℝ := fun m t =>
    (Int.fract t / t ^ (2 : ℕ)) *
      (roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
        roughSaiasScaledDickmanKernel (X / m) m t)
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hfactorNonneg : 0 ≤ 2 / Real.log (a : ℝ) := by positivity
  have haCapOne : (1 : ℝ) ≤ (a : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ a by omega)) (by norm_num)
  have hf : ∀ m ∈ Finset.Ico a b,
      IntervalIntegrable (f m) volume
        (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
    intro m hm
    have hmData := Finset.mem_Ico.mp hm
    have hm2 : 2 ≤ m := ha2.trans hmData.1
    have hnextX : m + 1 ≤ X := by omega
    have hum5 : Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) ≤ 5 :=
      roughSaiasNatHyperbolaLogRatio_le_five
        ha2 hmData.1 (by omega) hu5
    have hfull : IntervalIntegrable (f m) volume
        (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
      simpa only [f] using
        (roughSaiasHyperbolaFractionalTransition_intervalIntegrable
          hm2 hnextX hum5)
    have haCapM : (a : ℝ) ^ (5 : ℝ) ≤ (m : ℝ) ^ (5 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hmData.1) (by norm_num)
    apply hfull.mono_set
    rw [uIcc_of_le haCapOne, uIcc_of_le (haCapOne.trans haCapM)]
    exact Icc_subset_Icc le_rfl haCapM
  have hedge : ∀ m ∈ Finset.Ico a b,
      roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1) -
          roughSaiasBaseFreeFractionalIntegral (X / m) m =
        ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ), f m t := by
    intro m hm
    simpa only [f] using
      (roughSaiasBaseFreeFractionalIntegral_hyperbola_succ_sub_eq_firstCap
        ha2 hab hbX hm hu5)
  have hedgeBound : ∀ m ∈ Finset.Ico a b,
      |roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1) -
          roughSaiasBaseFreeFractionalIntegral (X / m) m| ≤
        ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ), |f m t| := by
    intro m hm
    rw [hedge m hm]
    exact intervalIntegral.abs_integral_le_integral_abs haCapOne
  have hsumInt : IntervalIntegrable
      (fun t : ℝ => ∑ m ∈ Finset.Ico a b, |f m t|) volume
      (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
    apply (IntervalIntegrable.sum (Finset.Ico a b)
      (fun m hm => (hf m hm).abs)).congr
    intro t _ht
    simp only [Finset.sum_apply]
  have hzeroNotMem : (0 : ℝ) ∉
      Set.uIcc (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) :=
    Set.notMem_uIcc_of_lt (by norm_num) (by positivity)
  have hinvSqInt : IntervalIntegrable (fun t : ℝ => 1 / t ^ (2 : ℕ))
      volume (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
    simpa [one_div, zpow_neg] using
      (intervalIntegral.intervalIntegrable_zpow
        (a := (1 : ℝ)) (b := (a : ℝ) ^ (5 : ℝ))
        (n := (-2 : ℤ)) (Or.inr hzeroNotMem))
  have hmajorInt : IntervalIntegrable
      (fun t : ℝ => (2 / Real.log (a : ℝ)) * (1 / t ^ (2 : ℕ)))
      volume (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) :=
    hinvSqInt.const_mul _
  have hpoint : ∀ t ∈ Set.uIcc (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)),
      (∑ m ∈ Finset.Ico a b, |f m t|) ≤
        (2 / Real.log (a : ℝ)) * (1 / t ^ (2 : ℕ)) := by
    intro t ht
    rw [Set.uIcc_of_le haCapOne] at ht
    have htpos : 0 < t := zero_lt_one.trans_le ht.1
    have htSqPos : 0 < t ^ (2 : ℕ) := pow_pos htpos 2
    have hwNonneg : 0 ≤ Int.fract t / t ^ (2 : ℕ) :=
      div_nonneg (Int.fract_nonneg t) htSqPos.le
    have hwLe : Int.fract t / t ^ (2 : ℕ) ≤ 1 / t ^ (2 : ℕ) :=
      div_le_div_of_nonneg_right (Int.fract_lt_one t).le htSqPos.le
    have hvariation :=
      roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_le_two_inv_log
        ha2 hab hbX ht.1 hu5
    calc
      (∑ m ∈ Finset.Ico a b, |f m t|) =
          (Int.fract t / t ^ (2 : ℕ)) *
            ∑ m ∈ Finset.Ico a b,
              |roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
                roughSaiasScaledDickmanKernel (X / m) m t| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _hm
        simp only [f, abs_mul, abs_of_nonneg hwNonneg]
      _ ≤ (Int.fract t / t ^ (2 : ℕ)) *
          (2 / Real.log (a : ℝ)) :=
        mul_le_mul_of_nonneg_left hvariation hwNonneg
      _ ≤ (1 / t ^ (2 : ℕ)) * (2 / Real.log (a : ℝ)) :=
        mul_le_mul_of_nonneg_right hwLe hfactorNonneg
      _ = (2 / Real.log (a : ℝ)) * (1 / t ^ (2 : ℕ)) := by ring
  have hsumIntegral :
      (∑ m ∈ Finset.Ico a b,
          ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ), |f m t|) =
        ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
          ∑ m ∈ Finset.Ico a b, |f m t| := by
    symm
    exact intervalIntegral.integral_finset_sum
      (fun m hm => (hf m hm).abs)
  have hmono :
      (∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
          ∑ m ∈ Finset.Ico a b, |f m t|) ≤
        ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
          (2 / Real.log (a : ℝ)) * (1 / t ^ (2 : ℕ)) := by
    exact intervalIntegral.integral_mono_on
      haCapOne hsumInt hmajorInt (fun t ht => hpoint t (by
        simpa only [Set.uIcc_of_le haCapOne] using ht))
  have hinvSqIntegral :
      (∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
        1 / t ^ (2 : ℕ)) =
      1 - 1 / ((a : ℝ) ^ (5 : ℝ)) := by
    exact roughSaias_integral_one_div_sq_eq haCapOne
  have hmajorBound :
      (∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
          (2 / Real.log (a : ℝ)) * (1 / t ^ (2 : ℕ))) ≤
        2 / Real.log (a : ℝ) := by
    rw [intervalIntegral.integral_const_mul, hinvSqIntegral]
    have hcapInvNonneg : 0 ≤ 1 / ((a : ℝ) ^ (5 : ℝ)) := by positivity
    calc
      (2 / Real.log (a : ℝ)) *
          (1 - 1 / ((a : ℝ) ^ (5 : ℝ))) ≤
        (2 / Real.log (a : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) hfactorNonneg
      _ = 2 / Real.log (a : ℝ) := by ring
  calc
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1) -
          roughSaiasBaseFreeFractionalIntegral (X / m) m|) ≤
      ∑ m ∈ Finset.Ico a b,
        ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ), |f m t| :=
      Finset.sum_le_sum hedgeBound
    _ = ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
        ∑ m ∈ Finset.Ico a b, |f m t| := hsumIntegral
    _ ≤ ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
        (2 / Real.log (a : ℝ)) * (1 / t ^ (2 : ℕ)) := hmono
    _ ≤ 2 / Real.log (a : ℝ) := hmajorBound

/-! ## The genuinely real hyperbola path inside natural cells -/



























































end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_024 := by
  exact @Erdos390.WholePaper.roughSaiasBaseFreeFractionalIntegral_hyperbola_sum_abs_succ_sub_le_two_inv_log
