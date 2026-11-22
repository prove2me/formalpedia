-- Prove2me | solution 1 for Erdos390.WholePaper.roughSaiasBaseFreeFractionalIntegral_quotient_succ_sub_eq_common_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:46:40.972143+00:00
-- url     : https://prove2.me/submissions/8231660e-5590-4429-993f-949f39784949

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





/-- The transformed kernel is supported below the natural quotient scale
`q/m`.  Above that scale the Dickman-derivative argument is strictly below
one.  The statement is pointwise, so no regularity of `fract` is needed. -/
theorem roughSaiasBaseFreeFractionalKernel_eq_zero_of_div_lt
    {q m : ℕ} (hq1 : 1 ≤ q) (hm2 : 2 ≤ m) {t : ℝ}
    (ht : (q : ℝ) / (m : ℝ) < t) :
    roughSaiasBaseFreeFractionalKernel q m t = 0 := by
  have hqpos : 0 < (q : ℝ) := by
    exact_mod_cast (show 0 < q by omega)
  have hmpos : 0 < (m : ℝ) := by
    positivity
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
  have harg :
      Real.log (q : ℝ) / Real.log (m : ℝ) -
          Real.log t / Real.log (m : ℝ) < 1 := by
    rw [← sub_div, div_lt_one (Real.log_pos hmone)]
    linarith
  unfold roughSaiasBaseFreeFractionalKernel
  rw [roughSaiasDickmanDerivative_of_lt_one harg]
  simp

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

/-- The five-face condition places the next-base support cutoff strictly
below the old artificial endpoint `m^5`. -/
theorem roughSaiasNatQuotient_div_succ_lt_rpow_five
    {q m : ℕ} (hq1 : 1 ≤ q) (hm2 : 2 ≤ m)
    (hu5 : Real.log (q : ℝ) / Real.log (m : ℝ) ≤ 5) :
    (q : ℝ) / ((m + 1 : ℕ) : ℝ) < (m : ℝ) ^ (5 : ℝ) := by
  have hqpos : 0 < (q : ℝ) := by
    exact_mod_cast (show 0 < q by omega)
  have hmpos : 0 < (m : ℝ) := by
    positivity
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos hmone
  have hlogq :
      Real.log (q : ℝ) ≤ 5 * Real.log (m : ℝ) :=
    (div_le_iff₀ hlogm).mp hu5
  have hpowpos : 0 < (m : ℝ) ^ (5 : ℝ) :=
    Real.rpow_pos_of_pos hmpos 5
  have hqpow : (q : ℝ) ≤ (m : ℝ) ^ (5 : ℝ) := by
    apply (Real.log_le_log_iff hqpos hpowpos).mp
    rw [Real.log_rpow hmpos]
    exact hlogq
  have hdivle :
      (q : ℝ) / ((m + 1 : ℕ) : ℝ) ≤
        (m : ℝ) ^ (5 : ℝ) / ((m + 1 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right hqpow (by positivity)
  have hdivlt :
      (m : ℝ) ^ (5 : ℝ) / ((m + 1 : ℕ) : ℝ) <
        (m : ℝ) ^ (5 : ℝ) :=
    div_lt_self hpowpos
      (by exact_mod_cast (show 1 < m + 1 by omega))
  exact hdivle.trans_lt hdivlt

/-- On five faces the upper-endpoint tail created by changing from `m^5`
to `(m+1)^5` is identically zero, because it lies beyond the transformed
support. -/
theorem roughSaiasBaseFreeFractionalKernel_succ_tail_eq_zero
    {q m : ℕ} (hq1 : 1 ≤ q) (hm2 : 2 ≤ m)
    (hu5 : Real.log (q : ℝ) / Real.log (m : ℝ) ≤ 5) :
    (∫ t in (m : ℝ) ^ (5 : ℝ)..
        ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ),
      roughSaiasBaseFreeFractionalKernel q (m + 1) t) = 0 := by
  have hcut := roughSaiasNatQuotient_div_succ_lt_rpow_five
    hq1 hm2 hu5
  have hupper :
      (m : ℝ) ^ (5 : ℝ) ≤
        ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ) :=
    Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast (show m ≤ m + 1 by omega)) (by norm_num)
  calc
    (∫ t in (m : ℝ) ^ (5 : ℝ)..
        ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ),
      roughSaiasBaseFreeFractionalKernel q (m + 1) t) =
        ∫ _t in (m : ℝ) ^ (5 : ℝ)..
          ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htI :
          t ∈ Icc ((m : ℝ) ^ (5 : ℝ))
            (((m + 1 : ℕ) : ℝ) ^ (5 : ℝ)) := by
        rw [uIcc_of_le hupper] at ht
        exact ht
      exact roughSaiasBaseFreeFractionalKernel_eq_zero_of_div_lt
        hq1 (by omega) (hcut.trans_le htI.1)
    _ = 0 := by simp

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



















/-- A simultaneous quotient drop and base increment has one exact
common-range correction integral.  The artificial endpoint tail still
vanishes: it is enough that the larger old quotient lies on the five
constructed faces. -/
theorem roughSaiasBaseFreeFractionalIntegral_quotient_succ_sub_eq_common
    {q₁ q₀ m : ℕ} (hq₁ : 1 ≤ q₁) (hq : q₁ ≤ q₀) (hm2 : 2 ≤ m)
    (hu₀5 : Real.log (q₀ : ℝ) / Real.log (m : ℝ) ≤ 5) :
    roughSaiasBaseFreeFractionalIntegral q₁ (m + 1) -
        roughSaiasBaseFreeFractionalIntegral q₀ m =
      ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
        (Int.fract t / t ^ (2 : ℕ)) *
          (roughSaiasScaledDickmanKernel q₁ (m + 1) t -
            roughSaiasScaledDickmanKernel q₀ m t) := by
  have hq₁pos : 0 < (q₁ : ℝ) := by
    exact_mod_cast (show 0 < q₁ by omega)
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogq : Real.log (q₁ : ℝ) ≤ Real.log (q₀ : ℝ) :=
    Real.log_le_log hq₁pos (by exact_mod_cast hq)
  have hu₁5 : Real.log (q₁ : ℝ) / Real.log (m : ℝ) ≤ 5 :=
    (div_le_div_of_nonneg_right hlogq hlogm.le).trans hu₀5
  have husucc5 :
      Real.log (q₁ : ℝ) / Real.log ((m + 1 : ℕ) : ℝ) ≤ 5 :=
    (roughSaiasNatQuotientLogRatio_succ_le hq₁ hm2).trans hu₁5
  have hnow :=
    roughSaiasBaseFreeFractionalKernel_intervalIntegrable hm2 hu₀5
  have hnext :=
    roughSaiasBaseFreeFractionalKernel_intervalIntegrable
      (m := m + 1) (q := q₁) (by omega) husucc5
  have huNow : (1 : ℝ) ≤ (m : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ m by omega)) (by norm_num)
  have huNext :
      (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow
      (by exact_mod_cast (show 1 ≤ m + 1 by omega)) (by norm_num)
  have hupper :
      (m : ℝ) ^ (5 : ℝ) ≤
        ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ) :=
    Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast (show m ≤ m + 1 by omega)) (by norm_num)
  have hnextCommon : IntervalIntegrable
      (roughSaiasBaseFreeFractionalKernel q₁ (m + 1)) volume
      (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
    apply hnext.mono_set
    rw [uIcc_of_le huNow, uIcc_of_le huNext]
    exact Icc_subset_Icc le_rfl hupper
  have hnextTail : IntervalIntegrable
      (roughSaiasBaseFreeFractionalKernel q₁ (m + 1)) volume
      ((m : ℝ) ^ (5 : ℝ))
      (((m + 1 : ℕ) : ℝ) ^ (5 : ℝ)) := by
    apply hnext.mono_set
    rw [uIcc_of_le hupper, uIcc_of_le huNext]
    exact Icc_subset_Icc huNow le_rfl
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hnextCommon hnextTail
  have hdiff := intervalIntegral.integral_sub hnextCommon hnow
  have htail := roughSaiasBaseFreeFractionalKernel_succ_tail_eq_zero
    hq₁ hm2 hu₁5
  unfold roughSaiasBaseFreeFractionalIntegral
  calc
    (∫ t in (1 : ℝ)..((m + 1 : ℕ) : ℝ) ^ (5 : ℝ),
        roughSaiasBaseFreeFractionalKernel q₁ (m + 1) t) -
        ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q₀ m t =
      ((∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q₁ (m + 1) t) +
        ∫ t in (m : ℝ) ^ (5 : ℝ)..
            ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q₁ (m + 1) t) -
        ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q₀ m t := by
      rw [hsplit]
    _ = (∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q₁ (m + 1) t) -
        ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q₀ m t := by
      rw [htail, add_zero]
    _ = ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
        (roughSaiasBaseFreeFractionalKernel q₁ (m + 1) t -
          roughSaiasBaseFreeFractionalKernel q₀ m t) := by
      rw [hdiff]
    _ = ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
        (Int.fract t / t ^ (2 : ℕ)) *
          (roughSaiasScaledDickmanKernel q₁ (m + 1) t -
            roughSaiasScaledDickmanKernel q₀ m t) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      change
        roughSaiasBaseFreeFractionalKernel q₁ (m + 1) t -
            roughSaiasBaseFreeFractionalKernel q₀ m t =
          (Int.fract t / t ^ (2 : ℕ)) *
            (roughSaiasScaledDickmanKernel q₁ (m + 1) t -
              roughSaiasScaledDickmanKernel q₀ m t)
      rw [roughSaiasBaseFreeFractionalKernel_eq_sawtooth_mul_scaled
          q₁ (m + 1) t,
        roughSaiasBaseFreeFractionalKernel_eq_sawtooth_mul_scaled q₀ m t]
      ring





























/-! ## The genuinely real hyperbola path inside natural cells -/



























































end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_025 := by
  exact @Erdos390.WholePaper.roughSaiasBaseFreeFractionalIntegral_quotient_succ_sub_eq_common
