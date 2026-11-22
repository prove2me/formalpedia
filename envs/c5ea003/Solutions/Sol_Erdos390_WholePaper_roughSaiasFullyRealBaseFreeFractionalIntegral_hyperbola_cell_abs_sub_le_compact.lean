-- Prove2me | solution 1 for Erdos390.WholePaper.roughSaiasFullyRealBaseFreeFractionalIntegral_hyperbola_cell_abs_sub_le_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:48:52.118639+00:00
-- url     : https://prove2.me/submissions/00caecea-a3b9-4fff-9c2b-67b99e142159

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
import Definitions.Def_erdos390_analytic_foundations_009

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



















/-! ## The explicit `1 / log y` normalization correction -/











/-! ## Exact connection to the genuine friable residual -/























end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasFullyRealNormalForm -/
section


/-!
# The Saias normal form with a genuinely real base

Continuous Buchstab produces inner terms `Lambda(x/s,s)` with a real base
`s`.  The project's original `roughSaiasG` takes a natural base, so it
cannot state that identity directly.  This file supplies the literal real
analogue, proves the same signed base-free substitution, and identifies it
exactly with the finite Stieltjes functional.  At natural bases it reduces
definitionally to the existing normal form.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## Fully real Saias data -/











theorem measurable_roughSaiasFullyRealFractionalWeight
    {y : ℝ} (hy : 0 < y) :
    Measurable (roughSaiasFullyRealFractionalWeight y) := by
  have hpow : Continuous (fun v : ℝ ↦ y ^ v) :=
    Real.continuous_const_rpow hy.ne'
  have hpowNeg : Continuous (fun v : ℝ ↦ y ^ (-v)) :=
    hpow.comp continuous_neg
  exact hpow.measurable.fract.mul hpowNeg.measurable

theorem roughSaiasFullyRealFractionalWeight_mem_unitInterval
    {y v : ℝ} (hy : 1 ≤ y) (hv : 0 ≤ v) :
    0 ≤ roughSaiasFullyRealFractionalWeight y v ∧
      roughSaiasFullyRealFractionalWeight y v ≤ 1 := by
  have hpowNonneg : 0 ≤ y ^ (-v) := Real.rpow_nonneg (by positivity) _
  have hpowLe : y ^ (-v) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith)
  have hfractNonneg : 0 ≤ Int.fract (y ^ v) := Int.fract_nonneg _
  have hfractLe : Int.fract (y ^ v) ≤ 1 := (Int.fract_lt_one _).le
  unfold roughSaiasFullyRealFractionalWeight
  constructor
  · exact mul_nonneg hfractNonneg hpowNonneg
  · calc
      Int.fract (y ^ v) * y ^ (-v) ≤ 1 * y ^ (-v) :=
        mul_le_mul_of_nonneg_right hfractLe hpowNonneg
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hpowLe (by norm_num)
      _ = 1 := mul_one _

theorem roughSaiasFullyRealIntegrand_intervalIntegrable
    {y u : ℝ} (hy : 1 < y) (hu5 : u ≤ 5) :
    IntervalIntegrable
      (fun v : ℝ ↦ roughSaiasDickmanDerivative (u - v) *
        roughSaiasFullyRealFractionalWeight y v)
      volume 0 5 := by
  have hmeas : Measurable
      (fun v : ℝ ↦ roughSaiasDickmanDerivative (u - v) *
        roughSaiasFullyRealFractionalWeight y v) :=
    (measurable_roughSaiasDickmanDerivative.comp
      (measurable_const.sub measurable_id)).mul
        (measurable_roughSaiasFullyRealFractionalWeight
          (zero_lt_one.trans hy))
  have hone : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume 0 5 :=
    continuous_const.intervalIntegrable 0 5
  apply hone.mono_fun' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with v hv
  have hv' : v ∈ Set.Icc (0 : ℝ) 5 := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] using
      Set.uIoc_subset_uIcc hv
  have hderiv := roughSaiasDickmanDerivative_abs_le_one
    (u := u - v) (by linarith [hv'.1])
  have hweight := roughSaiasFullyRealFractionalWeight_mem_unitInterval
    hy.le hv'.1
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hweight.1]
  calc
    |roughSaiasDickmanDerivative (u - v)| *
        roughSaiasFullyRealFractionalWeight y v ≤
      1 * roughSaiasFullyRealFractionalWeight y v :=
        mul_le_mul_of_nonneg_right hderiv hweight.1
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hweight.2 (by norm_num)
    _ = 1 := mul_one _

/-! ## Exact real-base substitution -/

theorem roughSaiasFullyRealBaseFreeKernel_rpow_mul_jacobian
    {x y : ℝ} (hy : 1 < y) (v : ℝ) :
    (Real.log y * y ^ v) *
        roughSaiasFullyRealBaseFreeFractionalKernel x y (y ^ v) =
      roughSaiasDickmanDerivative (Real.log x / Real.log y - v) *
        roughSaiasFullyRealFractionalWeight y v := by
  have hypos : 0 < y := zero_lt_one.trans hy
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  have hrpow : y ^ v ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hypos v)
  have hcancel : v * Real.log y / Real.log y = v := by
    field_simp [hlogy]
  have hcoord :
      (Real.log x - v * Real.log y) / Real.log y =
        Real.log x / Real.log y - v := by
    rw [sub_div, hcancel]
  unfold roughSaiasFullyRealBaseFreeFractionalKernel
    roughSaiasFullyRealFractionalWeight
  rw [Real.log_rpow hypos, hcoord, Real.rpow_neg hypos.le]
  field_simp [hlogy, hrpow]



theorem roughSaiasFullyRealBaseFreeKernel_intervalIntegrable
    {x y : ℝ} (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    IntervalIntegrable
      (roughSaiasFullyRealBaseFreeFractionalKernel x y)
      volume (1 : ℝ) (y ^ (5 : ℝ)) := by
  let f : ℝ → ℝ := fun v ↦ y ^ v
  let f' : ℝ → ℝ := fun v ↦ Real.log y * y ^ v
  have hypos : 0 < y := zero_lt_one.trans hy
  have hfderiv : ∀ v ∈ Set.Icc (0 : ℝ) 5,
      HasDerivWithinAt f (f' v) (Set.Icc (0 : ℝ) 5) v := by
    intro v _hv
    simpa [f, f'] using
      ((hasDerivAt_id v).const_rpow hypos).hasDerivWithinAt
  have hfmono : MonotoneOn f (Set.Icc (0 : ℝ) 5) :=
    (Real.strictMono_rpow_of_base_gt_one hy).monotone.monotoneOn _
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 5) :=
    (Real.continuous_const_rpow hypos.ne').continuousOn
  have hfimage : f '' Set.Icc (0 : ℝ) 5 =
      Set.Icc (1 : ℝ) (y ^ (5 : ℝ)) := by
    calc
      f '' Set.Icc (0 : ℝ) 5 = Set.Icc (f 0) (f 5) :=
        hfcont.image_Icc_of_monotoneOn (by norm_num) hfmono
      _ = Set.Icc (1 : ℝ) (y ^ (5 : ℝ)) := by simp [f]
  have horiginal : IntervalIntegrable
      (fun v : ℝ ↦
        roughSaiasDickmanDerivative
            (Real.log x / Real.log y - v) *
          roughSaiasFullyRealFractionalWeight y v)
      volume 0 5 :=
    roughSaiasFullyRealIntegrand_intervalIntegrable hy hu5
  have horiginalIcc :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le
      (by norm_num : (0 : ℝ) ≤ 5)).mp horiginal
  have hjacobianIcc : IntegrableOn
      (fun v : ℝ ↦
        f' v • roughSaiasFullyRealBaseFreeFractionalKernel x y (f v))
      (Set.Icc (0 : ℝ) 5) := by
    apply horiginalIcc.congr_fun _ measurableSet_Icc
    intro v _hv
    simpa [f, f', smul_eq_mul] using
      (roughSaiasFullyRealBaseFreeKernel_rpow_mul_jacobian
        (x := x) hy v).symm
  have hkernelImage : IntegrableOn
      (roughSaiasFullyRealBaseFreeFractionalKernel x y)
      (f '' Set.Icc (0 : ℝ) 5) :=
    (MeasureTheory.integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
      measurableSet_Icc hfderiv hfmono
        (roughSaiasFullyRealBaseFreeFractionalKernel x y)).mpr hjacobianIcc
  rw [hfimage] at hkernelImage
  have hu : (1 : ℝ) ≤ y ^ (5 : ℝ) :=
    Real.one_le_rpow hy.le (by norm_num)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hu).mpr hkernelImage

theorem roughSaiasFullyRealBaseFreeKernel_eq_zero_of_div_lt
    {x y t : ℝ} (hx : 0 < x) (hy : 1 < y)
    (ht : x / y < t) :
    roughSaiasFullyRealBaseFreeFractionalKernel x y t = 0 := by
  have hypos : 0 < y := zero_lt_one.trans hy
  have htpos : 0 < t := (div_pos hx hypos).trans ht
  have hx_lt_ty : x < t * y := (div_lt_iff₀ hypos).mp ht
  have hloglt : Real.log x < Real.log t + Real.log y := by
    have h := Real.strictMonoOn_log hx (mul_pos htpos hypos) hx_lt_ty
    rwa [Real.log_mul htpos.ne' hypos.ne'] at h
  have harg : (Real.log x - Real.log t) / Real.log y < 1 := by
    rw [div_lt_one (Real.log_pos hy)]
    linarith
  unfold roughSaiasFullyRealBaseFreeFractionalKernel
  rw [roughSaiasDickmanDerivative_of_lt_one harg]
  simp

theorem roughSaiasFullyReal_le_rpow_five
    {x y : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    x ≤ y ^ (5 : ℝ) := by
  have hypos : 0 < y := zero_lt_one.trans hy
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hlogx : Real.log x ≤ 5 * Real.log y :=
    (div_le_iff₀ hlogy).mp hu5
  have hcappos : 0 < y ^ (5 : ℝ) := Real.rpow_pos_of_pos hypos 5
  apply (Real.log_le_log_iff hx hcappos).mp
  rw [Real.log_rpow hypos]
  exact hlogx





















/-! ## Exact Stieltjes identification at a real base -/











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

















































/-! ## The genuinely real hyperbola path inside natural cells -/







/-- Algebraic factorization of the fully real base-free kernel along the
real hyperbola. -/
private theorem roughSaiasFullyRealBaseFreeFractionalKernel_hyperbola_eq
    (X : ℕ) (s t : ℝ) :
    roughSaiasFullyRealBaseFreeFractionalKernel ((X : ℝ) / s) s t =
      (Int.fract t / t ^ (2 : ℕ)) *
        roughSaiasFullyRealHyperbolaScaledDickmanKernel X s t := by
  unfold roughSaiasFullyRealBaseFreeFractionalKernel
    roughSaiasFullyRealHyperbolaScaledDickmanKernel
    roughSaiasFullyRealHyperbolaCoordinate
  ring

/-- Logarithmic normal form of the real-hyperbola coordinate. -/
private theorem roughSaiasFullyRealHyperbolaCoordinate_eq
    {X : ℕ} {s t : ℝ} (hX : 0 < X) (hs : 1 < s) :
    roughSaiasFullyRealHyperbolaCoordinate X s t =
      (Real.log (X : ℝ) - Real.log t) / Real.log s - 1 := by
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hspos : 0 < s := zero_lt_one.trans hs
  have hlogs : Real.log s ≠ 0 := (Real.log_pos hs).ne'
  unfold roughSaiasFullyRealHyperbolaCoordinate
  rw [Real.log_div hXR.ne' hspos.ne']
  field_simp [hlogs]
  ring

/-- Every real-hyperbola coordinate in the compact block remains on the
five constructed faces. -/
theorem roughSaiasFullyRealHyperbolaCoordinate_le_five
    {X a : ℕ} {s t : ℝ} (hX : 0 < X) (ha2 : 2 ≤ a)
    (has : (a : ℝ) ≤ s) (_hsX : s ≤ (X : ℝ)) (ht1 : 1 ≤ t)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    roughSaiasFullyRealHyperbolaCoordinate X s t ≤ 5 := by
  have hapos : (0 : ℝ) < (a : ℝ) := by positivity
  have hsone : 1 < s :=
    (by exact_mod_cast (show 1 < a by omega) : (1 : ℝ) < (a : ℝ)).trans_le has
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hlogs : 0 < Real.log s :=
    Real.log_pos ((by exact_mod_cast (show 1 < a by omega) :
      (1 : ℝ) < (a : ℝ)).trans_le has)
  have hlogX0 : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hlogas : Real.log (a : ℝ) ≤ Real.log s :=
    Real.log_le_log hapos has
  have hratio : Real.log (X : ℝ) / Real.log s ≤
      Real.log (X : ℝ) / Real.log (a : ℝ) :=
    div_le_div_of_nonneg_left hlogX0 hloga hlogas
  rw [roughSaiasFullyRealHyperbolaCoordinate_eq hX hsone]
  calc
    (Real.log (X : ℝ) - Real.log t) / Real.log s - 1 ≤
        Real.log (X : ℝ) / Real.log s := by
      have hsub :
          (Real.log (X : ℝ) - Real.log t) / Real.log s ≤
            Real.log (X : ℝ) / Real.log s :=
        div_le_div_of_nonneg_right
          (sub_le_self (Real.log (X : ℝ)) hlogt0) hlogs.le
      linarith
    _ ≤ Real.log (X : ℝ) / Real.log (a : ℝ) := hratio
    _ ≤ 5 := hu5

/-- Uniform inverse-log envelope for the continuously moving scaled
Dickman kernel on the five constructed faces. -/
private theorem roughSaiasFullyRealHyperbolaScaledDickmanKernel_abs_le_inv_log
    {X : ℕ} {s t : ℝ} (hs : 1 < s)
    (hu5 : roughSaiasFullyRealHyperbolaCoordinate X s t ≤ 5) :
    |roughSaiasFullyRealHyperbolaScaledDickmanKernel X s t| ≤
      1 / Real.log s := by
  have hlogs : 0 < Real.log s := Real.log_pos hs
  unfold roughSaiasFullyRealHyperbolaScaledDickmanKernel
  rw [abs_div, abs_of_pos hlogs]
  exact div_le_div_of_nonneg_right
    (roughSaiasDickmanDerivative_abs_le_one hu5) hlogs.le



/-- Active-face cancellation for the real-hyperbola scaled kernel. -/
private theorem roughSaiasFullyRealHyperbolaScaledDickmanKernel_eq_neg_rho_div
    {X : ℕ} {s t : ℝ} (hX : 0 < X) (hs : 1 < s)
    (hu1 : 1 ≤ roughSaiasFullyRealHyperbolaCoordinate X s t) :
    roughSaiasFullyRealHyperbolaScaledDickmanKernel X s t =
      -rho (roughSaiasFullyRealHyperbolaCoordinate X s t - 1) /
        (Real.log (X : ℝ) - Real.log t - Real.log s) := by
  have hlogs : Real.log s ≠ 0 := (Real.log_pos hs).ne'
  have hcoordinate :
      roughSaiasFullyRealHyperbolaCoordinate X s t * Real.log s =
        Real.log (X : ℝ) - Real.log t - Real.log s := by
    rw [roughSaiasFullyRealHyperbolaCoordinate_eq hX hs]
    field_simp [hlogs]
  unfold roughSaiasFullyRealHyperbolaScaledDickmanKernel
  rw [roughSaiasDickmanDerivative_of_one_le hu1, div_div, hcoordinate]

/-- The support inequality `t ≤ X/s²` is exactly the active-face condition
for the real-hyperbola coordinate. -/
private theorem one_le_roughSaiasFullyRealHyperbolaCoordinate_of_le_support
    {X : ℕ} {s t : ℝ} (_hX : 0 < X) (hs : 1 < s) (htpos : 0 < t)
    (htactive : t ≤ (X : ℝ) / s ^ (2 : ℕ)) :
    1 ≤ roughSaiasFullyRealHyperbolaCoordinate X s t := by
  have hspos : 0 < s := zero_lt_one.trans hs
  unfold roughSaiasFullyRealHyperbolaCoordinate
  rw [one_le_div (Real.log_pos hs)]
  have hts : t * s ≤ (X : ℝ) / s := by
    rw [le_div_iff₀ hspos, mul_assoc]
    simpa only [pow_two] using
      ((le_div_iff₀ (sq_pos_of_pos hspos)).mp htactive)
  have hlog := Real.log_le_log (mul_pos htpos hspos) hts
  rw [Real.log_mul htpos.ne' hspos.ne'] at hlog
  linarith

/-- The scaled kernel vanishes after the continuously moving support
`X / s^2`. -/
private theorem roughSaiasFullyRealHyperbolaScaledDickmanKernel_eq_zero_of_support_lt
    {X : ℕ} {s t : ℝ} (hX : 0 < X) (hs : 1 < s)
    (ht : (X : ℝ) / s ^ (2 : ℕ) < t) :
    roughSaiasFullyRealHyperbolaScaledDickmanKernel X s t = 0 := by
  have hXR : 0 < (X : ℝ) := by exact_mod_cast hX
  have hspos : 0 < s := zero_lt_one.trans hs
  have hsupportPos : 0 < (X : ℝ) / s ^ (2 : ℕ) := by positivity
  have htpos : 0 < t := hsupportPos.trans ht
  have hquotLt : (X : ℝ) / s < t * s := by
    rw [div_lt_iff₀ hspos]
    have := (div_lt_iff₀ (sq_pos_of_pos hspos)).mp ht
    nlinarith
  have hlogLt : Real.log ((X : ℝ) / s) <
      Real.log t + Real.log s := by
    have hquotPos : 0 < (X : ℝ) / s := div_pos hXR hspos
    have h := Real.strictMonoOn_log hquotPos (mul_pos htpos hspos) hquotLt
    rwa [Real.log_mul htpos.ne' hspos.ne'] at h
  have hcoord : roughSaiasFullyRealHyperbolaCoordinate X s t < 1 := by
    unfold roughSaiasFullyRealHyperbolaCoordinate
    rw [div_lt_one (Real.log_pos hs)]
    linarith
  unfold roughSaiasFullyRealHyperbolaScaledDickmanKernel
  rw [roughSaiasDickmanDerivative_of_lt_one hcoord]
  simp

/-- Along an active part of the genuinely real hyperbola the scaled kernel
is antitone in the moving base.  The quotient decrease and the base increase
reinforce one another. -/
private theorem roughSaiasFullyRealHyperbolaScaledDickmanKernel_le_of_le_of_active
    {X : ℕ} {s r t : ℝ} (hX : 0 < X) (hs : 1 < s)
    (hsr : s ≤ r) (htpos : 0 < t)
    (htactive : t ≤ (X : ℝ) / r ^ (2 : ℕ))
    (hus5 : roughSaiasFullyRealHyperbolaCoordinate X s t ≤ 5) :
    roughSaiasFullyRealHyperbolaScaledDickmanKernel X r t ≤
      roughSaiasFullyRealHyperbolaScaledDickmanKernel X s t := by
  have hspos : 0 < s := zero_lt_one.trans hs
  have hrone : 1 < r := hs.trans_le hsr
  have hrpos : 0 < r := zero_lt_one.trans hrone
  have hlogs : 0 < Real.log s := Real.log_pos hs
  have hlogr : 0 < Real.log r := Real.log_pos hrone
  have hlogsr : Real.log s ≤ Real.log r :=
    Real.log_le_log hspos hsr
  have htrSq : t * r ^ (2 : ℕ) ≤ (X : ℝ) :=
    (le_div_iff₀ (sq_pos_of_pos hrpos)).mp htactive
  have htX : t ≤ (X : ℝ) := by
    have hrSqOne : (1 : ℝ) ≤ r ^ (2 : ℕ) := by nlinarith
    nlinarith
  have hA0 : 0 ≤ Real.log (X : ℝ) - Real.log t :=
    sub_nonneg.mpr (Real.log_le_log htpos htX)
  have hcoord : roughSaiasFullyRealHyperbolaCoordinate X r t ≤
      roughSaiasFullyRealHyperbolaCoordinate X s t := by
    rw [roughSaiasFullyRealHyperbolaCoordinate_eq hX hrone,
      roughSaiasFullyRealHyperbolaCoordinate_eq hX hs]
    exact sub_le_sub_right
      (div_le_div_of_nonneg_left hA0 hlogs hlogsr) 1
  have huR1 : 1 ≤ roughSaiasFullyRealHyperbolaCoordinate X r t :=
    one_le_roughSaiasFullyRealHyperbolaCoordinate_of_le_support
      hX hrone htpos htactive
  have huS1 : 1 ≤ roughSaiasFullyRealHyperbolaCoordinate X s t :=
    huR1.trans hcoord
  have huR5 : roughSaiasFullyRealHyperbolaCoordinate X r t ≤ 5 :=
    hcoord.trans hus5
  have hrho :
      rho (roughSaiasFullyRealHyperbolaCoordinate X s t - 1) ≤
        rho (roughSaiasFullyRealHyperbolaCoordinate X r t - 1) :=
    roughRho_antitoneOn_zero_five
      (show roughSaiasFullyRealHyperbolaCoordinate X r t - 1 ∈
          Icc (0 : ℝ) 5 by constructor <;> linarith)
      (show roughSaiasFullyRealHyperbolaCoordinate X s t - 1 ∈
          Icc (0 : ℝ) 5 by constructor <;> linarith)
      (by linarith)
  have hdenomS : 0 < Real.log (X : ℝ) - Real.log t - Real.log s := by
    have hidentity :
        roughSaiasFullyRealHyperbolaCoordinate X s t * Real.log s =
          Real.log (X : ℝ) - Real.log t - Real.log s := by
      rw [roughSaiasFullyRealHyperbolaCoordinate_eq hX hs]
      field_simp [hlogs.ne']
    rw [← hidentity]
    exact mul_pos (zero_lt_one.trans_le huS1) hlogs
  have hdenomR : 0 < Real.log (X : ℝ) - Real.log t - Real.log r := by
    have hidentity :
        roughSaiasFullyRealHyperbolaCoordinate X r t * Real.log r =
          Real.log (X : ℝ) - Real.log t - Real.log r := by
      rw [roughSaiasFullyRealHyperbolaCoordinate_eq hX hrone]
      field_simp [hlogr.ne']
    rw [← hidentity]
    exact mul_pos (zero_lt_one.trans_le huR1) hlogr
  have hdenomLe :
      Real.log (X : ℝ) - Real.log t - Real.log r ≤
        Real.log (X : ℝ) - Real.log t - Real.log s := by
    linarith
  have hrhoNonneg :
      0 ≤ rho (roughSaiasFullyRealHyperbolaCoordinate X r t - 1) :=
    (rho_pos_on_zero_five (by linarith) (by linarith)).le
  rw [roughSaiasFullyRealHyperbolaScaledDickmanKernel_eq_neg_rho_div
      hX hrone huR1,
    roughSaiasFullyRealHyperbolaScaledDickmanKernel_eq_neg_rho_div
      hX hs huS1]
  rw [neg_div, neg_div]
  apply neg_le_neg
  calc
    rho (roughSaiasFullyRealHyperbolaCoordinate X s t - 1) /
          (Real.log (X : ℝ) - Real.log t - Real.log s) ≤
        rho (roughSaiasFullyRealHyperbolaCoordinate X r t - 1) /
          (Real.log (X : ℝ) - Real.log t - Real.log s) :=
      div_le_div_of_nonneg_right hrho hdenomS.le
    _ ≤ rho (roughSaiasFullyRealHyperbolaCoordinate X r t - 1) /
          (Real.log (X : ℝ) - Real.log t - Real.log r) :=
      div_le_div_of_nonneg_left hrhoNonneg hdenomR hdenomLe

/-- The cell envelope indeed dominates every within-cell oscillation to
the right endpoint. -/
private theorem roughSaiasFullyRealHyperbolaScaledDickmanKernel_cell_abs_sub_le
    {X a b m : ℕ} (hX : 0 < X) (ha2 : 2 ≤ a) (_hab : a ≤ b)
    (hbX : b ≤ X) (hm : m ∈ Finset.Ico a b)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5)
    {s t : ℝ} (hs : s ∈ Set.Icc (m : ℝ) (m + 1 : ℕ))
    (ht1 : 1 ≤ t) :
    |roughSaiasFullyRealHyperbolaScaledDickmanKernel X s t -
        roughSaiasFullyRealHyperbolaScaledDickmanKernel
          X ((m + 1 : ℕ) : ℝ) t| ≤
      roughSaiasFullyRealHyperbolaCellKernelOscillation X m t := by
  have hmData := Finset.mem_Ico.mp hm
  have hnextX : m + 1 ≤ X := by omega
  have hmone : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
  have hsone : 1 < s := hmone.trans_le hs.1
  have hnextOne : (1 : ℝ) < ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < m + 1 by omega)
  have htpos : 0 < t := zero_lt_one.trans_le ht1
  have hamR : (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmData.1
  have hmXR : (m : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast (show m ≤ X by omega)
  have hnextXR : ((m + 1 : ℕ) : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast hnextX
  have hfaceM := roughSaiasFullyRealHyperbolaCoordinate_le_five
    (s := (m : ℝ)) hX ha2 hamR hmXR ht1 hu5
  have hfaceS := roughSaiasFullyRealHyperbolaCoordinate_le_five
    (s := s) hX ha2 (hamR.trans hs.1) (hs.2.trans hnextXR) ht1 hu5
  by_cases hright :
      t ≤ (X : ℝ) / (((m + 1 : ℕ) : ℝ) ^ (2 : ℕ))
  · have hnextS :=
      roughSaiasFullyRealHyperbolaScaledDickmanKernel_le_of_le_of_active
        hX hsone hs.2 htpos hright hfaceS
    have hSm :=
      roughSaiasFullyRealHyperbolaScaledDickmanKernel_le_of_le_of_active
        hX hmone hs.1 htpos (hright.trans (by
          exact div_le_div_of_nonneg_left (by positivity)
            (sq_pos_of_pos (by positivity : (0 : ℝ) < s))
            (by nlinarith [hs.2]))) hfaceM
    rw [roughSaiasFullyRealHyperbolaCellKernelOscillation, if_pos hright,
      abs_of_nonneg (sub_nonneg.mpr hnextS)]
    linarith
  · have hrightLt := lt_of_not_ge hright
    have hnextZero :=
      roughSaiasFullyRealHyperbolaScaledDickmanKernel_eq_zero_of_support_lt
        hX hnextOne hrightLt
    by_cases hleft : t ≤ (X : ℝ) / ((m : ℝ) ^ (2 : ℕ))
    · have hlogsM : 0 < Real.log (m : ℝ) := Real.log_pos hmone
      have hlogMS : Real.log (m : ℝ) ≤ Real.log s :=
        Real.log_le_log (zero_lt_one.trans hmone) hs.1
      have hinv : 1 / Real.log s ≤ 1 / Real.log (m : ℝ) :=
        one_div_le_one_div_of_le hlogsM hlogMS
      have hSabs :
          |roughSaiasFullyRealHyperbolaScaledDickmanKernel X s t| ≤
            1 / Real.log (m : ℝ) := by
        by_cases hsactive : t ≤ (X : ℝ) / s ^ (2 : ℕ)
        · exact (roughSaiasFullyRealHyperbolaScaledDickmanKernel_abs_le_inv_log
              hsone hfaceS).trans hinv
        · rw [roughSaiasFullyRealHyperbolaScaledDickmanKernel_eq_zero_of_support_lt
              hX hsone (lt_of_not_ge hsactive), abs_zero]
          positivity
      rw [hnextZero, sub_zero,
        roughSaiasFullyRealHyperbolaCellKernelOscillation,
        if_neg hright, if_pos hleft]
      exact hSabs
    · have hleftLt := lt_of_not_ge hleft
      have hSsupport : (X : ℝ) / s ^ (2 : ℕ) < t := by
        exact (div_le_div_of_nonneg_left (by positivity)
          (sq_pos_of_pos (by positivity : (0 : ℝ) < (m : ℝ)))
          (by nlinarith [hs.1])).trans_lt hleftLt
      have hSzero :=
        roughSaiasFullyRealHyperbolaScaledDickmanKernel_eq_zero_of_support_lt
          hX hsone hSsupport
      rw [hSzero, hnextZero, sub_self, abs_zero,
        roughSaiasFullyRealHyperbolaCellKernelOscillation,
        if_neg hright, if_neg hleft]







/-- Measurability of the moving scaled kernel in the sawtooth variable. -/
private theorem measurable_roughSaiasFullyRealHyperbolaScaledDickmanKernel
    (X : ℕ) (s : ℝ) :
    Measurable (roughSaiasFullyRealHyperbolaScaledDickmanKernel X s) := by
  unfold roughSaiasFullyRealHyperbolaScaledDickmanKernel
    roughSaiasFullyRealHyperbolaCoordinate
  exact (measurable_roughSaiasDickmanDerivative.comp
      ((measurable_const.sub measurable_id.log).div measurable_const)).div
    measurable_const

/-- Measurability of one deterministic cell envelope. -/
private theorem measurable_roughSaiasFullyRealHyperbolaCellKernelOscillation
    (X m : ℕ) :
    Measurable (roughSaiasFullyRealHyperbolaCellKernelOscillation X m) := by
  unfold roughSaiasFullyRealHyperbolaCellKernelOscillation
  apply Measurable.ite measurableSet_Iic
  · exact
      (measurable_roughSaiasFullyRealHyperbolaScaledDickmanKernel X (m : ℝ)).sub
        (measurable_roughSaiasFullyRealHyperbolaScaledDickmanKernel
          X ((m + 1 : ℕ) : ℝ))
  · exact Measurable.ite measurableSet_Iic measurable_const measurable_const

/-- Measurability of the weighted cell envelope. -/
private theorem measurable_roughSaiasFullyRealHyperbolaCellFractionalOscillation
    (X m : ℕ) :
    Measurable (roughSaiasFullyRealHyperbolaCellFractionalOscillation X m) := by
  unfold roughSaiasFullyRealHyperbolaCellFractionalOscillation
  exact (measurable_id.fract.div (measurable_id.pow_const _)).mul
    (measurable_roughSaiasFullyRealHyperbolaCellKernelOscillation X m)

/-- Each cell envelope is nonnegative. -/
private theorem roughSaiasFullyRealHyperbolaCellKernelOscillation_nonneg
    {X a b m : ℕ} (hX : 0 < X) (ha2 : 2 ≤ a) (hab : a ≤ b)
    (hbX : b ≤ X) (hm : m ∈ Finset.Ico a b) {t : ℝ} (ht1 : 1 ≤ t)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    0 ≤ roughSaiasFullyRealHyperbolaCellKernelOscillation X m t := by
  have hbound :=
    roughSaiasFullyRealHyperbolaScaledDickmanKernel_cell_abs_sub_le
      hX ha2 hab hbX hm hu5
        (s := (m : ℝ)) (t := t)
        ⟨le_rfl, by exact_mod_cast (Nat.le_succ m)⟩ ht1
  exact (abs_nonneg _).trans hbound

/-- A single cell envelope is bounded by two inverse logarithms of the
first base. -/
private theorem roughSaiasFullyRealHyperbolaCellKernelOscillation_le_two_inv_log
    {X a b m : ℕ} (hX : 0 < X) (ha2 : 2 ≤ a) (_hab : a ≤ b)
    (hbX : b ≤ X) (hm : m ∈ Finset.Ico a b) {t : ℝ} (ht1 : 1 ≤ t)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    roughSaiasFullyRealHyperbolaCellKernelOscillation X m t ≤
      2 / Real.log (a : ℝ) := by
  have hmData := Finset.mem_Ico.mp hm
  have hnextX : m + 1 ≤ X := by omega
  have hmOne : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
  have hnextOne : (1 : ℝ) < ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < m + 1 by omega)
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hlogam : Real.log (a : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hmData.1)
  have hlogmnext : Real.log (m : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (Nat.le_succ m))
  have hinvM : 1 / Real.log (m : ℝ) ≤ 1 / Real.log (a : ℝ) :=
    one_div_le_one_div_of_le hloga hlogam
  have hinvNext : 1 / Real.log ((m + 1 : ℕ) : ℝ) ≤
      1 / Real.log (a : ℝ) :=
    (one_div_le_one_div_of_le (Real.log_pos hmOne) hlogmnext).trans hinvM
  by_cases hright :
      t ≤ (X : ℝ) / (((m + 1 : ℕ) : ℝ) ^ (2 : ℕ))
  · have hamR : (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmData.1
    have hmXR : (m : ℝ) ≤ (X : ℝ) := by
      exact_mod_cast (show m ≤ X by omega)
    have haNextR : (a : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show a ≤ m + 1 by omega)
    have hnextXR : ((m + 1 : ℕ) : ℝ) ≤ (X : ℝ) := by
      exact_mod_cast hnextX
    have hfaceM := roughSaiasFullyRealHyperbolaCoordinate_le_five
      (s := (m : ℝ)) hX ha2 hamR hmXR ht1 hu5
    have hfaceNext := roughSaiasFullyRealHyperbolaCoordinate_le_five
      (s := ((m + 1 : ℕ) : ℝ)) hX ha2 haNextR hnextXR ht1 hu5
    have hMabs :=
      roughSaiasFullyRealHyperbolaScaledDickmanKernel_abs_le_inv_log
        hmOne hfaceM
    have hNextAbs :=
      roughSaiasFullyRealHyperbolaScaledDickmanKernel_abs_le_inv_log
        hnextOne hfaceNext
    rw [roughSaiasFullyRealHyperbolaCellKernelOscillation, if_pos hright]
    calc
      roughSaiasFullyRealHyperbolaScaledDickmanKernel X (m : ℝ) t -
          roughSaiasFullyRealHyperbolaScaledDickmanKernel
            X ((m + 1 : ℕ) : ℝ) t ≤
        |roughSaiasFullyRealHyperbolaScaledDickmanKernel X (m : ℝ) t| +
          |roughSaiasFullyRealHyperbolaScaledDickmanKernel
            X ((m + 1 : ℕ) : ℝ) t| := by
              exact (le_abs_self _).trans (abs_sub _ _)
      _ ≤ 1 / Real.log (m : ℝ) +
          1 / Real.log ((m + 1 : ℕ) : ℝ) := add_le_add hMabs hNextAbs
      _ ≤ 1 / Real.log (a : ℝ) + 1 / Real.log (a : ℝ) :=
        add_le_add hinvM hinvNext
      _ = 2 / Real.log (a : ℝ) := by ring
  · by_cases hleft : t ≤ (X : ℝ) / ((m : ℝ) ^ (2 : ℕ))
    · rw [roughSaiasFullyRealHyperbolaCellKernelOscillation,
        if_neg hright, if_pos hleft]
      have hinvA : 0 ≤ 1 / Real.log (a : ℝ) :=
        (one_div_pos.mpr hloga).le
      exact hinvM.trans (by
        calc
          1 / Real.log (a : ℝ) ≤
              1 / Real.log (a : ℝ) + 1 / Real.log (a : ℝ) :=
            le_add_of_nonneg_right hinvA
          _ = 2 / Real.log (a : ℝ) := by ring)
    · rw [roughSaiasFullyRealHyperbolaCellKernelOscillation,
        if_neg hright, if_neg hleft]
      exact div_nonneg (by norm_num) hloga.le

/-- The weighted envelope is interval-integrable on the common cap. -/
private theorem roughSaiasFullyRealHyperbolaCellFractionalOscillation_intervalIntegrable
    {X a b m : ℕ} (hX : 0 < X) (ha2 : 2 ≤ a) (hab : a ≤ b)
    (hbX : b ≤ X) (hm : m ∈ Finset.Ico a b)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    IntervalIntegrable
      (roughSaiasFullyRealHyperbolaCellFractionalOscillation X m)
      volume (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have haCapOne : (1 : ℝ) ≤ (a : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ a by omega)) (by norm_num)
  have hzeroNotMem : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) :=
    Set.notMem_uIcc_of_lt (by norm_num) (by positivity)
  have hinvSq : IntervalIntegrable (fun t : ℝ => 1 / t ^ (2 : ℕ))
      volume (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
    simpa [one_div, zpow_neg] using
      (intervalIntegral.intervalIntegrable_zpow
        (a := (1 : ℝ)) (b := (a : ℝ) ^ (5 : ℝ))
        (n := (-2 : ℤ)) (Or.inr hzeroNotMem))
  have hmajor := hinvSq.const_mul (2 / Real.log (a : ℝ))
  apply hmajor.mono_fun'
    (measurable_roughSaiasFullyRealHyperbolaCellFractionalOscillation
      X m).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  have htI : t ∈ Set.Icc (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
    rw [← Set.uIcc_of_le haCapOne]
    exact Set.uIoc_subset_uIcc ht
  have htpos : 0 < t := zero_lt_one.trans_le htI.1
  have htSqPos : 0 < t ^ (2 : ℕ) := pow_pos htpos 2
  have hfactorNonneg : 0 ≤ Int.fract t / t ^ (2 : ℕ) :=
    div_nonneg (Int.fract_nonneg t) htSqPos.le
  have hfactorLe : Int.fract t / t ^ (2 : ℕ) ≤ 1 / t ^ (2 : ℕ) :=
    div_le_div_of_nonneg_right (Int.fract_lt_one t).le htSqPos.le
  have hoscNonneg :=
    roughSaiasFullyRealHyperbolaCellKernelOscillation_nonneg
      hX ha2 hab hbX hm htI.1 hu5
  have hoscBound :=
    roughSaiasFullyRealHyperbolaCellKernelOscillation_le_two_inv_log
      hX ha2 hab hbX hm htI.1 hu5
  unfold roughSaiasFullyRealHyperbolaCellFractionalOscillation
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hfactorNonneg hoscNonneg)]
  calc
    (Int.fract t / t ^ (2 : ℕ)) *
        roughSaiasFullyRealHyperbolaCellKernelOscillation X m t ≤
      (Int.fract t / t ^ (2 : ℕ)) * (2 / Real.log (a : ℝ)) :=
        mul_le_mul_of_nonneg_left hoscBound hfactorNonneg
    _ ≤ (1 / t ^ (2 : ℕ)) * (2 / Real.log (a : ℝ)) :=
      mul_le_mul_of_nonneg_right hfactorLe (by positivity)
    _ = (2 / Real.log (a : ℝ)) * (1 / t ^ (2 : ℕ)) := by ring



/-- On a compact real-hyperbola block, the fully real fractional integral
may be placed on the single smallest cap `a^5`. -/
private theorem roughSaiasFullyRealBaseFreeFractionalIntegral_hyperbola_eq_firstCap
    {X a b : ℕ} (hX : 0 < X) (ha2 : 2 ≤ a) (_hab : a ≤ b)
    (hbX : b ≤ X) {s : ℝ} (hs : s ∈ Set.Icc (a : ℝ) (b : ℝ))
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    roughSaiasFullyRealBaseFreeFractionalIntegral ((X : ℝ) / s) s =
      ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
        (Int.fract t / t ^ (2 : ℕ)) *
          roughSaiasFullyRealHyperbolaScaledDickmanKernel X s t := by
  have haOne : (1 : ℝ) < (a : ℝ) := by exact_mod_cast (show 1 < a by omega)
  have hsOne : 1 < s := haOne.trans_le hs.1
  have hspos : 0 < s := zero_lt_one.trans hsOne
  have hXreal : 0 < (X : ℝ) := by exact_mod_cast hX
  have hbXR : (b : ℝ) ≤ (X : ℝ) := by exact_mod_cast hbX
  have hface := roughSaiasFullyRealHyperbolaCoordinate_le_five
    (s := s) (t := (1 : ℝ)) hX ha2 hs.1 (hs.2.trans hbXR)
      (by norm_num) hu5
  have hratio : Real.log ((X : ℝ) / s) / Real.log s ≤ 5 := by
    simpa [roughSaiasFullyRealHyperbolaCoordinate] using hface
  have hnative := roughSaiasFullyRealBaseFreeKernel_intervalIntegrable
    (x := (X : ℝ) / s) hsOne hratio
  have haCapOne : (1 : ℝ) ≤ (a : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ a by omega)) (by norm_num)
  have haCapS : (a : ℝ) ^ (5 : ℝ) ≤ s ^ (5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hs.1 (by norm_num)
  have hcommon : IntervalIntegrable
      (roughSaiasFullyRealBaseFreeFractionalKernel ((X : ℝ) / s) s)
      volume (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
    apply hnative.mono_set
    rw [Set.uIcc_of_le haCapOne,
      Set.uIcc_of_le (haCapOne.trans haCapS)]
    exact Set.Icc_subset_Icc le_rfl haCapS
  have htail : IntervalIntegrable
      (roughSaiasFullyRealBaseFreeFractionalKernel ((X : ℝ) / s) s)
      volume ((a : ℝ) ^ (5 : ℝ)) (s ^ (5 : ℝ)) := by
    apply hnative.mono_set
    rw [Set.uIcc_of_le haCapS,
      Set.uIcc_of_le (haCapOne.trans haCapS)]
    exact Set.Icc_subset_Icc haCapOne le_rfl
  have hXcap : (X : ℝ) ≤ (a : ℝ) ^ (5 : ℝ) :=
    roughSaiasFullyReal_le_rpow_five hXreal haOne hu5
  have hsupport : ((X : ℝ) / s) / s < (a : ℝ) ^ (5 : ℝ) := by
    calc
      ((X : ℝ) / s) / s < (X : ℝ) / s :=
        div_lt_self (div_pos hXreal hspos) hsOne
      _ < (X : ℝ) := div_lt_self hXreal hsOne
      _ ≤ (a : ℝ) ^ (5 : ℝ) := hXcap
  have htailZero :
      (∫ t in (a : ℝ) ^ (5 : ℝ)..s ^ (5 : ℝ),
          roughSaiasFullyRealBaseFreeFractionalKernel ((X : ℝ) / s) s t) = 0 := by
    calc
      (∫ t in (a : ℝ) ^ (5 : ℝ)..s ^ (5 : ℝ),
          roughSaiasFullyRealBaseFreeFractionalKernel ((X : ℝ) / s) s t) =
        ∫ _t in (a : ℝ) ^ (5 : ℝ)..s ^ (5 : ℝ), (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          have htI : t ∈ Set.Icc ((a : ℝ) ^ (5 : ℝ)) (s ^ (5 : ℝ)) := by
            rw [Set.uIcc_of_le haCapS] at ht
            exact ht
          exact roughSaiasFullyRealBaseFreeKernel_eq_zero_of_div_lt
            (div_pos hXreal hspos) hsOne (hsupport.trans_le htI.1)
      _ = 0 := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hcommon htail
  unfold roughSaiasFullyRealBaseFreeFractionalIntegral
  rw [← hsplit, htailZero, add_zero]
  apply intervalIntegral.integral_congr
  intro t _ht
  exact roughSaiasFullyRealBaseFreeFractionalKernel_hyperbola_eq X s t

/-- One within-cell fully real fractional-integral displacement is bounded
by its deterministic integrated oscillation ledger. -/
theorem roughSaiasFullyRealBaseFreeFractionalIntegral_hyperbola_cell_abs_sub_le
    {X a b m : ℕ} (hX : 0 < X) (ha2 : 2 ≤ a) (hab : a ≤ b)
    (hbX : b ≤ X) (hm : m ∈ Finset.Ico a b)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5)
    {s : ℝ} (hs : s ∈ Set.Icc (m : ℝ) (m + 1 : ℕ)) :
    |roughSaiasFullyRealBaseFreeFractionalIntegral ((X : ℝ) / s) s -
        roughSaiasFullyRealBaseFreeFractionalIntegral
          ((X : ℝ) / (m + 1 : ℕ)) (m + 1 : ℕ)| ≤
      roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m := by
  have hmData := Finset.mem_Ico.mp hm
  have hsmem : s ∈ Set.Icc (a : ℝ) (b : ℝ) := by
    constructor
    · exact (by exact_mod_cast hmData.1 : (a : ℝ) ≤ (m : ℝ)).trans hs.1
    · exact hs.2.trans (by exact_mod_cast (show m + 1 ≤ b by omega))
  have hnextmem : ((m + 1 : ℕ) : ℝ) ∈ Set.Icc (a : ℝ) (b : ℝ) := by
    constructor
    · exact_mod_cast (show a ≤ m + 1 by omega)
    · exact_mod_cast (show m + 1 ≤ b by omega)
  have hsEq := roughSaiasFullyRealBaseFreeFractionalIntegral_hyperbola_eq_firstCap
    hX ha2 hab hbX hsmem hu5
  have hnextEq :=
    roughSaiasFullyRealBaseFreeFractionalIntegral_hyperbola_eq_firstCap
      hX ha2 hab hbX hnextmem hu5
  have hsOne : 1 < s :=
    (by exact_mod_cast (show 1 < a by omega) : (1 : ℝ) < (a : ℝ)).trans_le hsmem.1
  have hnextOne : (1 : ℝ) < ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < m + 1 by omega)
  have hbXR : (b : ℝ) ≤ (X : ℝ) := by exact_mod_cast hbX
  have hfaceS := roughSaiasFullyRealHyperbolaCoordinate_le_five
    (s := s) (t := (1 : ℝ)) hX ha2 hsmem.1
      (hsmem.2.trans hbXR) (by norm_num) hu5
  have hfaceNext := roughSaiasFullyRealHyperbolaCoordinate_le_five
    (s := ((m + 1 : ℕ) : ℝ)) (t := (1 : ℝ)) hX ha2
      hnextmem.1 (hnextmem.2.trans hbXR) (by norm_num) hu5
  have hcapS :=
    (roughSaiasFullyRealBaseFreeKernel_intervalIntegrable
      (x := (X : ℝ) / s) hsOne
      (by simpa [roughSaiasFullyRealHyperbolaCoordinate] using hfaceS)).mono_set
      (by
        have haCapOne : (1 : ℝ) ≤ (a : ℝ) ^ (5 : ℝ) :=
          Real.one_le_rpow (by exact_mod_cast (show 1 ≤ a by omega)) (by norm_num)
        have haCapS : (a : ℝ) ^ (5 : ℝ) ≤ s ^ (5 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hsmem.1 (by norm_num)
        rw [Set.uIcc_of_le haCapOne, Set.uIcc_of_le (haCapOne.trans haCapS)]
        exact Set.Icc_subset_Icc le_rfl haCapS)
  have hcapNext :=
    (roughSaiasFullyRealBaseFreeKernel_intervalIntegrable
      (x := (X : ℝ) / (m + 1 : ℕ)) hnextOne
      (by simpa [roughSaiasFullyRealHyperbolaCoordinate] using hfaceNext)).mono_set
      (by
        have haCapOne : (1 : ℝ) ≤ (a : ℝ) ^ (5 : ℝ) :=
          Real.one_le_rpow (by exact_mod_cast (show 1 ≤ a by omega)) (by norm_num)
        have haCapNext : (a : ℝ) ^ (5 : ℝ) ≤
            ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hnextmem.1 (by norm_num)
        rw [Set.uIcc_of_le haCapOne,
          Set.uIcc_of_le (haCapOne.trans haCapNext)]
        exact Set.Icc_subset_Icc le_rfl haCapNext)
  have hcapSWeighted : IntervalIntegrable
      (fun t : ℝ => (Int.fract t / t ^ (2 : ℕ)) *
        roughSaiasFullyRealHyperbolaScaledDickmanKernel X s t)
      volume (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
    apply hcapS.congr
    intro t _ht
    exact roughSaiasFullyRealBaseFreeFractionalKernel_hyperbola_eq X s t
  have hcapNextWeighted : IntervalIntegrable
      (fun t : ℝ => (Int.fract t / t ^ (2 : ℕ)) *
        roughSaiasFullyRealHyperbolaScaledDickmanKernel
          X ((m + 1 : ℕ) : ℝ) t)
      volume (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
    apply hcapNext.congr
    intro t _ht
    exact roughSaiasFullyRealBaseFreeFractionalKernel_hyperbola_eq
      X ((m + 1 : ℕ) : ℝ) t
  have hledgerInt :=
    roughSaiasFullyRealHyperbolaCellFractionalOscillation_intervalIntegrable
      hX ha2 hab hbX hm hu5
  have haCapOne : (1 : ℝ) ≤ (a : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ a by omega)) (by norm_num)
  rw [hsEq, hnextEq,
    ← intervalIntegral.integral_sub hcapSWeighted hcapNextWeighted]
  calc
    |∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
        (Int.fract t / t ^ (2 : ℕ)) *
            roughSaiasFullyRealHyperbolaScaledDickmanKernel X s t -
          (Int.fract t / t ^ (2 : ℕ)) *
            roughSaiasFullyRealHyperbolaScaledDickmanKernel
              X ((m + 1 : ℕ) : ℝ) t| ≤
      ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
        |(Int.fract t / t ^ (2 : ℕ)) *
            roughSaiasFullyRealHyperbolaScaledDickmanKernel X s t -
          (Int.fract t / t ^ (2 : ℕ)) *
            roughSaiasFullyRealHyperbolaScaledDickmanKernel
              X ((m + 1 : ℕ) : ℝ) t| :=
        intervalIntegral.abs_integral_le_integral_abs haCapOne
    _ ≤ ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
        roughSaiasFullyRealHyperbolaCellFractionalOscillation X m t := by
      apply intervalIntegral.integral_mono_on haCapOne
        (hcapSWeighted.sub hcapNextWeighted).abs hledgerInt
      intro t ht
      have htI : t ∈ Set.Icc (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
        simpa [Set.uIcc_of_le haCapOne] using ht
      have htpos : 0 < t := zero_lt_one.trans_le htI.1
      have htSqPos : 0 < t ^ (2 : ℕ) := pow_pos htpos 2
      have hfactorNonneg : 0 ≤ Int.fract t / t ^ (2 : ℕ) :=
        div_nonneg (Int.fract_nonneg t) htSqPos.le
      have hkernel :=
        roughSaiasFullyRealHyperbolaScaledDickmanKernel_cell_abs_sub_le
          hX ha2 hab hbX hm hu5 hs htI.1
      unfold roughSaiasFullyRealHyperbolaCellFractionalOscillation
      rw [← mul_sub, abs_mul, abs_of_nonneg hfactorNonneg]
      exact mul_le_mul_of_nonneg_left hkernel hfactorNonneg
    _ = roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m := by
      rfl









end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_027 := by
  exact @Erdos390.WholePaper.roughSaiasFullyRealBaseFreeFractionalIntegral_hyperbola_cell_abs_sub_le
