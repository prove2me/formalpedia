-- Prove2me | solution 1 for Erdos390.WholePaper.sum_roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger_le_two_inv_log_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:51:28.305166+00:00
-- url     : https://prove2.me/submissions/9722685c-8e26-40ce-a41c-1181568ca07e

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















































/-! ## The genuinely real hyperbola path inside natural cells -/









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

/-- The moving scaled kernel is nonpositive while it lies on an active
constructed face. -/
private theorem roughSaiasFullyRealHyperbolaScaledDickmanKernel_nonpos_of_active
    {X : ℕ} {s t : ℝ} (hs : 1 < s)
    (hu1 : 1 ≤ roughSaiasFullyRealHyperbolaCoordinate X s t)
    (hu5 : roughSaiasFullyRealHyperbolaCoordinate X s t ≤ 5) :
    roughSaiasFullyRealHyperbolaScaledDickmanKernel X s t ≤ 0 := by
  have hlogs : 0 < Real.log s := Real.log_pos hs
  have hrho :
      0 ≤ rho (roughSaiasFullyRealHyperbolaCoordinate X s t - 1) :=
    (rho_pos_on_zero_five (by linarith) (by linarith)).le
  unfold roughSaiasFullyRealHyperbolaScaledDickmanKernel
  rw [roughSaiasDickmanDerivative_of_one_le hu1]
  exact div_nonpos_of_nonpos_of_nonneg
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hrho)
      (by linarith)) hlogs.le

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

/-- The within-cell envelopes have total pointwise mass at most two inverse
logarithms.  Active endpoints form an initial segment; its monotone drops
telescope, and the single possible support-boundary cell costs the second
inverse logarithm. -/
private theorem sum_roughSaiasFullyRealHyperbolaCellKernelOscillation_le_two_inv_log
    {X a b : ℕ} (hX : 0 < X) (ha2 : 2 ≤ a) (_hab : a ≤ b)
    (hbX : b ≤ X) {t : ℝ} (ht1 : 1 ≤ t)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        roughSaiasFullyRealHyperbolaCellKernelOscillation X m t) ≤
      2 / Real.log (a : ℝ) := by
  classical
  let active : Finset ℕ := (Finset.Icc a b).filter
    (fun m => t ≤ (X : ℝ) / ((m : ℝ) ^ (2 : ℕ)))
  have htpos : 0 < t := zero_lt_one.trans_le ht1
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hsupportAntitone : ∀ {m n : ℕ}, a ≤ m → m ≤ n →
      (X : ℝ) / ((n : ℝ) ^ (2 : ℕ)) ≤
        (X : ℝ) / ((m : ℝ) ^ (2 : ℕ)) := by
    intro m n _ham hmn
    exact div_le_div_of_nonneg_left (by positivity)
      (sq_pos_of_pos (by exact_mod_cast (show 0 < m by omega)))
      (by exact_mod_cast (Nat.pow_le_pow_left hmn 2))
  by_cases hactiveNonempty : active.Nonempty
  · let c : ℕ := active.max' hactiveNonempty
    have hcActive : c ∈ active := Finset.max'_mem active hactiveNonempty
    have hcData : c ∈ Finset.Icc a b ∧
        t ≤ (X : ℝ) / ((c : ℝ) ^ (2 : ℕ)) := by
      simpa only [active, Finset.mem_filter] using hcActive
    have hac : a ≤ c := (Finset.mem_Icc.mp hcData.1).1
    have hcb : c ≤ b := (Finset.mem_Icc.mp hcData.1).2
    have hactiveLe : ∀ m, a ≤ m → m ≤ c →
        t ≤ (X : ℝ) / ((m : ℝ) ^ (2 : ℕ)) := by
      intro m ham hmc
      exact hcData.2.trans (hsupportAntitone ham hmc)
    have hinactiveGt : ∀ m, c < m → m ≤ b →
        (X : ℝ) / ((m : ℝ) ^ (2 : ℕ)) < t := by
      intro m hcm hmb
      apply lt_of_not_ge
      intro hmActive
      have hmMem : m ∈ active := by
        simp only [active, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hac.trans hcm.le, hmb⟩, hmActive⟩
      have hmc : m ≤ c := Finset.le_max' active m hmMem
      omega
    have hfaceA := roughSaiasFullyRealHyperbolaCoordinate_le_five
      hX ha2 le_rfl (by exact_mod_cast (hac.trans (hcb.trans hbX))) ht1 hu5
    have htel :
        (∑ m ∈ Finset.Ico a c,
            roughSaiasFullyRealHyperbolaCellKernelOscillation X m t) =
          roughSaiasFullyRealHyperbolaScaledDickmanKernel X (a : ℝ) t -
            roughSaiasFullyRealHyperbolaScaledDickmanKernel X (c : ℝ) t := by
      calc
        (∑ m ∈ Finset.Ico a c,
            roughSaiasFullyRealHyperbolaCellKernelOscillation X m t) =
          ∑ m ∈ Finset.Ico a c,
            (roughSaiasFullyRealHyperbolaScaledDickmanKernel X (m : ℝ) t -
              roughSaiasFullyRealHyperbolaScaledDickmanKernel
                X ((m + 1 : ℕ) : ℝ) t) := by
            apply Finset.sum_congr rfl
            intro m hm
            have hmData := Finset.mem_Ico.mp hm
            have hright := hactiveLe (m + 1) (by omega) (by omega)
            rw [roughSaiasFullyRealHyperbolaCellKernelOscillation,
              if_pos hright]
        _ = roughSaiasFullyRealHyperbolaScaledDickmanKernel X (a : ℝ) t -
            roughSaiasFullyRealHyperbolaScaledDickmanKernel X (c : ℝ) t := by
          simpa only [neg_sub_neg] using
            (Finset.sum_Ico_sub
              (fun m =>
                -roughSaiasFullyRealHyperbolaScaledDickmanKernel
                  X (m : ℝ) t) hac)
    have hcOne : (1 : ℝ) < (c : ℝ) := by exact_mod_cast (show 1 < c by omega)
    have hacR : (a : ℝ) ≤ (c : ℝ) := by exact_mod_cast hac
    have hcXR : (c : ℝ) ≤ (X : ℝ) := by
      exact_mod_cast (hcb.trans hbX)
    have hfaceC := roughSaiasFullyRealHyperbolaCoordinate_le_five
      (s := (c : ℝ)) hX ha2 hacR hcXR ht1 hu5
    have hcCoordOne : 1 ≤ roughSaiasFullyRealHyperbolaCoordinate X (c : ℝ) t :=
      one_le_roughSaiasFullyRealHyperbolaCoordinate_of_le_support
        hX hcOne htpos hcData.2
    have hcNonpos :=
      roughSaiasFullyRealHyperbolaScaledDickmanKernel_nonpos_of_active
        hcOne hcCoordOne hfaceC
    have hcAbs :=
      roughSaiasFullyRealHyperbolaScaledDickmanKernel_abs_le_inv_log
        hcOne hfaceC
    have hlogac : Real.log (a : ℝ) ≤ Real.log (c : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hac)
    have hinvC : 1 / Real.log (c : ℝ) ≤ 1 / Real.log (a : ℝ) :=
      one_div_le_one_div_of_le hloga hlogac
    have htelBound :
        (∑ m ∈ Finset.Ico a c,
            roughSaiasFullyRealHyperbolaCellKernelOscillation X m t) ≤
          1 / Real.log (a : ℝ) := by
      rw [htel]
      calc
        roughSaiasFullyRealHyperbolaScaledDickmanKernel X (a : ℝ) t -
            roughSaiasFullyRealHyperbolaScaledDickmanKernel X (c : ℝ) t ≤
          -roughSaiasFullyRealHyperbolaScaledDickmanKernel X (c : ℝ) t := by
            have haOne : (1 : ℝ) < (a : ℝ) := by
              exact_mod_cast (show 1 < a by omega)
            have haCoordOne :
                1 ≤ roughSaiasFullyRealHyperbolaCoordinate X (a : ℝ) t :=
              one_le_roughSaiasFullyRealHyperbolaCoordinate_of_le_support
                hX haOne htpos (hactiveLe a le_rfl hac)
            have haNonpos :=
              roughSaiasFullyRealHyperbolaScaledDickmanKernel_nonpos_of_active
                haOne haCoordOne hfaceA
            linarith
        _ = |roughSaiasFullyRealHyperbolaScaledDickmanKernel X (c : ℝ) t| :=
          (abs_of_nonpos hcNonpos).symm
        _ ≤ 1 / Real.log (c : ℝ) := hcAbs
        _ ≤ 1 / Real.log (a : ℝ) := hinvC
    rcases hcb.eq_or_lt with hcbEq | hcbLt
    · have htelBound' :
          (∑ m ∈ Finset.Ico a b,
              roughSaiasFullyRealHyperbolaCellKernelOscillation X m t) ≤
            1 / Real.log (a : ℝ) := by
        simpa only [hcbEq] using htelBound
      exact htelBound'.trans (by
        have hinvA : 0 ≤ 1 / Real.log (a : ℝ) := by positivity
        calc
          1 / Real.log (a : ℝ) ≤
              1 / Real.log (a : ℝ) + 1 / Real.log (a : ℝ) :=
            le_add_of_nonneg_right hinvA
          _ = 2 / Real.log (a : ℝ) := by ring)
    · have hcross :
          roughSaiasFullyRealHyperbolaCellKernelOscillation X c t =
            1 / Real.log (c : ℝ) := by
        have hright := hinactiveGt (c + 1) (by omega) (by omega)
        have hrightNot :
            ¬t ≤ (X : ℝ) / (((c + 1 : ℕ) : ℝ) ^ (2 : ℕ)) :=
          not_le.mpr hright
        rw [roughSaiasFullyRealHyperbolaCellKernelOscillation,
          if_neg hrightNot, if_pos hcData.2]
      have htail :
          (∑ m ∈ Finset.Ico (c + 1) b,
              roughSaiasFullyRealHyperbolaCellKernelOscillation X m t) = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        have hmData := Finset.mem_Ico.mp hm
        have hleft := hinactiveGt m (by omega) hmData.2.le
        have hright :
            (X : ℝ) / (((m + 1 : ℕ) : ℝ) ^ (2 : ℕ)) < t :=
          (hsupportAntitone (hac.trans (by omega)) (Nat.le_succ m)).trans_lt hleft
        have hrightNot :
            ¬t ≤ (X : ℝ) / (((m + 1 : ℕ) : ℝ) ^ (2 : ℕ)) :=
          not_le.mpr hright
        have hleftNot : ¬t ≤ (X : ℝ) / ((m : ℝ) ^ (2 : ℕ)) :=
          not_le.mpr hleft
        rw [roughSaiasFullyRealHyperbolaCellKernelOscillation,
          if_neg hrightNot, if_neg hleftNot]
      have htelExprBound :
          roughSaiasFullyRealHyperbolaScaledDickmanKernel X (a : ℝ) t -
              roughSaiasFullyRealHyperbolaScaledDickmanKernel X (c : ℝ) t ≤
            1 / Real.log (a : ℝ) := by
        rw [← htel]
        exact htelBound
      rw [← Finset.sum_Ico_consecutive _ hac hcbLt.le,
        ← Finset.sum_Ico_consecutive _ (Nat.le_succ c)
          (show c + 1 ≤ b by omega), htel, htail]
      simp only [Finset.sum_Ico_succ_top le_rfl, Finset.Ico_self,
        Finset.sum_empty, zero_add, add_zero]
      rw [hcross]
      calc
        roughSaiasFullyRealHyperbolaScaledDickmanKernel X (a : ℝ) t -
              roughSaiasFullyRealHyperbolaScaledDickmanKernel X (c : ℝ) t +
            1 / Real.log (c : ℝ) ≤
          1 / Real.log (a : ℝ) + 1 / Real.log (a : ℝ) :=
            add_le_add htelExprBound hinvC
        _ = 2 / Real.log (a : ℝ) := by ring
  · have hzero : ∀ m ∈ Finset.Ico a b,
        roughSaiasFullyRealHyperbolaCellKernelOscillation X m t = 0 := by
      intro m hm
      have hmData := Finset.mem_Ico.mp hm
      have hmNot : ¬t ≤ (X : ℝ) / ((m : ℝ) ^ (2 : ℕ)) := by
        intro hmActive
        apply hactiveNonempty
        exact ⟨m, by
          simp only [active, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hmData.1, hmData.2.le⟩, hmActive⟩⟩
      have hrightNot :
          ¬t ≤ (X : ℝ) / (((m + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
        intro hright
        exact hmNot (hright.trans (hsupportAntitone hmData.1 (Nat.le_succ m)))
      rw [roughSaiasFullyRealHyperbolaCellKernelOscillation,
        if_neg hrightNot, if_neg hmNot]
    rw [Finset.sum_eq_zero hzero]
    positivity





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

/-- The integrated real-hyperbola cell ledgers have total mass at most
`2/log a`. -/
theorem sum_roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger_le_two_inv_log
    {X a b : ℕ} (hX : 0 < X) (ha2 : 2 ≤ a) (hab : a ≤ b)
    (hbX : b ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m) ≤
      2 / Real.log (a : ℝ) := by
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have haCapOne : (1 : ℝ) ≤ (a : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ a by omega)) (by norm_num)
  have hint : ∀ m ∈ Finset.Ico a b,
      IntervalIntegrable
        (roughSaiasFullyRealHyperbolaCellFractionalOscillation X m)
        volume (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
    intro m hm
    exact
      roughSaiasFullyRealHyperbolaCellFractionalOscillation_intervalIntegrable
        hX ha2 hab hbX hm hu5
  have hsumInt : IntervalIntegrable
      (fun t : ℝ => ∑ m ∈ Finset.Ico a b,
        roughSaiasFullyRealHyperbolaCellFractionalOscillation X m t)
      volume (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
    apply (IntervalIntegrable.sum (Finset.Ico a b) hint).congr
    intro t _ht
    simp only [Finset.sum_apply]
  have hzeroNotMem : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) :=
    Set.notMem_uIcc_of_lt (by norm_num) (by positivity)
  have hinvSq : IntervalIntegrable (fun t : ℝ => 1 / t ^ (2 : ℕ))
      volume (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
    simpa [one_div, zpow_neg] using
      (intervalIntegral.intervalIntegrable_zpow
        (a := (1 : ℝ)) (b := (a : ℝ) ^ (5 : ℝ))
        (n := (-2 : ℤ)) (Or.inr hzeroNotMem))
  have hmajorInt := hinvSq.const_mul (2 / Real.log (a : ℝ))
  have hpoint : ∀ t ∈ Set.Icc (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)),
      (∑ m ∈ Finset.Ico a b,
          roughSaiasFullyRealHyperbolaCellFractionalOscillation X m t) ≤
        (2 / Real.log (a : ℝ)) * (1 / t ^ (2 : ℕ)) := by
    intro t ht
    have htpos : 0 < t := zero_lt_one.trans_le ht.1
    have htSqPos : 0 < t ^ (2 : ℕ) := pow_pos htpos 2
    have hfactorNonneg : 0 ≤ Int.fract t / t ^ (2 : ℕ) :=
      div_nonneg (Int.fract_nonneg t) htSqPos.le
    have hfactorLe : Int.fract t / t ^ (2 : ℕ) ≤ 1 / t ^ (2 : ℕ) :=
      div_le_div_of_nonneg_right (Int.fract_lt_one t).le htSqPos.le
    have hosc :=
      sum_roughSaiasFullyRealHyperbolaCellKernelOscillation_le_two_inv_log
        hX ha2 hab hbX ht.1 hu5
    calc
      (∑ m ∈ Finset.Ico a b,
          roughSaiasFullyRealHyperbolaCellFractionalOscillation X m t) =
        (Int.fract t / t ^ (2 : ℕ)) *
          ∑ m ∈ Finset.Ico a b,
            roughSaiasFullyRealHyperbolaCellKernelOscillation X m t := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro m _hm
              rfl
      _ ≤ (Int.fract t / t ^ (2 : ℕ)) *
          (2 / Real.log (a : ℝ)) :=
        mul_le_mul_of_nonneg_left hosc hfactorNonneg
      _ ≤ (1 / t ^ (2 : ℕ)) * (2 / Real.log (a : ℝ)) :=
        mul_le_mul_of_nonneg_right hfactorLe (by positivity)
      _ = (2 / Real.log (a : ℝ)) * (1 / t ^ (2 : ℕ)) := by ring
  have hmono := intervalIntegral.integral_mono_on
    haCapOne hsumInt hmajorInt hpoint
  have hsumIntegral :
      (∑ m ∈ Finset.Ico a b,
          roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m) =
        ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
          ∑ m ∈ Finset.Ico a b,
            roughSaiasFullyRealHyperbolaCellFractionalOscillation X m t := by
    unfold roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger
    symm
    exact intervalIntegral.integral_finset_sum hint
  have hinvSqIntegral :
      (∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ), 1 / t ^ (2 : ℕ)) =
        1 - 1 / ((a : ℝ) ^ (5 : ℝ)) := by
    exact roughSaias_integral_one_div_sq_eq haCapOne
  rw [hsumIntegral]
  calc
    (∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
        ∑ m ∈ Finset.Ico a b,
          roughSaiasFullyRealHyperbolaCellFractionalOscillation X m t) ≤
      ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
        (2 / Real.log (a : ℝ)) * (1 / t ^ (2 : ℕ)) := hmono
    _ = (2 / Real.log (a : ℝ)) *
        (1 - 1 / ((a : ℝ) ^ (5 : ℝ))) := by
      rw [intervalIntegral.integral_const_mul, hinvSqIntegral]
    _ ≤ (2 / Real.log (a : ℝ)) * 1 := by
      apply mul_le_mul_of_nonneg_left _
        (div_nonneg (by norm_num) hloga.le)
      have hpowPos : 0 < (a : ℝ) ^ (5 : ℝ) := by positivity
      have hinvPow : 0 ≤ 1 / ((a : ℝ) ^ (5 : ℝ)) :=
        div_nonneg zero_le_one hpowPos.le
      linarith
    _ = 2 / Real.log (a : ℝ) := by ring













end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_034 := by
  exact @Erdos390.WholePaper.sum_roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger_le_two_inv_log
