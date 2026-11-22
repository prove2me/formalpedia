-- Prove2me | solution 1 for Erdos390.WholePaper.roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_le_two_inv_log_of_cutoff_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:51:28.224398+00:00
-- url     : https://prove2.me/submissions/4e81502c-ada4-4f9f-bd7b-082c3ed130c5

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



/-- Throughout the effective support `t ≤ q/m`, the transformed coordinate
lies on the non-initial Dickman faces (`u ≥ 1`). -/
theorem one_le_roughSaiasBaseFreeDickmanCoordinate_of_le_div
    {q m : ℕ} (hm2 : 2 ≤ m) {t : ℝ}
    (htpos : 0 < t) (ht : t ≤ (q : ℝ) / (m : ℝ)) :
    1 ≤ roughSaiasBaseFreeDickmanCoordinate q m t := by
  have hmpos : 0 < (m : ℝ) := by
    positivity
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have htmq : t * (m : ℝ) ≤ (q : ℝ) :=
    (le_div_iff₀ hmpos).mp ht
  have hlogProduct :
      Real.log t + Real.log (m : ℝ) ≤ Real.log (q : ℝ) := by
    have h := Real.log_le_log (mul_pos htpos hmpos) htmq
    rwa [Real.log_mul htpos.ne' hmpos.ne'] at h
  rw [roughSaiasBaseFreeDickmanCoordinate_eq_sub_div,
    one_le_div (Real.log_pos hmone)]
  linarith



































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



/-- On an active face, `u_m(t) * log m = log q - log t` cancels the
base logarithm in the scaled Dickman kernel. -/
theorem roughSaiasScaledDickmanKernel_eq_neg_rho_div_log_sub
    {q m : ℕ} (hm2 : 2 ≤ m) {t : ℝ}
    (hu1 : 1 ≤ roughSaiasBaseFreeDickmanCoordinate q m t) :
    roughSaiasScaledDickmanKernel q m t =
      -rho (roughSaiasBaseFreeDickmanCoordinate q m t - 1) /
        (Real.log (q : ℝ) - Real.log t) := by
  have hlogm : Real.log (m : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < m by omega)))
  have hcoordinate :
      roughSaiasBaseFreeDickmanCoordinate q m t *
          Real.log (m : ℝ) =
        Real.log (q : ℝ) - Real.log t := by
    rw [roughSaiasBaseFreeDickmanCoordinate_eq_sub_div]
    exact div_mul_cancel₀ _ hlogm
  unfold roughSaiasScaledDickmanKernel
  rw [roughSaiasDickmanDerivative_of_one_le hu1, div_div, hcoordinate]

/-- Uniform envelope for the scaled kernel on the five constructed faces. -/
theorem roughSaiasScaledDickmanKernel_abs_le_inv_log
    {q m : ℕ} (hm2 : 2 ≤ m) {t : ℝ}
    (hu5 : roughSaiasBaseFreeDickmanCoordinate q m t ≤ 5) :
    |roughSaiasScaledDickmanKernel q m t| ≤
      1 / Real.log (m : ℝ) := by
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  unfold roughSaiasScaledDickmanKernel
  rw [abs_div, abs_of_pos hlogm]
  exact div_le_div_of_nonneg_right
    (roughSaiasDickmanDerivative_abs_le_one hu5) hlogm.le

/-- The scaled kernel is nonpositive on an active constructed face. -/
theorem roughSaiasScaledDickmanKernel_nonpos_of_active
    {q m : ℕ} (hm2 : 2 ≤ m) {t : ℝ}
    (hu1 : 1 ≤ roughSaiasBaseFreeDickmanCoordinate q m t)
    (hu5 : roughSaiasBaseFreeDickmanCoordinate q m t ≤ 5) :
    roughSaiasScaledDickmanKernel q m t ≤ 0 := by
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hrho :
      0 ≤ rho (roughSaiasBaseFreeDickmanCoordinate q m t - 1) :=
    (rho_pos_on_zero_five (by linarith) (by linarith)).le
  unfold roughSaiasScaledDickmanKernel
  rw [roughSaiasDickmanDerivative_of_one_le hu1]
  exact div_nonpos_of_nonpos_of_nonneg
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hrho)
      (by linarith)) hlogm.le



/-- On an active face, decreasing the quotient while holding the base fixed
makes the scaled kernel more negative.  This is the quotient-direction
counterpart of `roughSaiasScaledDickmanKernel_succ_le_of_active`. -/
theorem roughSaiasScaledDickmanKernel_le_of_quotient_le_of_active
    {q₁ q₀ m : ℕ} (hq₁ : 1 ≤ q₁) (hq : q₁ ≤ q₀) (hm2 : 2 ≤ m)
    {t : ℝ} (htpos : 0 < t)
    (htactive : t ≤ (q₁ : ℝ) / (m : ℝ))
    (hu₀5 : roughSaiasBaseFreeDickmanCoordinate q₀ m t ≤ 5) :
    roughSaiasScaledDickmanKernel q₁ m t ≤
      roughSaiasScaledDickmanKernel q₀ m t := by
  have hmpos : 0 < (m : ℝ) := by positivity
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have hq₁pos : 0 < (q₁ : ℝ) := by
    exact_mod_cast (show 0 < q₁ by omega)
  have hq₀pos : 0 < (q₀ : ℝ) := by
    exact_mod_cast (show 0 < q₀ by omega)
  have htq₁ : t ≤ (q₁ : ℝ) :=
    htactive.trans (div_le_self hq₁pos.le
      (by exact_mod_cast (show 1 ≤ m by omega)))
  have htq₀ : t ≤ (q₀ : ℝ) :=
    htq₁.trans (by exact_mod_cast hq)
  have hactive₀ : t ≤ (q₀ : ℝ) / (m : ℝ) := by
    exact htactive.trans
      (div_le_div_of_nonneg_right (by exact_mod_cast hq) hmpos.le)
  have hu₁1 : 1 ≤ roughSaiasBaseFreeDickmanCoordinate q₁ m t :=
    one_le_roughSaiasBaseFreeDickmanCoordinate_of_le_div
      hm2 htpos htactive
  have hu₀1 : 1 ≤ roughSaiasBaseFreeDickmanCoordinate q₀ m t :=
    one_le_roughSaiasBaseFreeDickmanCoordinate_of_le_div
      hm2 htpos hactive₀
  have hcoord : roughSaiasBaseFreeDickmanCoordinate q₁ m t ≤
      roughSaiasBaseFreeDickmanCoordinate q₀ m t := by
    have hlogq : Real.log (q₁ : ℝ) ≤ Real.log (q₀ : ℝ) :=
      Real.log_le_log hq₁pos (by exact_mod_cast hq)
    have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos hmone
    rw [roughSaiasBaseFreeDickmanCoordinate_eq_sub_div,
      roughSaiasBaseFreeDickmanCoordinate_eq_sub_div]
    exact div_le_div_of_nonneg_right
      (sub_le_sub_right hlogq (Real.log t)) hlogm.le
  have hu₁5 : roughSaiasBaseFreeDickmanCoordinate q₁ m t ≤ 5 :=
    hcoord.trans hu₀5
  have hrho :
      rho (roughSaiasBaseFreeDickmanCoordinate q₀ m t - 1) ≤
        rho (roughSaiasBaseFreeDickmanCoordinate q₁ m t - 1) := by
    exact roughRho_antitoneOn_zero_five
      (show roughSaiasBaseFreeDickmanCoordinate q₁ m t - 1 ∈
          Icc (0 : ℝ) 5 by constructor <;> linarith)
      (show roughSaiasBaseFreeDickmanCoordinate q₀ m t - 1 ∈
          Icc (0 : ℝ) 5 by constructor <;> linarith)
      (by linarith)
  have htq₁lt : t < (q₁ : ℝ) := by
    exact htactive.trans_lt (div_lt_self hq₁pos hmone)
  have hdenom₁ : 0 < Real.log (q₁ : ℝ) - Real.log t := by
    exact sub_pos.mpr (Real.strictMonoOn_log htpos hq₁pos htq₁lt)
  have hdenom₀ : 0 < Real.log (q₀ : ℝ) - Real.log t := by
    exact sub_pos.mpr
      (Real.strictMonoOn_log htpos hq₀pos (htq₁lt.trans_le
        (by exact_mod_cast hq)))
  have hdenomLe : Real.log (q₁ : ℝ) - Real.log t ≤
      Real.log (q₀ : ℝ) - Real.log t := by
    exact sub_le_sub_right (Real.log_le_log hq₁pos
      (by exact_mod_cast hq)) _
  have hrhoNonneg :
      0 ≤ rho (roughSaiasBaseFreeDickmanCoordinate q₁ m t - 1) :=
    (rho_pos_on_zero_five (by linarith) (by linarith)).le
  rw [roughSaiasScaledDickmanKernel_eq_neg_rho_div_log_sub hm2 hu₁1,
    roughSaiasScaledDickmanKernel_eq_neg_rho_div_log_sub hm2 hu₀1]
  rw [neg_div, neg_div]
  apply neg_le_neg
  calc
    rho (roughSaiasBaseFreeDickmanCoordinate q₀ m t - 1) /
          (Real.log (q₀ : ℝ) - Real.log t) ≤
        rho (roughSaiasBaseFreeDickmanCoordinate q₁ m t - 1) /
          (Real.log (q₀ : ℝ) - Real.log t) :=
      div_le_div_of_nonneg_right hrho hdenom₀.le
    _ ≤ rho (roughSaiasBaseFreeDickmanCoordinate q₁ m t - 1) /
          (Real.log (q₁ : ℝ) - Real.log t) :=
      div_le_div_of_nonneg_left hrhoNonneg hdenom₁ hdenomLe

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

/-- Consecutive scaled kernels are antitone as long as the next base is
still active.  The proof uses the common-denominator identity above, so the
coordinate change and the `1 / log m` change are not estimated separately. -/
theorem roughSaiasScaledDickmanKernel_succ_le_of_active
    {q m : ℕ} (hq1 : 1 ≤ q) (hm2 : 2 ≤ m) {t : ℝ}
    (htpos : 0 < t)
    (htactive : t ≤ (q : ℝ) / ((m + 1 : ℕ) : ℝ))
    (hum5 : roughSaiasBaseFreeDickmanCoordinate q m t ≤ 5) :
    roughSaiasScaledDickmanKernel q (m + 1) t ≤
      roughSaiasScaledDickmanKernel q m t := by
  have hdivMono :
      (q : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ (q : ℝ) / (m : ℝ) := by
    exact div_le_div_of_nonneg_left (by positivity)
      (by exact_mod_cast (show 0 < m by omega))
      (by exact_mod_cast (show m ≤ m + 1 by omega))
  have htactiveNow : t ≤ (q : ℝ) / (m : ℝ) :=
    htactive.trans hdivMono
  have htq : t ≤ (q : ℝ) := by
    exact htactive.trans
      (div_le_self (by positivity)
        (by exact_mod_cast (show 1 ≤ m + 1 by omega)))
  have huNow1 :
      1 ≤ roughSaiasBaseFreeDickmanCoordinate q m t :=
    one_le_roughSaiasBaseFreeDickmanCoordinate_of_le_div
      hm2 htpos htactiveNow
  have huNext1 :
      1 ≤ roughSaiasBaseFreeDickmanCoordinate q (m + 1) t :=
    one_le_roughSaiasBaseFreeDickmanCoordinate_of_le_div
      (by omega) htpos htactive
  have huNextNow :
      roughSaiasBaseFreeDickmanCoordinate q (m + 1) t ≤
        roughSaiasBaseFreeDickmanCoordinate q m t :=
    roughSaiasBaseFreeDickmanCoordinate_succ_le hm2 htpos htq
  have huNext5 :
      roughSaiasBaseFreeDickmanCoordinate q (m + 1) t ≤ 5 :=
    huNextNow.trans hum5
  have hrho :
      rho (roughSaiasBaseFreeDickmanCoordinate q m t - 1) ≤
        rho (roughSaiasBaseFreeDickmanCoordinate q (m + 1) t - 1) := by
    exact roughRho_antitoneOn_zero_five
      (show roughSaiasBaseFreeDickmanCoordinate q (m + 1) t - 1 ∈
          Icc (0 : ℝ) 5 by constructor <;> linarith)
      (show roughSaiasBaseFreeDickmanCoordinate q m t - 1 ∈
          Icc (0 : ℝ) 5 by constructor <;> linarith)
      (by linarith)
  have hlogNext : Real.log (((m + 1 : ℕ) : ℝ)) ≠ 0 :=
    ne_of_gt (Real.log_pos
      (by exact_mod_cast (show 1 < m + 1 by omega)))
  have hcoordinateNext :
      roughSaiasBaseFreeDickmanCoordinate q (m + 1) t *
          Real.log (((m + 1 : ℕ) : ℝ)) =
        Real.log (q : ℝ) - Real.log t := by
    rw [roughSaiasBaseFreeDickmanCoordinate_eq_sub_div]
    exact div_mul_cancel₀ _ hlogNext
  have hdenom : 0 < Real.log (q : ℝ) - Real.log t := by
    rw [← hcoordinateNext]
    exact mul_pos (lt_of_lt_of_le zero_lt_one huNext1)
      (Real.log_pos (by exact_mod_cast (show 1 < m + 1 by omega)))
  rw [roughSaiasScaledDickmanKernel_eq_neg_rho_div_log_sub
      (m := m + 1) (by omega) huNext1,
    roughSaiasScaledDickmanKernel_eq_neg_rho_div_log_sub
      (m := m) hm2 huNow1]
  exact div_le_div_of_nonneg_right (neg_le_neg hrho) hdenom.le

/-- Consecutive monotonicity along the natural hyperbola path
`m ↦ (X/m,m)`.  Both the quotient decrease and the base increase reinforce
the same signed kernel variation while the next point remains active. -/
theorem roughSaiasScaledDickmanKernel_hyperbola_succ_le_of_active
    {X m : ℕ} (hm2 : 2 ≤ m) (hnextX : m + 1 ≤ X)
    {t : ℝ} (htpos : 0 < t)
    (htactive : t ≤ ((X / (m + 1) : ℕ) : ℝ) /
      ((m + 1 : ℕ) : ℝ))
    (hum5 : roughSaiasBaseFreeDickmanCoordinate (X / m) m t ≤ 5) :
    roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t ≤
      roughSaiasScaledDickmanKernel (X / m) m t := by
  have hmPos : 0 < m := by omega
  have hnextPos : 0 < m + 1 := by omega
  have hqNext : 1 ≤ X / (m + 1) :=
    Nat.div_pos hnextX hnextPos
  have hqLe : X / (m + 1) ≤ X / m :=
    Nat.div_le_div_left (a := X) (Nat.le_succ m) hmPos
  have hdiv : ((X / (m + 1) : ℕ) : ℝ) /
        ((m + 1 : ℕ) : ℝ) ≤
      ((X / (m + 1) : ℕ) : ℝ) / (m : ℝ) := by
    exact div_le_div_of_nonneg_left (by positivity)
      (by exact_mod_cast hmPos) (by exact_mod_cast (Nat.le_succ m))
  have htactiveNow : t ≤ ((X / (m + 1) : ℕ) : ℝ) / (m : ℝ) :=
    htactive.trans hdiv
  have hfaceNextNow :
      roughSaiasBaseFreeDickmanCoordinate (X / (m + 1)) m t ≤ 5 := by
    have hcoord :
        roughSaiasBaseFreeDickmanCoordinate (X / (m + 1)) m t ≤
          roughSaiasBaseFreeDickmanCoordinate (X / m) m t := by
      have hqNextPosR : 0 < ((X / (m + 1) : ℕ) : ℝ) := by positivity
      have hlogq : Real.log ((X / (m + 1) : ℕ) : ℝ) ≤
          Real.log ((X / m : ℕ) : ℝ) :=
        Real.log_le_log hqNextPosR (by exact_mod_cast hqLe)
      have hlogm : 0 < Real.log (m : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < m by omega))
      rw [roughSaiasBaseFreeDickmanCoordinate_eq_sub_div,
        roughSaiasBaseFreeDickmanCoordinate_eq_sub_div]
      exact div_le_div_of_nonneg_right
        (sub_le_sub_right hlogq (Real.log t)) hlogm.le
    exact hcoord.trans hum5
  calc
    roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t ≤
        roughSaiasScaledDickmanKernel (X / (m + 1)) m t :=
      roughSaiasScaledDickmanKernel_succ_le_of_active
        hqNext hm2 htpos htactive hfaceNextNow
    _ ≤ roughSaiasScaledDickmanKernel (X / m) m t :=
      roughSaiasScaledDickmanKernel_le_of_quotient_le_of_active
        hqNext hqLe hm2 htpos htactiveNow hum5







/-- Exact telescoping of the absolute scaled-kernel variation along the
natural hyperbola path `m ↦ (X / m,m)` on an all-active block. -/
theorem roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_eq
    {X a b : ℕ} (ha2 : 2 ≤ a) (hab : a ≤ b) (hbX : b ≤ X)
    {t : ℝ} (htpos : 0 < t)
    (hactive : ∀ m ∈ Finset.Icc a b,
      t ≤ ((X / m : ℕ) : ℝ) / (m : ℝ))
    (hface : ∀ m ∈ Finset.Icc a b,
      roughSaiasBaseFreeDickmanCoordinate (X / m) m t ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
          roughSaiasScaledDickmanKernel (X / m) m t|) =
      roughSaiasScaledDickmanKernel (X / a) a t -
        roughSaiasScaledDickmanKernel (X / b) b t := by
  have hmono : ∀ m ∈ Finset.Ico a b,
      roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t ≤
        roughSaiasScaledDickmanKernel (X / m) m t := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hmNow : m ∈ Finset.Icc a b := by
      rw [Finset.mem_Icc]
      omega
    have hmNext : m + 1 ∈ Finset.Icc a b := by
      rw [Finset.mem_Icc]
      omega
    exact roughSaiasScaledDickmanKernel_hyperbola_succ_le_of_active
      (by omega) (by omega) htpos
      (hactive (m + 1) hmNext) (hface m hmNow)
  calc
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
          roughSaiasScaledDickmanKernel (X / m) m t|) =
        ∑ m ∈ Finset.Ico a b,
          (roughSaiasScaledDickmanKernel (X / m) m t -
            roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [abs_of_nonpos (sub_nonpos.mpr (hmono m hm))]
      ring
    _ = roughSaiasScaledDickmanKernel (X / a) a t -
        roughSaiasScaledDickmanKernel (X / b) b t := by
      clear hmono hactive hface hbX
      induction b, hab using Nat.le_induction with
      | base => simp
      | succ b hab ih =>
          rw [Finset.sum_Ico_succ_top hab, ih]
          ring

/-- Quantitative all-active variation along the hyperbola path.  Quotient
jumps and base increments have the same sign, so their combined variation
still costs only one inverse logarithm. -/
theorem roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_le_inv_log
    {X a b : ℕ} (ha2 : 2 ≤ a) (hab : a ≤ b) (hbX : b ≤ X)
    {t : ℝ} (htpos : 0 < t)
    (hactive : ∀ m ∈ Finset.Icc a b,
      t ≤ ((X / m : ℕ) : ℝ) / (m : ℝ))
    (hface : ∀ m ∈ Finset.Icc a b,
      roughSaiasBaseFreeDickmanCoordinate (X / m) m t ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
          roughSaiasScaledDickmanKernel (X / m) m t|) ≤
      1 / Real.log (a : ℝ) := by
  have haMem : a ∈ Finset.Icc a b := by
    rw [Finset.mem_Icc]
    exact ⟨le_rfl, hab⟩
  have hbMem : b ∈ Finset.Icc a b := by
    rw [Finset.mem_Icc]
    exact ⟨hab, le_rfl⟩
  have hb2 : 2 ≤ b := ha2.trans hab
  have huA1 :
      1 ≤ roughSaiasBaseFreeDickmanCoordinate (X / a) a t :=
    one_le_roughSaiasBaseFreeDickmanCoordinate_of_le_div
      ha2 htpos (hactive a haMem)
  have huB1 :
      1 ≤ roughSaiasBaseFreeDickmanCoordinate (X / b) b t :=
    one_le_roughSaiasBaseFreeDickmanCoordinate_of_le_div
      hb2 htpos (hactive b hbMem)
  have hA_nonpos : roughSaiasScaledDickmanKernel (X / a) a t ≤ 0 :=
    roughSaiasScaledDickmanKernel_nonpos_of_active
      ha2 huA1 (hface a haMem)
  have hB_nonpos : roughSaiasScaledDickmanKernel (X / b) b t ≤ 0 :=
    roughSaiasScaledDickmanKernel_nonpos_of_active
      hb2 huB1 (hface b hbMem)
  have hBabs : |roughSaiasScaledDickmanKernel (X / b) b t| ≤
      1 / Real.log (b : ℝ) :=
    roughSaiasScaledDickmanKernel_abs_le_inv_log
      hb2 (hface b hbMem)
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hlogab : Real.log (a : ℝ) ≤ Real.log (b : ℝ) :=
    Real.log_le_log
      (by exact_mod_cast (show 0 < a by omega))
      (by exact_mod_cast hab)
  rw [roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_eq
      ha2 hab hbX htpos hactive hface]
  calc
    roughSaiasScaledDickmanKernel (X / a) a t -
        roughSaiasScaledDickmanKernel (X / b) b t ≤
      -roughSaiasScaledDickmanKernel (X / b) b t := by linarith
    _ = |roughSaiasScaledDickmanKernel (X / b) b t| :=
      (abs_of_nonpos hB_nonpos).symm
    _ ≤ 1 / Real.log (b : ℝ) := hBabs
    _ ≤ 1 / Real.log (a : ℝ) :=
      one_div_le_one_div_of_le hloga hlogab

/-- One-cutoff variation along the hyperbola path.  Once
`t > (X / m) / m`, every later kernel is zero; the unique reset costs a
second inverse logarithm. -/
theorem roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_le_two_inv_log_of_cutoff
    {X a c b : ℕ} (ha2 : 2 ≤ a) (hac : a ≤ c) (hcb : c ≤ b)
    (hbX : b ≤ X) {t : ℝ} (htpos : 0 < t)
    (hactive : ∀ m ∈ Finset.Icc a c,
      t ≤ ((X / m : ℕ) : ℝ) / (m : ℝ))
    (hface : ∀ m ∈ Finset.Icc a c,
      roughSaiasBaseFreeDickmanCoordinate (X / m) m t ≤ 5)
    (hinactive : ∀ m ∈ Finset.Ioc c b,
      ((X / m : ℕ) : ℝ) / (m : ℝ) < t) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
          roughSaiasScaledDickmanKernel (X / m) m t|) ≤
      2 / Real.log (a : ℝ) := by
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hactiveBound :
      (∑ m ∈ Finset.Ico a c,
          |roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
            roughSaiasScaledDickmanKernel (X / m) m t|) ≤
        1 / Real.log (a : ℝ) :=
    roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_le_inv_log
      ha2 hac (hcb.trans hbX) htpos hactive hface
  rcases hcb.eq_or_lt with rfl | hcbLt
  · exact hactiveBound.trans (by
      have hinv : 0 ≤ 1 / Real.log (a : ℝ) := by positivity
      calc
        1 / Real.log (a : ℝ) ≤
            2 * (1 / Real.log (a : ℝ)) := by linarith
        _ = 2 / Real.log (a : ℝ) := by ring)
  · have hc2 : 2 ≤ c := ha2.trans hac
    have hcMem : c ∈ Finset.Icc a c := by
      rw [Finset.mem_Icc]
      exact ⟨hac, le_rfl⟩
    have hcNextMem : c + 1 ∈ Finset.Ioc c b := by
      rw [Finset.mem_Ioc]
      omega
    have hcNextLeX : c + 1 ≤ X := by omega
    have hcNextPos : 0 < c + 1 := by omega
    have hqNext : 1 ≤ X / (c + 1) :=
      Nat.div_pos hcNextLeX hcNextPos
    have hcNextZero :
        roughSaiasScaledDickmanKernel (X / (c + 1)) (c + 1) t = 0 :=
      roughSaiasScaledDickmanKernel_eq_zero_of_div_lt
        hqNext (by omega) (hinactive (c + 1) hcNextMem)
    have htailZero :
        (∑ m ∈ Finset.Ico (c + 1) b,
          |roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
            roughSaiasScaledDickmanKernel (X / m) m t|) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      rw [Finset.mem_Ico] at hm
      have hmMem : m ∈ Finset.Ioc c b := by
        rw [Finset.mem_Ioc]
        omega
      have hmNextMem : m + 1 ∈ Finset.Ioc c b := by
        rw [Finset.mem_Ioc]
        omega
      have hqm : 1 ≤ X / m :=
        Nat.div_pos (by omega) (by omega)
      have hqmNext : 1 ≤ X / (m + 1) :=
        Nat.div_pos (by omega) (by omega)
      have hmZero : roughSaiasScaledDickmanKernel (X / m) m t = 0 :=
        roughSaiasScaledDickmanKernel_eq_zero_of_div_lt
          hqm (by omega) (hinactive m hmMem)
      have hmNextZero :
          roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t = 0 :=
        roughSaiasScaledDickmanKernel_eq_zero_of_div_lt
          hqmNext (by omega) (hinactive (m + 1) hmNextMem)
      rw [hmZero, hmNextZero, sub_self, abs_zero]
    have htail :
        (∑ m ∈ Finset.Ico c b,
          |roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
            roughSaiasScaledDickmanKernel (X / m) m t|) =
          |roughSaiasScaledDickmanKernel (X / c) c t| := by
      rw [Finset.sum_eq_sum_Ico_succ_bot hcbLt, hcNextZero,
        zero_sub, abs_neg, htailZero, add_zero]
    have hcAbs : |roughSaiasScaledDickmanKernel (X / c) c t| ≤
        1 / Real.log (c : ℝ) :=
      roughSaiasScaledDickmanKernel_abs_le_inv_log
        hc2 (hface c hcMem)
    have hlogac : Real.log (a : ℝ) ≤ Real.log (c : ℝ) :=
      Real.log_le_log
        (by exact_mod_cast (show 0 < a by omega))
        (by exact_mod_cast hac)
    have hcAbs' : |roughSaiasScaledDickmanKernel (X / c) c t| ≤
        1 / Real.log (a : ℝ) :=
      hcAbs.trans (one_div_le_one_div_of_le hloga hlogac)
    rw [← Finset.sum_Ico_consecutive _ hac hcb, htail]
    calc
      (∑ m ∈ Finset.Ico a c,
          |roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
            roughSaiasScaledDickmanKernel (X / m) m t|) +
          |roughSaiasScaledDickmanKernel (X / c) c t| ≤
        1 / Real.log (a : ℝ) + 1 / Real.log (a : ℝ) :=
          add_le_add hactiveBound hcAbs'
      _ = 2 / Real.log (a : ℝ) := by ring



















/-! ## The genuinely real hyperbola path inside natural cells -/



























































end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_032 := by
  exact @Erdos390.WholePaper.roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_le_two_inv_log_of_cutoff
