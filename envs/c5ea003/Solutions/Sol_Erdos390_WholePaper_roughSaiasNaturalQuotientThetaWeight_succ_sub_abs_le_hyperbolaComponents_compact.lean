-- Prove2me | solution 1 for Erdos390.WholePaper.roughSaiasNaturalQuotientThetaWeight_succ_sub_abs_le_hyperbolaComponents_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:48:52.438661+00:00
-- url     : https://prove2.me/submissions/401c9e12-b6a7-42d7-95bc-b2b40656f9ad

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
import Definitions.Def_erdos390_analytic_foundations_009
import Theorems.Thm_Erdos390_WholePaper_roughCompactBV_translation_le_of_le_compact


section
theorem Erdos390.WholePaper.roughCompactBV_translation_le_of_le : Erdos390.RemainingAnalyticGoal008_019 := @Erdos390.WholePaper.roughCompactBV_translation_le_of_le_compact
end
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





/-! ## The explicit `1 / log y` normalization correction -/











/-! ## Exact connection to the genuine friable residual -/























end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughCompactBVTranslation -/
section


/-!
# The compact bounded-variation translation estimate

This file closes the pure real-analysis premise isolated in
`RoughSaiasNormalization.lean`.  If `f` has total variation at most `2` on
`[-5,5]`, then translating `f` by two parameters in `[0,5]` changes its
`L¹([0,5])` norm by at most twice the distance between the parameters.

The proof uses the cumulative signed variation

`V(x) = variationOnFromTo f [-5,5] (-5) x`.

Both `V` and `V-f` are monotone on the compact interval, so all functions
that occur below are interval integrable.  For `a <= b`, pointwise variation
gives

`|f(a-v)-f(b-v)| <= V(b-v)-V(a-v)`.

After translating the two integrals, additivity on adjacent intervals leaves
one interval of length `b-a` at each endpoint.  Monotonicity bounds their
difference by `(b-a) * (V(5)-V(-5))`, which is at most `2*(b-a)`.
-/

open scoped ENNReal Interval

namespace Erdos390.WholePaper

open Set MeasureTheory

noncomputable section



/-- The compact BV translation premise from `RoughSaiasNormalization` is a
theorem, with exactly the constant and ranges used there. -/
theorem roughCompactBVTranslationPrinciple :
    RoughCompactBVTranslationPrinciple := by
  intro f hfvar a b ha hb
  rcases le_total a b with hab | hba
  · calc
      (∫ v in (0 : ℝ)..5, |f (a - v) - f (b - v)|) ≤
          2 * (b - a) :=
        roughCompactBV_translation_le_of_le hfvar ha hb hab
      _ = 2 * |a - b| := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)]
  · calc
      (∫ v in (0 : ℝ)..5, |f (a - v) - f (b - v)|) =
          ∫ v in (0 : ℝ)..5, |f (b - v) - f (a - v)| := by
        apply intervalIntegral.integral_congr
        intro v _hv
        change |f (a - v) - f (b - v)| = |f (b - v) - f (a - v)|
        exact abs_sub_comm _ _
      _ ≤ 2 * (a - b) :=
        roughCompactBV_translation_le_of_le hfvar hb ha hba
      _ = 2 * |a - b| := by
        rw [abs_of_nonneg (sub_nonneg.mpr hba)]

/-! ## Unconditional forms of the normalization estimates -/

theorem roughSaiasDickmanDerivative_translation_le_two_unconditional
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 5)
    (hb : b ∈ Icc (0 : ℝ) 5) :
    (∫ v in (0 : ℝ)..5,
      |roughSaiasDickmanDerivative (a - v) -
        roughSaiasDickmanDerivative (b - v)|) ≤
      2 * |a - b| :=
  roughSaiasDickmanDerivative_translation_le_two
    roughCompactBVTranslationPrinciple ha hb







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



/-- Exact change of variables in the signed Saias correction integral.
Unlike the usual continuous substitution lemma, this proof does not require
continuity of `fract`: monotonicity of `v ↦ m^v` is sufficient. -/
theorem roughSaiasFractionalIntegral_eq_baseFree
    {q m : ℕ} (hm2 : 2 ≤ m) :
    (∫ v in (0 : ℝ)..5,
        roughSaiasDickmanDerivative
            (Real.log (q : ℝ) / Real.log (m : ℝ) - v) *
          roughSaiasFractionalWeight m v) =
      roughSaiasBaseFreeFractionalIntegral q m := by
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
  have hchange :
      (∫ t in f '' Icc (0 : ℝ) 5,
          roughSaiasBaseFreeFractionalKernel q m t) =
        ∫ v in Icc (0 : ℝ) 5,
          f' v • roughSaiasBaseFreeFractionalKernel q m (f v) :=
    MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn
      measurableSet_Icc hfderiv hfmono
        (roughSaiasBaseFreeFractionalKernel q m)
  have hpoint (v : ℝ) :
      f' v • roughSaiasBaseFreeFractionalKernel q m (f v) =
        roughSaiasDickmanDerivative
            (Real.log (q : ℝ) / Real.log (m : ℝ) - v) *
          roughSaiasFractionalWeight m v := by
    simpa [f, f', smul_eq_mul] using
      roughSaiasBaseFreeFractionalKernel_rpow_mul_jacobian
        (q := q) hm2 v
  have hu : (1 : ℝ) ≤ (m : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ m by omega)) (by norm_num)
  unfold roughSaiasBaseFreeFractionalIntegral
  calc
    (∫ v in (0 : ℝ)..5,
        roughSaiasDickmanDerivative
            (Real.log (q : ℝ) / Real.log (m : ℝ) - v) *
          roughSaiasFractionalWeight m v) =
        ∫ v in Icc (0 : ℝ) 5,
          roughSaiasDickmanDerivative
              (Real.log (q : ℝ) / Real.log (m : ℝ) - v) *
            roughSaiasFractionalWeight m v := by
      rw [intervalIntegral.integral_of_le (by norm_num),
        MeasureTheory.integral_Icc_eq_integral_Ioc]
    _ = ∫ v in Icc (0 : ℝ) 5,
          f' v • roughSaiasBaseFreeFractionalKernel q m (f v) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro v _hv
      exact (hpoint v).symm
    _ = ∫ t in Icc (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)),
          roughSaiasBaseFreeFractionalKernel q m t := by
      rw [← hfimage]
      exact hchange.symm
    _ = ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q m t := by
      rw [intervalIntegral.integral_of_le hu,
        MeasureTheory.integral_Icc_eq_integral_Ioc]











/-- At a natural quotient, `G_m` is exactly `rho` minus the transformed
base-free-sawtooth integral. -/
theorem roughSaiasG_at_natQuotient_eq_baseFree
    {q m : ℕ} (hm2 : 2 ≤ m) :
    roughSaiasG m
        (Real.log (q : ℝ) / Real.log (m : ℝ)) =
      rho (Real.log (q : ℝ) / Real.log (m : ℝ)) -
        roughSaiasBaseFreeFractionalIntegral q m := by
  unfold roughSaiasG
  rw [roughSaiasFractionalIntegral_eq_baseFree hm2]



/-! ## Exact floor/base pairing in the transformed coordinate -/

/-- Natural main term at a fixed quotient, written with the base-free
sawtooth integral. -/
theorem roughSaiasNaturalMain_eq_rho_sub_baseFree
    {q m : ℕ} (hm2 : 2 ≤ m) :
    roughSaiasNaturalMain q m =
      (q : ℝ) *
        (rho (Real.log (q : ℝ) / Real.log (m : ℝ)) -
          roughSaiasBaseFreeFractionalIntegral q m) := by
  unfold roughSaiasNaturalMain FriableAsymptotic.dickmanU
  rw [roughSaiasG_at_natQuotient_eq_baseFree hm2]



/-- Exact identification of the floor/frac-paired natural weight with the
base-free-sawtooth representation. -/
theorem roughSaiasNaturalQuotientThetaWeight_eq_baseFree
    {X m : ℕ} (hm2 : 2 ≤ m) :
    roughSaiasNaturalQuotientThetaWeight X m =
      roughSaiasBaseFreeNaturalThetaWeight (X / m) m := by
  unfold roughSaiasNaturalQuotientThetaWeight
    roughSaiasBaseFreeNaturalThetaWeight
  rw [roughSaiasNaturalMain_eq_rho_sub_baseFree hm2]

/-- Exact consecutive-base variation with quotient jumps retained.  On a
block where `X/(m+1)=X/m`, both terms use the same quotient and the same
base-free sawtooth variable `t`. -/
theorem roughSaiasNaturalQuotientThetaWeight_diff_eq_baseFree
    {X m : ℕ} (hm2 : 2 ≤ m) :
    roughSaiasNaturalQuotientThetaWeight X (m + 1) -
        roughSaiasNaturalQuotientThetaWeight X m =
      roughSaiasBaseFreeNaturalThetaWeight (X / (m + 1)) (m + 1) -
        roughSaiasBaseFreeNaturalThetaWeight (X / m) m := by
  rw [roughSaiasNaturalQuotientThetaWeight_eq_baseFree (by omega),
    roughSaiasNaturalQuotientThetaWeight_eq_baseFree hm2]



/-! ## The signed center as a base-free quotient-block sum -/







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















/-- The fully real normalizer is exactly one on its initial Dickman face. -/
theorem roughSaiasFullyRealG_eq_one_of_le_one
    {y u : ℝ} (hu : u ≤ 1) :
    roughSaiasFullyRealG y u = 1 := by
  have hzero :
      (∫ v in (0 : ℝ)..5,
        roughSaiasDickmanDerivative (u - v) *
          roughSaiasFullyRealFractionalWeight y v) = 0 := by
    have hcongr :
        (∫ v in (0 : ℝ)..5,
          roughSaiasDickmanDerivative (u - v) *
            roughSaiasFullyRealFractionalWeight y v) =
          ∫ _v in (0 : ℝ)..5, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro v hv
      have hv' : v ∈ Set.Icc (0 : ℝ) 5 := by
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] using hv
      by_cases huv : u - v < 1
      · simp [roughSaiasDickmanDerivative_of_lt_one huv]
      · have huEq : u = 1 := by linarith [hv'.1]
        have hvEq : v = 0 := by linarith [hv'.1]
        subst u
        subst v
        simp [roughSaiasFullyRealFractionalWeight]
    simpa using hcongr
  rw [roughSaiasFullyRealG, hzero, sub_zero, rho_eq_one_of_le_one hu]

/-- The compact `3`-Lipschitz estimate is independent of whether the base
is natural: its proof uses only that the fractional weight lies in `[0,1]`.
-/
theorem roughSaiasFullyRealG_lipschitz_three
    {y : ℝ} (hy : 1 < y) {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 5) (hb : b ∈ Set.Icc (0 : ℝ) 5) :
    |roughSaiasFullyRealG y a - roughSaiasFullyRealG y b| ≤
      3 * |a - b| := by
  let Fa : ℝ → ℝ := fun v ↦
    roughSaiasDickmanDerivative (a - v) *
      roughSaiasFullyRealFractionalWeight y v
  let Fb : ℝ → ℝ := fun v ↦
    roughSaiasDickmanDerivative (b - v) *
      roughSaiasFullyRealFractionalWeight y v
  let qa : ℝ → ℝ := fun v ↦ roughSaiasDickmanDerivative (a - v)
  let qb : ℝ → ℝ := fun v ↦ roughSaiasDickmanDerivative (b - v)
  have hFa : IntervalIntegrable Fa volume 0 5 := by
    simpa only [Fa] using
      roughSaiasFullyRealIntegrand_intervalIntegrable hy ha.2
  have hFb : IntervalIntegrable Fb volume 0 5 := by
    simpa only [Fb] using
      roughSaiasFullyRealIntegrand_intervalIntegrable hy hb.2
  have hqa : IntervalIntegrable qa volume 0 5 := by
    simpa only [qa] using
      roughSaiasDickmanDerivative_translate_intervalIntegrable ha.2
  have hqb : IntervalIntegrable qb volume 0 5 := by
    simpa only [qb] using
      roughSaiasDickmanDerivative_translate_intervalIntegrable hb.2
  have hdiff :
      (∫ v in (0 : ℝ)..5, Fa v) - ∫ v in (0 : ℝ)..5, Fb v =
        ∫ v in (0 : ℝ)..5, Fa v - Fb v :=
    (intervalIntegral.integral_sub hFa hFb).symm
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
        have hweight := roughSaiasFullyRealFractionalWeight_mem_unitInterval
          hy.le hv.1
        change
          |qa v * roughSaiasFullyRealFractionalWeight y v -
              qb v * roughSaiasFullyRealFractionalWeight y v| ≤
            |qa v - qb v|
        rw [← sub_mul, abs_mul, abs_of_nonneg hweight.1]
        exact mul_le_of_le_one_right (abs_nonneg (qa v - qb v)) hweight.2
  have htranslate :
      (∫ v in (0 : ℝ)..5, |qa v - qb v|) ≤ 2 * |a - b| := by
    simpa only [qa, qb] using
      roughSaiasDickmanDerivative_translation_le_two_unconditional ha hb
  have hrho : |rho a - rho b| ≤ |a - b| :=
    roughRho_abs_sub_le_abs_of_le_five ha.2 hb.2
  change
    |(rho a - ∫ v in (0 : ℝ)..5, Fa v) -
      (rho b - ∫ v in (0 : ℝ)..5, Fb v)| ≤ 3 * |a - b|
  calc
    _ = |(rho a - rho b) -
        ((∫ v in (0 : ℝ)..5, Fa v) -
          ∫ v in (0 : ℝ)..5, Fb v)| := by
      congr 1
      ring
    _ ≤ |rho a - rho b| +
        |(∫ v in (0 : ℝ)..5, Fa v) -
          ∫ v in (0 : ℝ)..5, Fb v| := abs_sub _ _
    _ ≤ |a - b| + ∫ v in (0 : ℝ)..5, |qa v - qb v| :=
      add_le_add hrho hintegral
    _ ≤ |a - b| + 2 * |a - b| := add_le_add le_rfl htranslate
    _ = 3 * |a - b| := by ring

theorem roughSaiasFullyRealG_abs_le_sixteen
    {y u : ℝ} (hy : 1 < y) (hu : u ∈ Set.Icc (0 : ℝ) 5) :
    |roughSaiasFullyRealG y u| ≤ 16 := by
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 5 := by norm_num
  have hlip := roughSaiasFullyRealG_lipschitz_three hy hu hzero
  rw [roughSaiasFullyRealG_eq_one_of_le_one (by norm_num : (0 : ℝ) ≤ 1)]
    at hlip
  calc
    |roughSaiasFullyRealG y u| =
        |(roughSaiasFullyRealG y u - 1) + 1| := by
      congr 1
      ring
    _ ≤ |roughSaiasFullyRealG y u - 1| + |(1 : ℝ)| := abs_add_le _ _
    _ ≤ 3 * |u - 0| + 1 := by
      rw [abs_one]
      exact add_le_add hlip le_rfl
    _ ≤ 3 * 5 + 1 := by
      have huabs : |u - 0| ≤ 5 := by
        rw [sub_zero, abs_of_nonneg hu.1]
        exact hu.2
      gcongr
    _ = 16 := by norm_num











/-! ## Exact Stieltjes identification at a real base -/











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasSelectorLedgerBound -/
section


/-!
# Summing the upper-cell quotient-selector ledger

On cells above the square-root transition the fully real Buchstab
integrand is the elementary quotient selector

`floor (X / s) / log s`.

The cell ledger from `RoughSaiasFullyRealBuchstabCells` has two pieces.
The natural quotient drops telescope exactly, while the reciprocal-log
variation is bounded by the convergent `sum 1 / m^2` tail.  This file makes
that summation quantitative without any asymptotic or defect premise.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section



theorem roughSaiasNaturalQuotientDrop_nonneg
    (X : ℕ) {m : ℕ} (hm : 0 < m) :
    0 ≤ roughSaiasNaturalQuotientDrop X m := by
  unfold roughSaiasNaturalQuotientDrop
  apply sub_nonneg.mpr
  exact_mod_cast Nat.div_le_div_left (a := X) (Nat.le_succ m) hm







theorem roughSaias_invLog_succ_sub_nonneg
    {m : ℕ} (hm2 : 2 ≤ m) :
    0 ≤ 1 / Real.log (m : ℝ) -
      1 / Real.log ((m + 1 : ℕ) : ℝ) := by
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogmono : Real.log (m : ℝ) ≤
      Real.log ((m + 1 : ℕ) : ℝ) :=
    Real.log_le_log
      (by exact_mod_cast (show 0 < m by omega))
      (by exact_mod_cast (Nat.le_succ m))
  exact sub_nonneg.mpr (one_div_le_one_div_of_le hlogm hlogmono)













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



/-- Log-ratio form of five-face propagation along natural hyperbola
quotients. -/
theorem roughSaiasNatHyperbolaLogRatio_le_five
    {X a m : ℕ} (ha2 : 2 ≤ a) (ham : a ≤ m) (hmX : m ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) ≤ 5 := by
  simpa [roughSaiasBaseFreeDickmanCoordinate] using
    (roughSaiasBaseFreeDickmanCoordinate_natHyperbola_le_five
      ha2 ham hmX (t := (1 : ℝ)) (by norm_num) hu5)











/-! ## The genuinely real hyperbola path inside natural cells -/



























































end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasSharpCorrectionTarget -/
section


/-!
# The sharp fully real correction target

The reverse defect splits directly into:

1. the ordinary Dickman continuous-integral versus prime-theta
   discrepancy, already closed by the existing Riemann and fourth-power
   PNT estimates; and
2. one fully real Saias correction integral versus its matching residual
   prime weight.

This is the minimal analytic target left after all exact base changes,
floor pairings, upper-selector cells, and standard Dickman estimates have
been discharged.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section



































/-! ## Closing the lower fully-real quadrature -/



















/-- The selector ledger is exactly the drop of the positive coefficient
`(X / m) / log m`, independently of whether the cell is above or below
the square-root transition. -/
theorem roughSaiasNatHyperbolaCoefficient_sub_succ_eq_selectorCellLedger
    (X m : ℕ) :
    ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) -
        ((X / (m + 1) : ℕ) : ℝ) /
          Real.log ((m + 1 : ℕ) : ℝ) =
      roughSaiasSelectorCellLedger X m := by
  unfold roughSaiasSelectorCellLedger
  ring

/-- Lower-face pointwise variation of the full natural theta weight.  The
coefficient drift is charged to the existing selector ledger, while the
genuinely smooth part is split into rho variation and the common-cap
fractional-integral variation. -/
theorem roughSaiasNaturalQuotientThetaWeight_succ_sub_abs_le_hyperbolaComponents
    {X a b m : ℕ} (ha2 : 2 ≤ a) (_hab : a ≤ b) (hbX : b ≤ X)
    (hm : m ∈ Finset.Ico a b)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
        roughSaiasNaturalQuotientThetaWeight X m| ≤
      16 * roughSaiasSelectorCellLedger X m +
        ((X : ℝ) / ((m : ℝ) * Real.log (m : ℝ))) *
          (|rho (Real.log ((X / (m + 1) : ℕ) : ℝ) /
                  Real.log ((m + 1 : ℕ) : ℝ)) -
              rho (Real.log ((X / m : ℕ) : ℝ) /
                Real.log (m : ℝ))| +
            |roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1) -
              roughSaiasBaseFreeFractionalIntegral (X / m) m|) := by
  have hmData := Finset.mem_Ico.mp hm
  have hm2 : 2 ≤ m := ha2.trans hmData.1
  have hnextX : m + 1 ≤ X := by omega
  have hqNow : 1 ≤ X / m := Nat.div_pos (by omega) (by omega)
  have hqNext : 1 ≤ X / (m + 1) := Nat.div_pos hnextX (by omega)
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogNext : 0 < Real.log ((m + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m + 1 by omega))
  let A₀ : ℝ := ((X / m : ℕ) : ℝ) / Real.log (m : ℝ)
  let A₁ : ℝ := ((X / (m + 1) : ℕ) : ℝ) /
    Real.log ((m + 1 : ℕ) : ℝ)
  let u₀ : ℝ := Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ)
  let u₁ : ℝ := Real.log ((X / (m + 1) : ℕ) : ℝ) /
    Real.log ((m + 1 : ℕ) : ℝ)
  let I₀ : ℝ := roughSaiasBaseFreeFractionalIntegral (X / m) m
  let I₁ : ℝ :=
    roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1)
  have hcoeff : A₀ - A₁ = roughSaiasSelectorCellLedger X m := by
    simpa only [A₀, A₁] using
      roughSaiasNatHyperbolaCoefficient_sub_succ_eq_selectorCellLedger X m
  have hledgerNonneg : 0 ≤ roughSaiasSelectorCellLedger X m := by
    have hdrop :=
      roughSaiasNaturalQuotientDrop_nonneg (m := m) X (by omega)
    unfold roughSaiasSelectorCellLedger
    exact add_nonneg
      (div_nonneg hdrop hlogm.le)
      (mul_nonneg (by positivity) (roughSaias_invLog_succ_sub_nonneg hm2))
  have hA₁A₀ : A₁ ≤ A₀ := by linarith
  have hA₀nonneg : 0 ≤ A₀ := by
    exact div_nonneg (by positivity) hlogm.le
  have hA₀bound : A₀ ≤
      (X : ℝ) / ((m : ℝ) * Real.log (m : ℝ)) := by
    calc
      A₀ ≤ ((X : ℝ) / (m : ℝ)) / Real.log (m : ℝ) := by
        exact div_le_div_of_nonneg_right Nat.cast_div_le hlogm.le
      _ = (X : ℝ) / ((m : ℝ) * Real.log (m : ℝ)) := by ring
  have hu₁0 : 0 ≤ u₁ := by
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hqNext)) hlogNext.le
  have hu₁5 : u₁ ≤ 5 := by
    simpa only [u₁] using roughSaiasNatHyperbolaLogRatio_le_five
      ha2 (by omega) (by omega) hu5
  have hB₁ : |rho u₁ - I₁| ≤ 16 := by
    have hG : |roughSaiasG (m + 1) u₁| ≤ 16 := by
      rw [← roughSaiasFullyRealG_nat]
      exact roughSaiasFullyRealG_abs_le_sixteen
        (by exact_mod_cast (show 1 < m + 1 by omega)) ⟨hu₁0, hu₁5⟩
    have hbase := roughSaiasG_at_natQuotient_eq_baseFree
      (q := X / (m + 1)) (m := m + 1) (by omega)
    rw [hbase] at hG
    simpa only [u₁, I₁] using hG
  have hrearrange :
      roughSaiasBaseFreeNaturalThetaWeight (X / (m + 1)) (m + 1) -
          roughSaiasBaseFreeNaturalThetaWeight (X / m) m =
        (A₁ - A₀) * (rho u₁ - I₁) +
          A₀ * ((rho u₁ - rho u₀) - (I₁ - I₀)) := by
    unfold roughSaiasBaseFreeNaturalThetaWeight A₀ A₁ u₀ u₁ I₀ I₁
    ring
  rw [roughSaiasNaturalQuotientThetaWeight_diff_eq_baseFree hm2,
    hrearrange]
  calc
    |(A₁ - A₀) * (rho u₁ - I₁) +
        A₀ * ((rho u₁ - rho u₀) - (I₁ - I₀))| ≤
      |A₁ - A₀| * |rho u₁ - I₁| +
        |A₀| * |(rho u₁ - rho u₀) - (I₁ - I₀)| := by
      simpa only [abs_mul] using
        (abs_add_le ((A₁ - A₀) * (rho u₁ - I₁))
          (A₀ * ((rho u₁ - rho u₀) - (I₁ - I₀))))
    _ = roughSaiasSelectorCellLedger X m * |rho u₁ - I₁| +
        A₀ * |(rho u₁ - rho u₀) - (I₁ - I₀)| := by
      simp only [abs_of_nonpos (sub_nonpos.mpr hA₁A₀),
        abs_of_nonneg hA₀nonneg, neg_sub, hcoeff]
    _ ≤ 16 * roughSaiasSelectorCellLedger X m +
        A₀ * (|rho u₁ - rho u₀| + |I₁ - I₀|) := by
      have hfirst := mul_le_mul_of_nonneg_left hB₁ hledgerNonneg
      have hsecond := mul_le_mul_of_nonneg_left
        (abs_sub (rho u₁ - rho u₀) (I₁ - I₀)) hA₀nonneg
      calc
        roughSaiasSelectorCellLedger X m * |rho u₁ - I₁| +
            A₀ * |(rho u₁ - rho u₀) - (I₁ - I₀)| ≤
          roughSaiasSelectorCellLedger X m * 16 +
            A₀ * (|rho u₁ - rho u₀| + |I₁ - I₀|) :=
          add_le_add hfirst hsecond
        _ = 16 * roughSaiasSelectorCellLedger X m +
            A₀ * (|rho u₁ - rho u₀| + |I₁ - I₀|) := by ring
    _ ≤ 16 * roughSaiasSelectorCellLedger X m +
        ((X : ℝ) / ((m : ℝ) * Real.log (m : ℝ))) *
          (|rho u₁ - rho u₀| + |I₁ - I₀|) := by
      exact add_le_add
        le_rfl
        (mul_le_mul_of_nonneg_right hA₀bound
          (add_nonneg (abs_nonneg _) (abs_nonneg _)))
    _ = 16 * roughSaiasSelectorCellLedger X m +
        ((X : ℝ) / ((m : ℝ) * Real.log (m : ℝ))) *
          (|rho (Real.log ((X / (m + 1) : ℕ) : ℝ) /
                  Real.log ((m + 1 : ℕ) : ℝ)) -
              rho (Real.log ((X / m : ℕ) : ℝ) /
                Real.log (m : ℝ))| +
            |roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1) -
              roughSaiasBaseFreeFractionalIntegral (X / m) m|) := by
      rfl



































/-! ## Closed sharp defect and endpoint witnesses -/











end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_030 := by
  exact @Erdos390.WholePaper.roughSaiasNaturalQuotientThetaWeight_succ_sub_abs_le_hyperbolaComponents
