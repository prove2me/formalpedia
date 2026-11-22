-- Prove2me | solution 1 for Erdos390.WholePaper.abs_sum_roughSaiasFullyRealNaturalCells_lower_le_forty_invLogSq_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:51:28.533482+00:00
-- url     : https://prove2.me/submissions/73d23f3e-1566-489c-8508-ccf48030acbc

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
import Theorems.Thm_Erdos390_WholePaper_roughSaiasFullyRealBaseFreeFractionalIntegral_hyperbola_cell_abs_sub_le_compact
import Theorems.Thm_Erdos390_WholePaper_sum_roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger_le_two_inv_log_compact




section
theorem Erdos390.WholePaper.sum_roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger_le_two_inv_log : Erdos390.RemainingAnalyticGoal008_034 := @Erdos390.WholePaper.sum_roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger_le_two_inv_log_compact
end
section
theorem Erdos390.WholePaper.roughSaiasFullyRealBaseFreeFractionalIntegral_hyperbola_cell_abs_sub_le : Erdos390.RemainingAnalyticGoal008_027 := @Erdos390.WholePaper.roughSaiasFullyRealBaseFreeFractionalIntegral_hyperbola_cell_abs_sub_le_compact
end
section
theorem Erdos390.WholePaper.roughCompactBV_translation_le_of_le : Erdos390.RemainingAnalyticGoal008_019 := @Erdos390.WholePaper.roughCompactBV_translation_le_of_le_compact
end
/- Source module: Erdos390.Full.FriableAsymptotic -/
section


/-!
# Friable counts on the Erdős 390 scale

This file develops the arithmetic side of the uniform Dickman estimate from
Mathlib's actual finite set `Nat.smoothNumbersUpTo`.  In particular, the
statements below are exact finite identities: no asymptotic count is exposed
as a hypothesis or a contract.

Our second parameter `y` is inclusive: `friableCount X y` counts positive
integers at most `X` all of whose prime factors are at most `y`.  Thus the
underlying Mathlib smoothness threshold is `y + 1`.
-/

open scoped BigOperators
open Filter Topology Asymptotics

namespace Erdos390.Full.FriableAsymptotic

open ArithmeticModel DickmanBasic Scale

/-! ## Quantitative prime-number input

The finite de Bruijn induction below needs a power-saving prime Stieltjes
estimate.  We derive it here from the audited medium-strength PNT, rather than
postulating a prime-distribution contract.  The exponential PNT remainder is
stronger than every fixed power of `1 / log x`.
-/



















































/-! ## Explicit regularity of the finite Dickman kernel -/









/-! ## The Dickman test weight in the prime recurrence -/











/-- The continuous Dickman test weight is continuous away from the two
irrelevant singular points `0` and `1`. -/
theorem continuousOn_dickmanContinuousWeight (X : ℝ) :
    ContinuousOn (dickmanContinuousWeight X) (Set.Ioi (1 : ℝ)) := by
  intro t ht
  rw [Set.mem_Ioi] at ht
  have ht0 : t ≠ 0 := by linarith [ht]
  have ht1 : t ≠ 1 := by linarith [ht]
  have hlog_ne : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht]) ht1
  have hlog : ContinuousAt Real.log t := Real.continuousAt_log ht0
  have hq : ContinuousAt
      (fun u : ℝ => Real.log X / Real.log u - 1) t :=
    (continuousAt_const.div hlog hlog_ne).sub continuousAt_const
  have hrho : ContinuousAt
      (fun u : ℝ => rho (Real.log X / Real.log u - 1)) t :=
    continuous_rho.continuousAt.comp hq
  have hmain : ContinuousAt
      (fun u : ℝ => X / u * rho (Real.log X / Real.log u - 1)) t :=
    (continuousAt_const.div continuousAt_id ht0).mul hrho
  exact (hmain.div hlog hlog_ne).continuousWithinAt







































/-! ## Explicit oscillation and Riemann error for the Dickman weight -/


open DickmanBasic






























/-! ## Quantitative PNT transfer for the Dickman prime weight

The following estimates combine the preceding Chebyshev--Stieltjes identity,
the audited medium PNT, and the explicit Dickman-weight oscillation bound.
They are the one-prime analytic input for the finite de Bruijn induction.
-/


















/-! ## Uniform floor stability for the recursive Dickman kernel -/





























































end Erdos390.Full.FriableAsymptotic

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

/- Source module: Erdos390.WholePaper.RoughSaiasRightAbel -/
section


/-!
# Abel summation with a right derivative

The Dickman test function used in the de Bruijn--Saias Stieltjes
functional is continuous, but it has a corner when its logarithmic
coordinate is `1`.  The usual `sum_mul_eq_sub_sub_integral_mul` asks for a
two-sided derivative at every point of the closed interval and therefore
does not apply literally.

This file records the exact variant needed here.  Its proof follows the
unit-cell proof of Mathlib's Abel summation theorem, replacing the ordinary
FTC on a cell by `integral_eq_sub_of_hasDeriv_right_of_le`.  A single corner
(or indeed finitely many corners) is harmless as long as the displayed
right derivative exists and is integrable.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Finset MeasureTheory Set

noncomputable section

namespace RoughSaiasRightAbel

variable (c : ℕ → ℝ)

/-! ## Unit-cell facts -/

private theorem prefix_eq_on_unit_cell {m n : ℕ} :
    ∀ᵐ t : ℝ, t ∈ Set.Icc (n : ℝ) (n + 1) →
      ∑ k ∈ Finset.Icc m ⌊t⌋₊, c k =
        ∑ k ∈ Finset.Icc m n, c k := by
  filter_upwards [MeasureTheory.Ico_ae_eq_Icc] with t ht hmem
  rw [Nat.floor_eq_on_Ico _ _ (ht.mpr hmem)]

private theorem right_integral_mul_prefix
    {f f' : ℝ → ℝ} {a b t₁ t₂ : ℝ} {n : ℕ}
    (_hab : a ≤ b)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_right : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt f (f' t) (Set.Ioi t) t)
    (hf'_int : IntegrableOn f' (Set.Icc a b))
    (ht : t₁ ≤ t₂) (hn₁ : (n : ℝ) ≤ t₁)
    (ht₂n : t₂ ≤ (n : ℝ) + 1)
    (hat₁ : a ≤ t₁) (ht₂b : t₂ ≤ b) :
    (∫ t in t₁..t₂,
        f' t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =
      (f t₂ - f t₁) * ∑ k ∈ Finset.Icc 0 n, c k := by
  have hcell : Set.uIoc t₁ t₂ ⊆ Set.Icc (n : ℝ) (n + 1) := by
    rw [Set.uIoc_of_le ht]
    exact Set.Ioc_subset_Icc_self.trans
      (Set.Icc_subset_Icc hn₁ ht₂n)
  have hsub : Set.Icc t₁ t₂ ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc hat₁ ht₂b
  have hftc : (∫ t in t₁..t₂, f' t) = f t₂ - f t₁ := by
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
    · exact hf_cont.mono hsub
    · intro t htOpen
      exact hf_right t
        ⟨hat₁.trans_lt htOpen.1, htOpen.2.trans_le ht₂b⟩
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht]
      exact hf'_int.mono_set hsub
  rw [← hftc, ← intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [prefix_eq_on_unit_cell c (m := 0) (n := n)] with t hpref htmem
  rw [hpref (hcell htmem)]

private theorem left_floor_bounds {a b : ℝ} {k : ℕ}
    (hk : k ∈ Set.Ico (⌊a⌋₊ + 1) ⌊b⌋₊) :
    a ≤ k ∧ k + 1 ≤ b := by
  constructor
  · have hkleft := (Set.mem_Ico.mp hk).1
    exact le_of_lt ((Nat.floor_lt' (by omega)).mp hkleft)
  · rw [← Nat.cast_add_one, ← Nat.le_floor_iff' (Nat.succ_ne_zero k)]
    exact (Set.mem_Ico.mp hk).2

private theorem left_floor_bounds_finset {a b : ℝ} {k : ℕ}
    (hk : k ∈ Finset.Ico (⌊a⌋₊ + 1) ⌊b⌋₊) :
    a ≤ k ∧ k + 1 ≤ b := by
  exact left_floor_bounds (by simpa only [← Finset.coe_Ico] using hk)

/-! ## The right-derivative Abel identity -/

/-- Abel summation on a compact real interval for a continuous test
function with an integrable right derivative.  This differs from
`sum_mul_eq_sub_sub_integral_mul` only in the regularity datum. -/
theorem sum_mul_eq_sub_sub_integral_mul_right
    {f f' : ℝ → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_right : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt f (f' t) (Set.Ioi t) t)
    (hf'_int : IntegrableOn f' (Set.Icc a b)) :
    (∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k) =
      f b * (∑ k ∈ Finset.Icc 0 ⌊b⌋₊, c k) -
        f a * (∑ k ∈ Finset.Icc 0 ⌊a⌋₊, c k) -
        ∫ t in Set.Ioc a b,
          f' t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k := by
  rw [← intervalIntegral.integral_of_le hab]
  have haFloor : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le ha
  have hbCeil : b ≤ (⌊b⌋₊ : ℝ) + 1 :=
    (Nat.lt_floor_add_one _).le
  obtain hfloorEq | hfloorLt :=
      eq_or_lt_of_le (Nat.floor_le_floor hab)
  · rw [hfloorEq, Finset.Ioc_eq_empty_of_le le_rfl, Finset.sum_empty,
      ← sub_mul,
      right_integral_mul_prefix c hab hf_cont hf_right hf'_int
        hab (hfloorEq ▸ haFloor) hbCeil le_rfl le_rfl,
      sub_self]
  · have haSucc : a ≤ (⌊a⌋₊ : ℝ) + 1 :=
      (Nat.lt_floor_add_one _).le
    have haSuccB : (⌊a⌋₊ : ℝ) + 1 ≤ b := by
      rw [← Nat.cast_add_one, ← Nat.le_floor_iff (ha.trans hab)]
      exact hfloorLt
    have hbFloor : (⌊b⌋₊ : ℝ) ≤ b :=
      Nat.floor_le (ha.trans hab)
    have haFloorB : a ≤ (⌊b⌋₊ : ℝ) :=
      (Nat.floor_lt ha).mp hfloorLt |>.le
    simp_rw [← smul_eq_mul,
      Finset.sum_Ioc_by_parts (fun k ↦ f k) _ hfloorLt,
      Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc,
      smul_eq_mul]
    have hcells :
        (∑ k ∈ Finset.Ioc ⌊a⌋₊ (⌊b⌋₊ - 1),
            (f ((k + 1 : ℕ) : ℝ) - f k) *
              ∑ n ∈ Finset.Icc 0 k, c n) =
          ∑ k ∈ Finset.Ico (⌊a⌋₊ + 1) ⌊b⌋₊,
            ∫ t in (k : ℝ)..(k + 1 : ℕ),
              f' t * ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n := by
      rw [← Finset.Ico_add_one_add_one_eq_Ioc,
        Nat.sub_add_cancel (by omega), Eq.comm]
      apply Finset.sum_congr rfl
      intro k hk
      have hkBounds := left_floor_bounds_finset (a := a) (b := b) hk
      exact right_integral_mul_prefix c
        (t₁ := (k : ℝ)) (t₂ := ((k + 1 : ℕ) : ℝ)) (n := k)
        hab hf_cont hf_right hf'_int
        (by exact_mod_cast k.le_succ) le_rfl
        (by norm_num) hkBounds.1
        (by simpa only [Nat.cast_add, Nat.cast_one] using hkBounds.2)
    rw [hcells,
      intervalIntegral.sum_integral_adjacent_intervals_Ico hfloorLt,
      Nat.cast_add, Nat.cast_one,
      ← intervalIntegral.integral_interval_sub_left
        (a := a) (c := (⌊a⌋₊ : ℝ) + 1),
      ← intervalIntegral.integral_add_adjacent_intervals
        (b := (⌊b⌋₊ : ℝ)) (c := b),
      right_integral_mul_prefix c hab hf_cont hf_right hf'_int
        haSucc haFloor le_rfl le_rfl haSuccB,
      right_integral_mul_prefix c hab hf_cont hf_right hf'_int
        hbFloor le_rfl hbCeil haFloorB le_rfl]
    · ring
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le haFloorB]
      exact (integrableOn_mul_sum_Icc c ha hf'_int).mono_set
        (Set.Icc_subset_Icc_right hbFloor)
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hbFloor]
      exact (integrableOn_mul_sum_Icc c ha hf'_int).mono_set
        (Set.Icc_subset_Icc_left haFloorB)
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le haFloorB]
      exact (integrableOn_mul_sum_Icc c ha hf'_int).mono_set
        (Set.Icc_subset_Icc_right hbFloor)
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le haSucc]
      exact (integrableOn_mul_sum_Icc c ha hf'_int).mono_set
        (Set.Icc_subset_Icc_right haSuccB)
    · intro k hk
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le
        (by exact_mod_cast k.le_succ)]
      have hkBounds := left_floor_bounds (a := a) (b := b) hk
      have hkUpper : (((k + 1 : ℕ) : ℝ) ≤ b) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hkBounds.2
      exact (integrableOn_mul_sum_Icc c ha hf'_int).mono_set
        (Set.Icc_subset_Icc hkBounds.1 hkUpper)



end RoughSaiasRightAbel

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasStieltjesKernel -/
section


/-!
# The compact Dickman kernel for the de Bruijn signed functional

This file isolates the only nonsmooth point in the integration-by-parts
identification of the Saias normal form.  The repository's finite Dickman
function is `1` to the left of the first face, so its right derivative as a
function of the Stieltjes variable is zero when the logarithmic coordinate
is exactly `1`.  This is different at one point from
`roughSaiasDickmanDerivative`, whose value at `1` is the *Dickman-coordinate*
right limit `-1`.

The open-face representative below has value zero at that corner.  It gives
an honest right derivative for the Stieltjes test function; changing it back
to `roughSaiasDickmanDerivative` later is an almost-everywhere, one-point
change.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section





theorem roughSaiasOpenFaceDickmanDerivative_of_one_lt
    {u : ℝ} (hu : 1 < u) :
    roughSaiasOpenFaceDickmanDerivative u = -rho (u - 1) / u := by
  simp [roughSaiasOpenFaceDickmanDerivative, not_le.mpr hu]



/-- Away from the single corner, the open-face and right-limit
representatives agree pointwise. -/
theorem roughSaiasOpenFaceDickmanDerivative_eq_roughSaias
    {u : ℝ} (hu : u ≠ 1) :
    roughSaiasOpenFaceDickmanDerivative u =
      roughSaiasDickmanDerivative u := by
  rcases lt_or_gt_of_ne hu with hu1 | h1u
  · rw [roughSaiasOpenFaceDickmanDerivative_of_le_one hu1.le,
      roughSaiasDickmanDerivative_of_lt_one hu1]
  · rw [roughSaiasOpenFaceDickmanDerivative_of_one_lt h1u,
      roughSaiasDickmanDerivative_of_one_le h1u.le]

theorem measurable_roughSaiasOpenFaceDickmanDerivative :
    Measurable roughSaiasOpenFaceDickmanDerivative := by
  unfold roughSaiasOpenFaceDickmanDerivative
  apply Measurable.ite measurableSet_Iic measurable_const
  exact (continuous_rho.measurable.comp
    (measurable_id.sub_const 1)).neg.div measurable_id

/-- The open-face representative has the same unit bound as the
right-limit representative on the compact five-face range. -/
theorem roughSaiasOpenFaceDickmanDerivative_abs_le_one
    {u : ℝ} (hu5 : u ≤ 5) :
    |roughSaiasOpenFaceDickmanDerivative u| ≤ 1 := by
  by_cases hu1 : u ≤ 1
  · simp [roughSaiasOpenFaceDickmanDerivative_of_le_one hu1]
  · have h1u : 1 < u := lt_of_not_ge hu1
    have hb := FriableAsymptotic.rho_delay_integrand_bounds h1u.le hu5
    rw [roughSaiasOpenFaceDickmanDerivative_of_one_lt
        h1u, neg_div, abs_neg, abs_of_nonneg hb.1]
    exact hb.2



/-! ## Real logarithmic coordinate and Stieltjes test function -/







/-- On `1 ≤ t ≤ x`, the Stieltjes coordinate stays between zero and
the endpoint coordinate. -/
theorem roughSaiasStieltjesCoordinate_mem
    {x y t : ℝ} (hy : 1 < y) (ht1 : 1 ≤ t) (htx : t ≤ x) :
    0 ≤ roughSaiasStieltjesCoordinate x y t ∧
      roughSaiasStieltjesCoordinate x y t ≤
        Real.log x / Real.log y := by
  have htpos : 0 < t := zero_lt_one.trans_le ht1
  have hxpos : 0 < x := htpos.trans_le htx
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hlogtx : Real.log t ≤ Real.log x :=
    Real.log_le_log htpos htx
  have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  unfold roughSaiasStieltjesCoordinate
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlogtx) hlogy.le
  · apply (div_le_iff₀ hlogy).2
    have hendpoint :
        Real.log x / Real.log y * Real.log y = Real.log x := by
      field_simp [hlogy.ne']
    rw [hendpoint]
    linarith

/-- Continuity of the Stieltjes test on every positive compact interval. -/
theorem continuousOn_roughSaiasStieltjesTest
    {x y A B : ℝ} (hy : 1 < y) (hA : 0 < A) :
    ContinuousOn (roughSaiasStieltjesTest x y) (Set.Icc A B) := by
  intro t ht
  have htpos : 0 < t := hA.trans_le ht.1
  have ht0 : t ≠ 0 := htpos.ne'
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  have hcoord : ContinuousAt (roughSaiasStieltjesCoordinate x y) t := by
    unfold roughSaiasStieltjesCoordinate
    exact (continuousAt_const.sub (Real.continuousAt_log ht0)).div_const _
  unfold roughSaiasStieltjesTest
  exact ((continuousAt_const.mul
      (continuous_rho.continuousAt.comp hcoord)).div
        continuousAt_id ht0).continuousWithinAt

/-! ## The corner-safe right derivative -/

/-- The displayed derivative is the genuine right derivative throughout
the compact Stieltjes interval.  At coordinate `1`, increasing `t` moves
onto the constant Dickman face, hence the zero open-face value above. -/
theorem hasDerivWithinAt_roughSaiasStieltjesTest_right
    {x y t : ℝ} (hy : 1 < y) (ht1 : 1 ≤ t) (htx : t ≤ x)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    HasDerivWithinAt (roughSaiasStieltjesTest x y)
      (roughSaiasStieltjesTestRightDerivative x y t)
      (Set.Ioi t) t := by
  have htpos : 0 < t := zero_lt_one.trans_le ht1
  have ht0 : t ≠ 0 := htpos.ne'
  have hxpos : 0 < x := htpos.trans_le htx
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hcoordMem := roughSaiasStieltjesCoordinate_mem hy ht1 htx
  have hcoord5 : roughSaiasStieltjesCoordinate x y t ≤ 5 :=
    hcoordMem.2.trans hu5
  by_cases hface : roughSaiasStieltjesCoordinate x y t ≤ 1
  · have heq :
        roughSaiasStieltjesTest x y =ᶠ[nhdsWithin t (Set.Ioi t)]
          (fun s : ℝ ↦ x / s) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hts : t < s := hs
      have hspos : 0 < s := htpos.trans hts
      have hlogts : Real.log t < Real.log s :=
        Real.strictMonoOn_log htpos hspos hts
      have hcoordLt :
          roughSaiasStieltjesCoordinate x y s <
            roughSaiasStieltjesCoordinate x y t := by
        unfold roughSaiasStieltjesCoordinate
        exact (div_lt_div_iff_of_pos_right hlogy).2 (by linarith)
      rw [roughSaiasStieltjesTest,
        rho_eq_one_of_le_one (hcoordLt.le.trans hface)]
      ring
    have hsimple : HasDerivAt (fun s : ℝ ↦ x / s) (-x / t ^ 2) t := by
      have h := (hasDerivAt_const t x).div (hasDerivAt_id t) ht0
      convert h using 1
      simp only [id_eq, zero_mul, mul_one, zero_sub]
    have hvalue : roughSaiasStieltjesTest x y t = x / t := by
      rw [roughSaiasStieltjesTest, rho_eq_one_of_le_one hface]
      ring
    have hcongr := hsimple.hasDerivWithinAt.congr_of_eventuallyEq
      heq hvalue
    convert hcongr using 1
    unfold roughSaiasStieltjesTestRightDerivative
    simp only [roughSaiasOpenFaceDickmanDerivative_of_le_one hface,
      mul_zero, zero_mul, zero_div, rho_eq_one_of_le_one hface,
      mul_one, zero_sub]
    ring
  · have hface' : 1 < roughSaiasStieltjesCoordinate x y t :=
      lt_of_not_ge hface
    have hcoordDeriv :
        HasDerivAt (roughSaiasStieltjesCoordinate x y)
          (-1 / (t * Real.log y)) t := by
      unfold roughSaiasStieltjesCoordinate
      have h := ((hasDerivAt_const t (Real.log x)).sub
        (Real.hasDerivAt_log ht0)).div_const (Real.log y)
      convert h using 1
      field_simp [ht0, hlogy.ne']
      ring
    have hrho : HasDerivAt
        (fun s : ℝ ↦ rho (roughSaiasStieltjesCoordinate x y s))
        ((-rho (roughSaiasStieltjesCoordinate x y t - 1) /
            roughSaiasStieltjesCoordinate x y t) *
          (-1 / (t * Real.log y))) t :=
      (hasDerivAt_rho hface' (hcoord5.trans (by norm_num))).comp t hcoordDeriv
    have hquot := ((hasDerivAt_const t x).mul hrho).div
      (hasDerivAt_id t) ht0
    convert hquot.hasDerivWithinAt using 1
    unfold roughSaiasStieltjesTestRightDerivative
    rw [roughSaiasOpenFaceDickmanDerivative_of_one_lt hface']
    simp only [id_eq, Pi.mul_apply, zero_mul, zero_add, mul_one]
    field_simp [ht0]

/-- The right-derivative theorem in the exact open-interval shape expected
by `sum_mul_eq_sub_sub_integral_mul_right`. -/
theorem roughSaiasStieltjesTest_hasRightDerivOn
    {x y R : ℝ} (hy : 1 < y) (_hR : 1 ≤ R) (hRx : R ≤ x)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    ∀ t ∈ Set.Ioo (1 : ℝ) R,
      HasDerivWithinAt (roughSaiasStieltjesTest x y)
        (roughSaiasStieltjesTestRightDerivative x y t)
        (Set.Ioi t) t := by
  intro t ht
  exact hasDerivWithinAt_roughSaiasStieltjesTest_right hy ht.1.le
    (ht.2.le.trans hRx) hu5

/-! ## Integrability of the right derivative -/

theorem measurable_roughSaiasStieltjesCoordinate (x y : ℝ) :
    Measurable (roughSaiasStieltjesCoordinate x y) := by
  unfold roughSaiasStieltjesCoordinate
  exact (measurable_const.sub Real.measurable_log).div measurable_const

theorem measurable_roughSaiasStieltjesTestRightDerivative
    (x y : ℝ) :
    Measurable (roughSaiasStieltjesTestRightDerivative x y) := by
  have hcoord := measurable_roughSaiasStieltjesCoordinate x y
  unfold roughSaiasStieltjesTestRightDerivative
  exact (((measurable_const.mul
      (measurable_roughSaiasOpenFaceDickmanDerivative.comp hcoord)).mul
        (measurable_const.div
          (measurable_id.mul measurable_const))).div measurable_id).sub
      ((measurable_const.mul (continuous_rho.measurable.comp hcoord)).div
        (measurable_id.pow_const 2))

/-- A crude compact majorant, used only to certify ordinary integrability.
The later sharp estimates retain the signed kernel and do not use this
triangle inequality. -/
theorem roughSaiasStieltjesTestRightDerivative_abs_le
    {x y t : ℝ} (hy : 1 < y) (ht1 : 1 ≤ t) (htx : t ≤ x)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    |roughSaiasStieltjesTestRightDerivative x y t| ≤
      x * (1 / Real.log y + 1) := by
  have htpos : 0 < t := zero_lt_one.trans_le ht1
  have hxpos : 0 < x := htpos.trans_le htx
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hcoord := roughSaiasStieltjesCoordinate_mem hy ht1 htx
  have hcoord5 : roughSaiasStieltjesCoordinate x y t ≤ 5 :=
    hcoord.2.trans hu5
  have hD := roughSaiasOpenFaceDickmanDerivative_abs_le_one hcoord5
  have hrho0 : 0 ≤ rho (roughSaiasStieltjesCoordinate x y t) :=
    (rho_pos_on_zero_five hcoord.1 hcoord5).le
  have hrho1 : rho (roughSaiasStieltjesCoordinate x y t) ≤ 1 :=
    FriableAsymptotic.rho_le_one_of_le_five hcoord5
  have hdenom : 0 < t * Real.log y := mul_pos htpos hlogy
  have hinvDenom : 1 / (t * Real.log y) ≤ 1 / Real.log y := by
    apply one_div_le_one_div_of_le hlogy
    nlinarith [mul_le_mul_of_nonneg_right ht1 hlogy.le]
  have hfirstNonneg :
      0 ≤ x *
        |roughSaiasOpenFaceDickmanDerivative
          (roughSaiasStieltjesCoordinate x y t)| *
          (1 / (t * Real.log y)) := by positivity
  have hfirst :
      |x * roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate x y t) *
          (-1 / (t * Real.log y)) / t| ≤
        x * (1 / Real.log y) := by
    calc
      _ = (x *
          |roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate x y t)| *
            (1 / (t * Real.log y))) / t := by
          rw [abs_div, abs_mul, abs_mul, neg_div, abs_neg, abs_div,
            abs_one, abs_of_pos hxpos, abs_of_pos hdenom,
            abs_of_pos htpos]
      _ ≤ x *
          |roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate x y t)| *
            (1 / (t * Real.log y)) :=
        div_le_self hfirstNonneg ht1
      _ ≤ x * 1 * (1 / Real.log y) := by
        gcongr
      _ = x * (1 / Real.log y) := by ring
  have hsecond :
      |x * rho (roughSaiasStieltjesCoordinate x y t) / t ^ 2| ≤ x := by
    rw [abs_of_nonneg (div_nonneg (mul_nonneg hxpos.le hrho0)
      (sq_nonneg t))]
    calc
      x * rho (roughSaiasStieltjesCoordinate x y t) / t ^ 2 ≤
          x * rho (roughSaiasStieltjesCoordinate x y t) :=
        div_le_self (mul_nonneg hxpos.le hrho0) (by nlinarith)
      _ ≤ x * 1 := mul_le_mul_of_nonneg_left hrho1 hxpos.le
      _ = x := mul_one x
  unfold roughSaiasStieltjesTestRightDerivative
  calc
    _ ≤
        |x * roughSaiasOpenFaceDickmanDerivative
              (roughSaiasStieltjesCoordinate x y t) *
            (-1 / (t * Real.log y)) / t| +
          |x * rho (roughSaiasStieltjesCoordinate x y t) / t ^ 2| :=
      abs_sub _ _
    _ ≤ x * (1 / Real.log y) + x := add_le_add hfirst hsecond
    _ = x * (1 / Real.log y + 1) := by ring



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasContinuousBuchstab -/
section


/-!
# The compact base-free functional behind continuous Buchstab

The de Bruijn approximation has a base-free Stieltjes description against

`d (floor t / t)`.

Since `t \mapsto floor t / t` is not monotone, Mathlib's positive
`StieltjesFunction.measure` is not the right primitive here.  On a finite
interval its signed action is instead represented explicitly as

`sum f(n) / n - integral f(t) floor(t) / t^2 dt`.

This file introduces that atom-minus-density functional, together with the
zero extension of the Dickman function which supplies its exact support.
The cutoff is kept as an explicit natural number: in the continuous
Buchstab identity the outer cutoff can then remain fixed while the first
argument changes from `x` to `x / s`.  The support lemmas below show that
this choice is harmless.

The eventual identification with `roughSaiasLambdaNormalForm` is a separate
finite Abel calculation.  In particular, no equality with the Stieltjes
normalization is built into any definition in this file.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## The supported Dickman profile -/





theorem roughSaiasZeroExtendedRho_of_nonneg
    {u : ℝ} (hu : 0 ≤ u) :
    roughSaiasZeroExtendedRho u = rho u := by
  simp [roughSaiasZeroExtendedRho, not_lt.mpr hu]



theorem measurable_roughSaiasZeroExtendedRho :
    Measurable roughSaiasZeroExtendedRho := by
  unfold roughSaiasZeroExtendedRho
  apply Measurable.ite measurableSet_Iio measurable_const
  exact continuous_rho.measurable

/-- On the five constructed faces, the supported profile remains in the
unit interval. -/
theorem roughSaiasZeroExtendedRho_mem_unitInterval
    {u : ℝ} (hu5 : u ≤ 5) :
    0 ≤ roughSaiasZeroExtendedRho u ∧
      roughSaiasZeroExtendedRho u ≤ 1 := by
  by_cases hu : u < 0
  · simp [roughSaiasZeroExtendedRho_of_neg hu]
  · have hu0 : 0 ≤ u := le_of_not_gt hu
    rw [roughSaiasZeroExtendedRho_of_nonneg hu0]
    exact ⟨(rho_pos_on_zero_five hu0 hu5).le,
      FriableAsymptotic.rho_le_one_of_le_five hu5⟩





theorem measurable_roughSaiasStieltjesDickmanProfile
    (x y : ℝ) :
    Measurable (roughSaiasStieltjesDickmanProfile x y) := by
  have hquot : Measurable (fun t : ℝ => x / t) :=
    measurable_const.div measurable_id
  have hcoordinate : Measurable
      (fun t : ℝ => Real.log (x / t) / Real.log y) :=
    (Real.measurable_log.comp hquot).div measurable_const
  exact measurable_const.mul
    (measurable_roughSaiasZeroExtendedRho.comp hcoordinate)

/-- The supported profile is exactly zero beyond its first argument. -/
theorem roughSaiasStieltjesDickmanProfile_eq_zero_of_lt
    {x y t : ℝ} (hx : 0 < x) (hy : 1 < y)
    (ht : 0 < t) (hxt : x < t) :
    roughSaiasStieltjesDickmanProfile x y t = 0 := by
  have hratioPos : 0 < x / t := div_pos hx ht
  have hratioLt : x / t < 1 := (div_lt_one ht).2 hxt
  have hlogRatio : Real.log (x / t) < 0 :=
    Real.log_neg hratioPos hratioLt
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hcoordinate : Real.log (x / t) / Real.log y < 0 :=
    div_neg_of_neg_of_pos hlogRatio hlogy
  unfold roughSaiasStieltjesDickmanProfile
  rw [roughSaiasZeroExtendedRho_of_neg hcoordinate, mul_zero]





/-- On the supported interval, the logarithmic quotient used in this file
is the real coordinate from `RoughSaiasStieltjesKernel`. -/
theorem roughSaiasStieltjesCoordinate_eq_log_div
    {x y t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    roughSaiasStieltjesCoordinate x y t =
      Real.log (x / t) / Real.log y := by
  unfold roughSaiasStieltjesCoordinate
  rw [Real.log_div hx.ne' ht.ne']

/-- Dividing the supported profile by the Stieltjes variable gives exactly
the corner-safe Abel test from `RoughSaiasStieltjesKernel`. -/
theorem roughSaiasStieltjesDickmanProfile_div_eq_test
    {x y t : ℝ} (hx : 0 < x) (hy : 1 < y)
    (ht : 0 < t) (htx : t ≤ x) :
    roughSaiasStieltjesDickmanProfile x y t / t =
      roughSaiasStieltjesTest x y t := by
  have hratio : 1 ≤ x / t := by
    exact (le_div_iff₀ ht).2 (by simpa using htx)
  have hcoordinate :
      0 ≤ Real.log (x / t) / Real.log y :=
    div_nonneg (Real.log_nonneg hratio) (Real.log_pos hy).le
  unfold roughSaiasStieltjesDickmanProfile roughSaiasStieltjesTest
    roughSaiasStieltjesCoordinate
  rw [roughSaiasZeroExtendedRho_of_nonneg hcoordinate,
    Real.log_div hx.ne' ht.ne']

/-- Multiplicative form of the preceding test-profile identification. -/
theorem roughSaiasStieltjesDickmanProfile_eq_mul_test
    {x y t : ℝ} (hx : 0 < x) (hy : 1 < y)
    (ht : 0 < t) (htx : t ≤ x) :
    roughSaiasStieltjesDickmanProfile x y t =
      t * roughSaiasStieltjesTest x y t := by
  have h := roughSaiasStieltjesDickmanProfile_div_eq_test
    hx hy ht htx
  have ht0 : t ≠ 0 := ht.ne'
  calc
    roughSaiasStieltjesDickmanProfile x y t =
        (roughSaiasStieltjesDickmanProfile x y t / t) * t :=
      (div_mul_cancel₀ _ ht0).symm
    _ = t * roughSaiasStieltjesTest x y t := by
      rw [h]
      ring



/-! ## The finite atom-minus-density functional -/



theorem measurable_roughSaiasFloorDensity :
    Measurable roughSaiasFloorDensity := by
  have hfloorNat : Measurable (fun t : ℝ => ⌊t⌋₊) :=
    measurable_id.nat_floor
  have hfloorReal : Measurable (fun t : ℝ => ((⌊t⌋₊ : ℕ) : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hfloorNat
  exact hfloorReal.div (measurable_id.pow_const 2)





















/-! ## Cutoff independence -/

theorem roughSaiasStieltjesAtomPart_eq_of_cutoff
    {R S : ℕ} {f : ℝ → ℝ} (hRS : R ≤ S)
    (hzero : ∀ n, R < n → n ≤ S → f (n : ℝ) = 0) :
    roughSaiasStieltjesAtomPart R f =
      roughSaiasStieltjesAtomPart S f := by
  unfold roughSaiasStieltjesAtomPart
  apply Finset.sum_subset
  · intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans hRS⟩
  · intro n hnS hnR
    have hnData := Finset.mem_Icc.mp hnS
    have hRn : R < n := by
      by_contra hnot
      apply hnR
      exact Finset.mem_Icc.mpr ⟨hnData.1, le_of_not_gt hnot⟩
    rw [hzero n hRn hnData.2, zero_div]

theorem roughSaiasStieltjesDensityPart_eq_of_cutoff
    {R S : ℕ} {f : ℝ → ℝ} (hRS : R ≤ S)
    (hzero : ∀ t, (R : ℝ) < t → t ≤ (S : ℝ) → f t = 0) :
    roughSaiasStieltjesDensityPart R f =
      roughSaiasStieltjesDensityPart S f := by
  have hsubset : Set.Ioc (1 : ℝ) (R : ℝ) ⊆
      Set.Ioc (1 : ℝ) (S : ℝ) := by
    rintro t ⟨ht1, htR⟩
    exact ⟨ht1, htR.trans (by exact_mod_cast hRS)⟩
  unfold roughSaiasStieltjesDensityPart
  symm
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
    measurableSet_Ioc hsubset
  intro t ht
  have htS := ht.1
  have htNotR := ht.2
  have hRt : (R : ℝ) < t := by
    by_contra hnot
    exact htNotR ⟨htS.1, le_of_not_gt hnot⟩
  rw [hzero t hRt htS.2, zero_mul]

theorem roughSaiasFiniteStieltjesFunctional_eq_of_cutoff
    {R S : ℕ} {f : ℝ → ℝ} (hRS : R ≤ S)
    (hzero : ∀ t, (R : ℝ) < t → t ≤ (S : ℝ) → f t = 0) :
    roughSaiasFiniteStieltjesFunctional R f =
      roughSaiasFiniteStieltjesFunctional S f := by
  have hzeroNat : ∀ n, R < n → n ≤ S → f (n : ℝ) = 0 := by
    intro n hRn hnS
    exact hzero (n : ℝ) (by exact_mod_cast hRn) (by exact_mod_cast hnS)
  unfold roughSaiasFiniteStieltjesFunctional
  rw [roughSaiasStieltjesAtomPart_eq_of_cutoff hRS hzeroNat,
    roughSaiasStieltjesDensityPart_eq_of_cutoff hRS hzero]

/-! ## A real-base de Bruijn functional -/





/-- Once the cap lies above `x`, enlarging it changes neither the atoms nor
the density. -/
theorem roughSaiasLambdaStieltjesWithCutoff_eq_of_le
    {R S : ℕ} {x y : ℝ} (hRS : R ≤ S)
    (hx : 0 < x) (hy : 1 < y) (hxR : x ≤ (R : ℝ)) :
    roughSaiasLambdaStieltjesWithCutoff R x y =
      roughSaiasLambdaStieltjesWithCutoff S x y := by
  unfold roughSaiasLambdaStieltjesWithCutoff
  apply roughSaiasFiniteStieltjesFunctional_eq_of_cutoff hRS
  intro t hRt htS
  have hxt : x < t := hxR.trans_lt hRt
  exact roughSaiasStieltjesDickmanProfile_eq_zero_of_lt
    hx hy (hx.trans hxt) hxt

theorem roughSaiasLambdaStieltjesWithCutoff_eq_canonical
    {R : ℕ} {x y : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hxR : x ≤ (R : ℝ)) :
    roughSaiasLambdaStieltjesWithCutoff R x y =
      roughSaiasLambdaStieltjes x y := by
  have hceilR : ⌈x⌉₊ ≤ R := Nat.ceil_le.mpr hxR
  unfold roughSaiasLambdaStieltjes
  symm
  exact roughSaiasLambdaStieltjesWithCutoff_eq_of_le
    hceilR hx hy (Nat.le_ceil x)















/-- In the active region, the pointwise continuous-Buchstab profile is a
fixed multiple of the ordinary Dickman continuous weight. -/
theorem roughSaiasContinuousBuchstabProfile_eq_mul_dickmanWeight
    {x s t : ℝ} (hx : 0 < x) (hs : 1 < s) (ht : 0 < t)
    (hactive : 1 ≤ Real.log (x / t) / Real.log s) :
    roughSaiasContinuousBuchstabProfile x s t =
      t * FriableAsymptotic.dickmanContinuousWeight (x / t) s := by
  have hspos : 0 < s := zero_lt_one.trans hs
  have hqpos : 0 < x / t := div_pos hx ht
  have hlogS : 0 < Real.log s := Real.log_pos hs
  have hquotient : (x / s) / t = (x / t) / s := by
    field_simp [hspos.ne', ht.ne']
  have hcoordinate :
      Real.log ((x / s) / t) / Real.log s =
        Real.log (x / t) / Real.log s - 1 := by
    rw [hquotient, Real.log_div hqpos.ne' hspos.ne']
    field_simp [hlogS.ne']
  have hdelayNonneg :
      0 ≤ Real.log (x / t) / Real.log s - 1 := by
    linarith
  unfold roughSaiasContinuousBuchstabProfile
    roughSaiasStieltjesDickmanProfile
    FriableAsymptotic.dickmanContinuousWeight
  rw [hcoordinate,
    roughSaiasZeroExtendedRho_of_nonneg hdelayNonneg]
  field_simp [hspos.ne', ht.ne', hlogS.ne']

theorem roughSaiasContinuousBuchstabProfile_eq_zero_of_lt
    {x s t : ℝ} (hx : 0 < x) (hs : 1 < s) (ht : 0 < t)
    (hxt : x / s < t) :
    roughSaiasContinuousBuchstabProfile x s t = 0 := by
  unfold roughSaiasContinuousBuchstabProfile
  rw [roughSaiasStieltjesDickmanProfile_eq_zero_of_lt
      (div_pos hx (zero_lt_one.trans hs)) hs ht hxt,
    zero_div]



/-- The continuous-Buchstab profile is interval integrable up to its birth
face.  At the top endpoint it agrees with the continuous Dickman weight;
this is why the non-strict active-coordinate lemma is used here. -/
theorem intervalIntegrable_roughSaiasContinuousBuchstabProfile_to_birth
    {x t y : ℝ} (hx : 0 < x) (ht : 0 < t)
    (hy : 1 < y) (hyq : y < x / t) :
    IntervalIntegrable (roughSaiasContinuousBuchstabProfile x · t)
      volume y (x / t) := by
  have hcontWeight : ContinuousOn
      (FriableAsymptotic.dickmanContinuousWeight (x / t))
      (Set.Icc y (x / t)) :=
    (FriableAsymptotic.continuousOn_dickmanContinuousWeight
      (x / t)).mono (fun s hs => by
        rw [Set.mem_Ioi]
        exact hy.trans_le hs.1)
  have hcont : ContinuousOn
      (fun s => t *
        FriableAsymptotic.dickmanContinuousWeight (x / t) s)
      (Set.Icc y (x / t)) :=
    continuousOn_const.mul hcontWeight
  have hbase := hcont.intervalIntegrable_of_Icc
    (μ := volume) hyq.le
  apply hbase.congr
  intro s hsU
  have hsI : s ∈ Set.Ioc y (x / t) := by
    simpa only [Set.uIoc_of_le hyq.le] using hsU
  have hsone : 1 < s := hy.trans hsI.1
  have hspos : 0 < s := zero_lt_one.trans hsone
  have hlogSQ : Real.log s ≤ Real.log (x / t) :=
    Real.log_le_log hspos hsI.2
  have hactive : 1 ≤ Real.log (x / t) / Real.log s :=
    (one_le_div (Real.log_pos hsone)).2 hlogSQ
  exact (roughSaiasContinuousBuchstabProfile_eq_mul_dickmanWeight
    hx hsone ht hactive).symm

/-- Past the birth face, the continuous-Buchstab profile is interval
integrable (and vanishes away from the excluded left endpoint). -/
theorem intervalIntegrable_roughSaiasContinuousBuchstabProfile_from_birth
    {x t z : ℝ} (hx : 0 < x) (ht : 0 < t)
    (hq1 : 1 < x / t) (hqz : x / t ≤ z) :
    IntervalIntegrable (roughSaiasContinuousBuchstabProfile x · t)
      volume (x / t) z := by
  have hzero : IntervalIntegrable (fun _ : ℝ => (0 : ℝ))
      volume (x / t) z := continuous_const.intervalIntegrable _ _
  apply hzero.congr
  intro s hsU
  have hsI : s ∈ Set.Ioc (x / t) z := by
    simpa only [Set.uIoc_of_le hqz] using hsU
  have hsone : 1 < s := hq1.trans hsI.1
  have hspos : 0 < s := zero_lt_one.trans hsone
  have hxsMul : x < s * t := (div_lt_iff₀ ht).mp hsI.1
  have hxs : x / s < t := by
    apply (div_lt_iff₀ hspos).2
    simpa only [mul_comm] using hxsMul
  exact (roughSaiasContinuousBuchstabProfile_eq_zero_of_lt
    hx hsone ht hxs).symm











/-- The pointwise continuous-Buchstab kernel is interval integrable on the
whole base interval.  This is the regularity input needed before lifting the
pointwise identity through the finite signed functional. -/
theorem intervalIntegrable_roughSaiasContinuousBuchstabProfile
    {x t y z : ℝ} (hx : 0 < x) (ht : 0 < t)
    (hy : 1 < y) (hyz : y ≤ z)
    (_hu6 : Real.log (x / t) / Real.log y ≤ 6) :
    IntervalIntegrable (roughSaiasContinuousBuchstabProfile x · t)
      volume y z := by
  by_cases hqy : x / t ≤ y
  · have hzero : IntervalIntegrable (fun _ : ℝ => (0 : ℝ))
        volume y z := continuous_const.intervalIntegrable _ _
    apply hzero.congr
    intro s hsU
    have hsI : s ∈ Set.Ioc y z := by
      simpa only [Set.uIoc_of_le hyz] using hsU
    have hsone : 1 < s := hy.trans hsI.1
    have hspos : 0 < s := zero_lt_one.trans hsone
    have hqs : x / t < s := hqy.trans_lt hsI.1
    have hxsMul : x < s * t := (div_lt_iff₀ ht).mp hqs
    have hxs : x / s < t := by
      apply (div_lt_iff₀ hspos).2
      simpa only [mul_comm] using hxsMul
    exact (roughSaiasContinuousBuchstabProfile_eq_zero_of_lt
      hx hsone ht hxs).symm
  · have hyq : y < x / t := lt_of_not_ge hqy
    by_cases hzq : z < x / t
    · have hqpos : 0 < x / t :=
          (zero_lt_one.trans hy).trans (hyz.trans_lt hzq)
      have hcontWeight : ContinuousOn
          (FriableAsymptotic.dickmanContinuousWeight (x / t))
          (Set.Icc y z) :=
        (FriableAsymptotic.continuousOn_dickmanContinuousWeight
          (x / t)).mono (fun s hs => by
            rw [Set.mem_Ioi]
            exact hy.trans_le hs.1)
      have hcont : ContinuousOn
          (fun s => t *
            FriableAsymptotic.dickmanContinuousWeight (x / t) s)
          (Set.Icc y z) :=
        continuousOn_const.mul hcontWeight
      have hbase := hcont.intervalIntegrable_of_Icc
        (μ := volume) hyz
      apply hbase.congr
      intro s hsU
      have hsI : s ∈ Set.Ioc y z := by
        simpa only [Set.uIoc_of_le hyz] using hsU
      have hsone : 1 < s := hy.trans hsI.1
      have hspos : 0 < s := zero_lt_one.trans hsone
      have hsQ : s < x / t := hsI.2.trans_lt hzq
      have hlogSQ : Real.log s < Real.log (x / t) :=
        Real.strictMonoOn_log hspos hqpos hsQ
      have hactive : 1 ≤ Real.log (x / t) / Real.log s :=
        ((one_lt_div (Real.log_pos hsone)).2 hlogSQ).le
      exact (roughSaiasContinuousBuchstabProfile_eq_mul_dickmanWeight
        hx hsone ht hactive).symm
    · exact
        (intervalIntegrable_roughSaiasContinuousBuchstabProfile_to_birth
          hx ht hy hyq).trans
          (intervalIntegrable_roughSaiasContinuousBuchstabProfile_from_birth
            hx ht (hy.trans hyq) (le_of_not_gt hzq))



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasSignedFractionalAbel -/
section


/-!
# Signed fractional correction and finite Abel decomposition for the Saias defect

This file goes one level below
`RoughSaiasReverseNormalFormDefectInvLogSqBound`.  It never assumes a bound
for that defect.  Instead it keeps the quotient fractional correction with
its sign, separates the reverse defect into a continuous normal-form prime
sum and that signed correction, and applies the project's existing finite
theta Abel identity to the continuous prime sum.

The resulting quantitative theorem assumes only a cumulative theta-error
bound.  Its right side is the explicit endpoint-plus-variation ledger for the
Saias theta weight.  Thus the remaining inverse-log-square problem is a
deterministic estimate for the displayed signed Abel center, not a renamed
copy of the original defect bound.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

/-! ## One quotient: retain the fractional correction with its sign -/







/-- Natural division is exactly the real quotient minus its fractional
part.  This includes the totalized `m=0` case. -/
theorem roughSaiasRealQuotient_sub_fract_eq_natQuotient
    (X m : ℕ) :
    (X : ℝ) / (m : ℝ) -
        Int.fract ((X : ℝ) / (m : ℝ)) =
      ((X / m : ℕ) : ℝ) := by
  rw [Int.self_sub_fract]
  rw [← natCast_floor_eq_intCast_floor (by positivity)]
  rw [Nat.floor_div_eq_div]

/-- Exact signed quotient correction.  No triangle inequality or absolute
value is used. -/
theorem roughSaiasSignedPrimeFloorCorrection_eq_fractional
    (X m : ℕ) :
    roughSaiasSignedPrimeFloorCorrection X m =
      roughSaiasSignedFractionalCorrectionTerm X m := by
  have hfloor := roughSaiasRealQuotient_sub_fract_eq_natQuotient X m
  unfold roughSaiasSignedPrimeFloorCorrection
    roughSaiasContinuousPrimeNormalForm
    roughSaiasSignedFractionalCorrectionTerm
    roughSaiasLambdaNormalForm roughSaiasNaturalMain
  linear_combination
    (roughSaiasG m
      (Real.log ((X : ℝ) / (m : ℝ)) / Real.log (m : ℝ))) * hfloor

/-! ## The reverse defect as continuous part plus signed correction -/







/-! ## Exact finite theta Abel identity -/

















/-! ## The floor/frac-paired natural theta weight -/





/-- Pointwise pairing: the continuous weight is the natural weight plus the
signed fractional correction. -/
theorem roughSaiasNormalFormThetaWeight_eq_natural_add_fractional
    (X m : ℕ) :
    roughSaiasNormalFormThetaWeight X m =
      roughSaiasNaturalQuotientThetaWeight X m +
        roughSaiasFractionalCorrectionThetaWeight X m := by
  unfold roughSaiasNormalFormThetaWeight
    roughSaiasNaturalQuotientThetaWeight
    roughSaiasFractionalCorrectionThetaWeight
  rw [← roughSaiasSignedPrimeFloorCorrection_eq_fractional]
  unfold
    roughSaiasSignedPrimeFloorCorrection
  ring





















/-! ## Quantitative theta transfer, without a defect-bound premise -/













/-! ## Closed fourth-power theta specialization -/













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasStieltjesNormalForm -/
section


/-!
# Identification of the finite signed functional with the Saias normal form

This file performs the finite integration-by-parts calculation that was
deliberately absent from `RoughSaiasNormalization`.  The atom part is
handled by the corner-safe right-derivative Abel theorem.  Its density term
cancels the quotient-rule part of that derivative before any estimate is
taken.  What remains splits exactly as

* a smooth Dickman FTC term, and
* the signed base-free fractional correction already formalized in
  `RoughSaiasBaseChange`.

Thus the explicit atom-minus-density functional is identified with the
existing normal form at a positive natural endpoint without assuming any
defect or endpoint estimate.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## The exact density cancellation -/







theorem roughSaiasNatFloor_cast_eq_sub_fract
    {t : ℝ} (ht : 0 ≤ t) :
    (((⌊t⌋₊ : ℕ) : ℝ)) = t - Int.fract t := by
  rw [Int.self_sub_fract,
    ← natCast_floor_eq_intCast_floor ht]





theorem roughSaiasPositiveIncrement_prefix (N : ℕ) :
    (∑ k ∈ Finset.Icc 0 N,
      FriableAsymptotic.positiveIncrement k) = (N : ℝ) := by
  have hfin : Finset.Icc 0 N = Finset.range (N + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  rw [hfin]
  exact FriableAsymptotic.sum_range_positiveIncrement N







/-! ## Evaluation of the smooth part -/

/-- Multiplying the Abel test by `t/x` recovers `rho` and transfers its
corner-safe right derivative to the logarithmic coordinate. -/
theorem hasDerivWithinAt_roughSaiasRhoCoordinate_right
    {x y t : ℝ} (hy : 1 < y) (ht1 : 1 ≤ t) (htx : t ≤ x)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    HasDerivWithinAt
      (fun s : ℝ ↦ rho (roughSaiasStieltjesCoordinate x y s))
      (roughSaiasOpenFaceDickmanDerivative
          (roughSaiasStieltjesCoordinate x y t) *
        (-1 / (t * Real.log y)))
      (Set.Ioi t) t := by
  have htpos : 0 < t := zero_lt_one.trans_le ht1
  have ht0 : t ≠ 0 := htpos.ne'
  have hxpos : 0 < x := htpos.trans_le htx
  have hx0 : x ≠ 0 := hxpos.ne'
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  have htest := hasDerivWithinAt_roughSaiasStieltjesTest_right
    hy ht1 htx hu5
  have hprod := (hasDerivAt_id t).hasDerivWithinAt.mul htest
  have hquot := hprod.div_const x
  have heq :
      (fun s : ℝ ↦ rho (roughSaiasStieltjesCoordinate x y s))
        =ᶠ[nhdsWithin t (Set.Ioi t)]
      (fun s : ℝ ↦ s * roughSaiasStieltjesTest x y s / x) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s := htpos.trans hs
    unfold roughSaiasStieltjesTest
    field_simp [hspos.ne', hx0]
  have hvalue :
      rho (roughSaiasStieltjesCoordinate x y t) =
        t * roughSaiasStieltjesTest x y t / x := by
    unfold roughSaiasStieltjesTest
    field_simp [ht0, hx0]
  have hcongr := hquot.congr_of_eventuallyEq heq hvalue
  convert hcongr using 1
  simp only [id_eq]
  unfold roughSaiasStieltjesTest
    roughSaiasStieltjesTestRightDerivative
  field_simp [ht0, hx0, hlogy]
  ring

theorem continuousOn_roughSaiasRhoCoordinate
    {x y A B : ℝ} (_hy : 1 < y) (hA : 0 < A) :
    ContinuousOn
      (fun t : ℝ ↦ rho (roughSaiasStieltjesCoordinate x y t))
      (Set.Icc A B) := by
  intro t ht
  have ht0 : t ≠ 0 := (hA.trans_le ht.1).ne'
  have hcoord : ContinuousAt (roughSaiasStieltjesCoordinate x y) t := by
    unfold roughSaiasStieltjesCoordinate
    exact (continuousAt_const.sub (Real.continuousAt_log ht0)).div_const _
  exact (continuous_rho.continuousAt.comp hcoord).continuousWithinAt









/-! ## Identification of the signed fractional part -/











/-! ## Final natural-endpoint identification -/





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasRealStieltjesNormalForm -/
section


/-!
# Real-endpoint identification of the Stieltjes and Saias normal forms

The natural-endpoint calculation in `RoughSaiasStieltjesNormalForm` is
extended here to every real outer endpoint `x ≥ 1`.  Abel summation now
produces `floor x`, and the elementary identity

`floor x = x - fract x`

supplies exactly the terminal sawtooth in `roughSaiasLambdaNormalForm`.
This real version is needed in continuous Buchstab at the inner endpoints
`x/s`.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## Real floor-correction kernels -/







theorem roughSaiasRealStieltjesFloorCorrection_eq_smooth_sub_fractional
    {x y t : ℝ} (ht : 0 < t) (hy : 1 < y) :
    roughSaiasRealStieltjesFloorCorrection x y t =
      roughSaiasRealStieltjesSmoothCorrection x y t -
        roughSaiasRealStieltjesFractionalCorrection x y t := by
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  have ht0 : t ≠ 0 := ht.ne'
  unfold roughSaiasRealStieltjesFloorCorrection
    roughSaiasRealStieltjesSmoothCorrection
    roughSaiasRealStieltjesFractionalCorrection
  rw [roughSaiasNatFloor_cast_eq_sub_fract ht.le]
  field_simp [ht0, hlogy]

theorem roughSaiasRealStieltjesDerivativeFloor_add_density
    {x y t : ℝ} (hx : 0 < x) (hy : 1 < y)
    (ht : 0 < t) (htx : t ≤ x) :
    roughSaiasStieltjesTestRightDerivative x y t *
          (((⌊t⌋₊ : ℕ) : ℝ)) +
        roughSaiasStieltjesDickmanProfile x y t *
          roughSaiasFloorDensity t =
      -roughSaiasRealStieltjesFloorCorrection x y t := by
  have ht0 : t ≠ 0 := ht.ne'
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  rw [roughSaiasStieltjesDickmanProfile_eq_mul_test hx hy ht htx]
  unfold roughSaiasStieltjesTestRightDerivative
    roughSaiasStieltjesTest roughSaiasFloorDensity
    roughSaiasRealStieltjesFloorCorrection
  field_simp [ht0, hlogy]
  ring

/-! ## Real compact integrability -/

theorem integrableOn_roughSaiasRealStieltjesTestRightDerivative
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    IntegrableOn (roughSaiasStieltjesTestRightDerivative x y)
      (Set.Icc (1 : ℝ) x) := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hC : 0 ≤ x * (1 / Real.log y + 1) := by
    have hlogy : 0 < Real.log y := Real.log_pos hy
    positivity
  have hconst : IntervalIntegrable
      (fun _ : ℝ ↦ x * (1 / Real.log y + 1))
      volume (1 : ℝ) x :=
    continuous_const.intervalIntegrable _ _
  have hint : IntervalIntegrable
      (roughSaiasStieltjesTestRightDerivative x y)
      volume (1 : ℝ) x := by
    apply hconst.mono_fun'
      (measurable_roughSaiasStieltjesTestRightDerivative x y).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have htI : t ∈ Set.Icc (1 : ℝ) x := by
      simpa only [Set.uIcc_of_le hx1] using Set.uIoc_subset_uIcc ht
    rw [Real.norm_eq_abs]
    exact roughSaiasStieltjesTestRightDerivative_abs_le
      hy htI.1 htI.2 hu5
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hx1).mp hint

theorem integrableOn_roughSaiasRealStieltjesDerivative_mul_floor
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    IntegrableOn
      (fun t : ℝ ↦ roughSaiasStieltjesTestRightDerivative x y t *
        (((⌊t⌋₊ : ℕ) : ℝ)))
      (Set.Ioc (1 : ℝ) x) := by
  have hint := integrableOn_roughSaiasRealStieltjesTestRightDerivative
    hx1 hy hu5
  have hmul := integrableOn_mul_sum_Icc
    FriableAsymptotic.positiveIncrement (a := (1 : ℝ))
      (b := x) (m := 0) (by norm_num) hint
  have hmul' := hmul.mono_set Set.Ioc_subset_Icc_self
  simpa only [roughSaiasPositiveIncrement_prefix] using hmul'

theorem integrableOn_roughSaiasRealStieltjesProfile_mul_floorDensity
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    IntegrableOn
      (fun t : ℝ ↦ roughSaiasStieltjesDickmanProfile x y t *
        roughSaiasFloorDensity t)
      (Set.Ioc (1 : ℝ) x) := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hx0 : 0 ≤ x := hx.le
  have hmeas : Measurable (fun t : ℝ ↦
      roughSaiasStieltjesDickmanProfile x y t *
        roughSaiasFloorDensity t) :=
    (measurable_roughSaiasStieltjesDickmanProfile x y).mul
      measurable_roughSaiasFloorDensity
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ x)
      volume (1 : ℝ) x :=
    continuous_const.intervalIntegrable _ _
  have hint : IntervalIntegrable (fun t : ℝ ↦
      roughSaiasStieltjesDickmanProfile x y t *
        roughSaiasFloorDensity t) volume (1 : ℝ) x := by
    apply hconst.mono_fun' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have htI : t ∈ Set.Icc (1 : ℝ) x := by
      simpa only [Set.uIcc_of_le hx1] using Set.uIoc_subset_uIcc ht
    have htpos : 0 < t := zero_lt_one.trans_le htI.1
    have hcoord := roughSaiasStieltjesCoordinate_mem hy htI.1 htI.2
    have hcoordLog5 : Real.log (x / t) / Real.log y ≤ 5 := by
      rw [← roughSaiasStieltjesCoordinate_eq_log_div hx htpos]
      exact hcoord.2.trans hu5
    have hrho := roughSaiasZeroExtendedRho_mem_unitInterval hcoordLog5
    have hprofile0 : 0 ≤ roughSaiasStieltjesDickmanProfile x y t := by
      unfold roughSaiasStieltjesDickmanProfile
      exact mul_nonneg hx0 hrho.1
    have hprofilex : roughSaiasStieltjesDickmanProfile x y t ≤ x := by
      unfold roughSaiasStieltjesDickmanProfile
      exact (mul_le_mul_of_nonneg_left hrho.2 hx0).trans_eq (mul_one _)
    have hfloor0 : (0 : ℝ) ≤ (((⌊t⌋₊ : ℕ) : ℝ)) := by positivity
    have hfloort : (((⌊t⌋₊ : ℕ) : ℝ)) ≤ t := Nat.floor_le htpos.le
    have ht2 : 0 < t ^ 2 := sq_pos_of_pos htpos
    have hdensity0 : 0 ≤ roughSaiasFloorDensity t := by
      unfold roughSaiasFloorDensity
      exact div_nonneg hfloor0 ht2.le
    have hdensity1 : roughSaiasFloorDensity t ≤ 1 := by
      unfold roughSaiasFloorDensity
      apply (div_le_one ht2).2
      have hquad : 0 ≤ t * (t - 1) :=
        mul_nonneg htpos.le (sub_nonneg.mpr htI.1)
      exact hfloort.trans (by nlinarith)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hprofile0 hdensity0)]
    calc
      roughSaiasStieltjesDickmanProfile x y t * roughSaiasFloorDensity t ≤
          roughSaiasStieltjesDickmanProfile x y t * 1 :=
        mul_le_mul_of_nonneg_left hdensity1 hprofile0
      _ ≤ x * 1 := mul_le_mul_of_nonneg_right hprofilex (by norm_num)
      _ = x := mul_one _
  have hintIcc :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx1).mp hint
  exact hintIcc.mono_set Set.Ioc_subset_Icc_self

/-! ## Abel summation at a real endpoint -/

theorem roughSaiasStieltjesAtomPart_ceil_profile_eq_floor_test
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y) :
    roughSaiasStieltjesAtomPart ⌈x⌉₊
        (roughSaiasStieltjesDickmanProfile x y) =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        roughSaiasStieltjesTest x y (n : ℝ) := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hfloorceil : ⌊x⌋₊ ≤ ⌈x⌉₊ := by
    have h := Nat.floor_le_floor (Nat.le_ceil x)
    simpa using h
  have hsubset : Finset.Icc 1 ⌊x⌋₊ ⊆ Finset.Icc 1 ⌈x⌉₊ := by
    intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans hfloorceil⟩
  have hsum :
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          roughSaiasStieltjesDickmanProfile x y (n : ℝ) / (n : ℝ)) =
        ∑ n ∈ Finset.Icc 1 ⌈x⌉₊,
          roughSaiasStieltjesDickmanProfile x y (n : ℝ) / (n : ℝ) := by
    apply Finset.sum_subset hsubset
    intro n hnceil hnfloor
    have hnData := Finset.mem_Icc.mp hnceil
    have hfloorlt : ⌊x⌋₊ < n := by
      by_contra hnot
      exact hnfloor (Finset.mem_Icc.mpr
        ⟨hnData.1, le_of_not_gt hnot⟩)
    have hxt : x < (n : ℝ) :=
      (Nat.floor_lt' (by omega)).mp hfloorlt
    rw [roughSaiasStieltjesDickmanProfile_eq_zero_of_lt
      hx hy (by exact_mod_cast (show 0 < n by omega)) hxt, zero_div]
  unfold roughSaiasStieltjesAtomPart
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnData := Finset.mem_Icc.mp hn
  have hnx : (n : ℝ) ≤ x :=
    (by exact_mod_cast hnData.2 : (n : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans
      (Nat.floor_le hx.le)
  exact roughSaiasStieltjesDickmanProfile_div_eq_test
    hx hy (by exact_mod_cast (show 0 < n by omega)) hnx

theorem roughSaiasStieltjesTest_floor_sum_eq_endpoint_sub_integral
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        roughSaiasStieltjesTest x y (n : ℝ)) =
      (⌊x⌋₊ : ℝ) -
        ∫ t in Set.Ioc (1 : ℝ) x,
          roughSaiasStieltjesTestRightDerivative x y t *
            (((⌊t⌋₊ : ℕ) : ℝ)) := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hcont := continuousOn_roughSaiasStieltjesTest
    (x := x) (y := y) (A := (1 : ℝ)) (B := x) hy (by norm_num)
  have hright := roughSaiasStieltjesTest_hasRightDerivOn
    (x := x) (y := y) (R := x) hy hx1 le_rfl hu5
  have hint := integrableOn_roughSaiasRealStieltjesTestRightDerivative
    hx1 hy hu5
  have hAbel :=
    RoughSaiasRightAbel.sum_mul_eq_sub_sub_integral_mul_right
      FriableAsymptotic.positiveIncrement
      (a := (1 : ℝ)) (b := x) (by norm_num) hx1
      hcont hright hint
  have hweighted :
      (∑ k ∈ Finset.Ioc 1 ⌊x⌋₊,
          roughSaiasStieltjesTest x y (k : ℝ) *
            FriableAsymptotic.positiveIncrement k) =
        ∑ k ∈ Finset.Ioc 1 ⌊x⌋₊,
          roughSaiasStieltjesTest x y (k : ℝ) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : k ≠ 0 := by
      rw [Finset.mem_Ioc] at hk
      omega
    simp [FriableAsymptotic.positiveIncrement, hk0]
  have hfloor1 : 1 ≤ ⌊x⌋₊ := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using hx1
  simp only [Nat.floor_one] at hAbel
  rw [hweighted] at hAbel
  simp_rw [roughSaiasPositiveIncrement_prefix] at hAbel
  rw [roughSaiasStieltjesTest_self hx.ne'] at hAbel
  nth_rewrite 1 [Finset.Icc_eq_cons_Ioc hfloor1]
  rw [Finset.sum_cons, hAbel]
  ring

theorem roughSaiasStieltjesDensityPart_ceil_profile_eq_realCap
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y) :
    roughSaiasStieltjesDensityPart ⌈x⌉₊
        (roughSaiasStieltjesDickmanProfile x y) =
      ∫ t in Set.Ioc (1 : ℝ) x,
        roughSaiasStieltjesDickmanProfile x y t *
          roughSaiasFloorDensity t := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hsubset : Set.Ioc (1 : ℝ) x ⊆
      Set.Ioc (1 : ℝ) (⌈x⌉₊ : ℝ) := by
    rintro t ⟨ht1, htx⟩
    exact ⟨ht1, htx.trans (Nat.le_ceil x)⟩
  unfold roughSaiasStieltjesDensityPart
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
    measurableSet_Ioc hsubset
  intro t ht
  have hxt : x < t := by
    by_contra hnot
    exact ht.2 ⟨ht.1.1, le_of_not_gt hnot⟩
  rw [roughSaiasStieltjesDickmanProfile_eq_zero_of_lt
    hx hy (zero_lt_one.trans ht.1.1) hxt, zero_mul]

theorem roughSaiasLambdaStieltjes_eq_floor_add_floorCorrection
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    roughSaiasLambdaStieltjes x y =
      (⌊x⌋₊ : ℝ) +
        ∫ t in Set.Ioc (1 : ℝ) x,
          roughSaiasRealStieltjesFloorCorrection x y t := by
  have hderiv := integrableOn_roughSaiasRealStieltjesDerivative_mul_floor
    hx1 hy hu5
  have hdensity :=
    integrableOn_roughSaiasRealStieltjesProfile_mul_floorDensity
      hx1 hy hu5
  unfold roughSaiasLambdaStieltjes roughSaiasLambdaStieltjesWithCutoff
    roughSaiasFiniteStieltjesFunctional
  rw [roughSaiasStieltjesAtomPart_ceil_profile_eq_floor_test hx1 hy,
    roughSaiasStieltjesTest_floor_sum_eq_endpoint_sub_integral hx1 hy hu5,
    roughSaiasStieltjesDensityPart_ceil_profile_eq_realCap hx1 hy]
  have hadd := MeasureTheory.integral_add hderiv hdensity
  have hpoint :
      (∫ t in Set.Ioc (1 : ℝ) x,
          (roughSaiasStieltjesTestRightDerivative x y t *
              (((⌊t⌋₊ : ℕ) : ℝ)) +
            roughSaiasStieltjesDickmanProfile x y t *
              roughSaiasFloorDensity t)) =
        ∫ t in Set.Ioc (1 : ℝ) x,
          -roughSaiasRealStieltjesFloorCorrection x y t := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact roughSaiasRealStieltjesDerivativeFloor_add_density
      (zero_lt_one.trans_le hx1) hy (zero_lt_one.trans ht.1) ht.2
  calc
    (⌊x⌋₊ : ℝ) -
          (∫ t in Set.Ioc (1 : ℝ) x,
            roughSaiasStieltjesTestRightDerivative x y t *
              (((⌊t⌋₊ : ℕ) : ℝ))) -
          (∫ t in Set.Ioc (1 : ℝ) x,
            roughSaiasStieltjesDickmanProfile x y t *
              roughSaiasFloorDensity t) =
        (⌊x⌋₊ : ℝ) -
          ((∫ t in Set.Ioc (1 : ℝ) x,
              roughSaiasStieltjesTestRightDerivative x y t *
                (((⌊t⌋₊ : ℕ) : ℝ))) +
            (∫ t in Set.Ioc (1 : ℝ) x,
              roughSaiasStieltjesDickmanProfile x y t *
                roughSaiasFloorDensity t)) := by ring
    _ = (⌊x⌋₊ : ℝ) -
          ∫ t in Set.Ioc (1 : ℝ) x,
            (roughSaiasStieltjesTestRightDerivative x y t *
                (((⌊t⌋₊ : ℕ) : ℝ)) +
              roughSaiasStieltjesDickmanProfile x y t *
                roughSaiasFloorDensity t) := by rw [hadd]
    _ = (⌊x⌋₊ : ℝ) -
          ∫ t in Set.Ioc (1 : ℝ) x,
            -roughSaiasRealStieltjesFloorCorrection x y t := by rw [hpoint]
    _ = (⌊x⌋₊ : ℝ) +
          ∫ t in Set.Ioc (1 : ℝ) x,
            roughSaiasRealStieltjesFloorCorrection x y t := by
      rw [MeasureTheory.integral_neg]
      ring

/-! ## Smooth real contribution -/

theorem integrableOn_roughSaiasRealRhoCoordinateRightDerivative
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    IntegrableOn
      (fun t : ℝ ↦
        roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate x y t) *
          (-1 / (t * Real.log y)))
      (Set.Icc (1 : ℝ) x) := by
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hmeas : Measurable (fun t : ℝ ↦
      roughSaiasOpenFaceDickmanDerivative
          (roughSaiasStieltjesCoordinate x y t) *
        (-1 / (t * Real.log y))) :=
    (measurable_roughSaiasOpenFaceDickmanDerivative.comp
      (measurable_roughSaiasStieltjesCoordinate x y)).mul
        (measurable_const.div (measurable_id.mul measurable_const))
  have hconst : IntervalIntegrable
      (fun _ : ℝ ↦ 1 / Real.log y) volume (1 : ℝ) x :=
    continuous_const.intervalIntegrable _ _
  have hint : IntervalIntegrable (fun t : ℝ ↦
      roughSaiasOpenFaceDickmanDerivative
          (roughSaiasStieltjesCoordinate x y t) *
        (-1 / (t * Real.log y))) volume (1 : ℝ) x := by
    apply hconst.mono_fun' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have htI : t ∈ Set.Icc (1 : ℝ) x := by
      simpa only [Set.uIcc_of_le hx1] using Set.uIoc_subset_uIcc ht
    have htpos : 0 < t := zero_lt_one.trans_le htI.1
    have hcoord := roughSaiasStieltjesCoordinate_mem hy htI.1 htI.2
    have hD := roughSaiasOpenFaceDickmanDerivative_abs_le_one
      (hcoord.2.trans hu5)
    have hdenom : 0 < t * Real.log y := mul_pos htpos hlogy
    have hinv : 1 / (t * Real.log y) ≤ 1 / Real.log y := by
      apply one_div_le_one_div_of_le hlogy
      nlinarith [mul_le_mul_of_nonneg_right htI.1 hlogy.le]
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_neg, abs_one,
      abs_of_pos hdenom]
    calc
      |roughSaiasOpenFaceDickmanDerivative
          (roughSaiasStieltjesCoordinate x y t)| *
          (1 / (t * Real.log y)) ≤
        1 * (1 / (t * Real.log y)) :=
          mul_le_mul_of_nonneg_right hD (by positivity)
      _ ≤ 1 * (1 / Real.log y) :=
        mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 1 / Real.log y := one_mul _
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hx1).mp hint

theorem integral_roughSaiasRealRhoCoordinateRightDerivative
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    (∫ t in (1 : ℝ)..x,
        roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate x y t) *
          (-1 / (t * Real.log y))) =
      1 - rho (Real.log x / Real.log y) := by
  have hcont := continuousOn_roughSaiasRhoCoordinate
    (x := x) (y := y) (A := (1 : ℝ)) (B := x) hy (by norm_num)
  have hright : ∀ t ∈ Set.Ioo (1 : ℝ) x,
      HasDerivWithinAt
        (fun s : ℝ ↦ rho (roughSaiasStieltjesCoordinate x y s))
        (roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate x y t) *
          (-1 / (t * Real.log y)))
        (Set.Ioi t) t := by
    intro t ht
    exact hasDerivWithinAt_roughSaiasRhoCoordinate_right
      hy ht.1.le ht.2.le hu5
  have hintIcc := integrableOn_roughSaiasRealRhoCoordinateRightDerivative
    hx1 hy hu5
  have hint : IntervalIntegrable
      (fun t : ℝ ↦
        roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate x y t) *
          (-1 / (t * Real.log y)))
      volume (1 : ℝ) x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx1).mpr hintIcc
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    hx1 hcont hright hint
  simpa [roughSaiasStieltjesCoordinate] using hftc

theorem integral_roughSaiasRealStieltjesSmoothCorrection
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    (∫ t in Set.Ioc (1 : ℝ) x,
        roughSaiasRealStieltjesSmoothCorrection x y t) =
      x * (rho (Real.log x / Real.log y) - 1) := by
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  rw [← intervalIntegral.integral_of_le hx1]
  have heq :
      (∫ t in (1 : ℝ)..x,
          roughSaiasRealStieltjesSmoothCorrection x y t) =
        ∫ t in (1 : ℝ)..x,
          (-x) *
            (roughSaiasOpenFaceDickmanDerivative
                (roughSaiasStieltjesCoordinate x y t) *
              (-1 / (t * Real.log y))) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htI : t ∈ Set.Icc (1 : ℝ) x := by
      simpa [Set.uIcc_of_le hx1] using ht
    have ht0 : t ≠ 0 := (zero_lt_one.trans_le htI.1).ne'
    unfold roughSaiasRealStieltjesSmoothCorrection
    field_simp [ht0, hlogy]
  rw [heq, intervalIntegral.integral_const_mul,
    integral_roughSaiasRealRhoCoordinateRightDerivative hx1 hy hu5]
  ring

theorem integrableOn_roughSaiasRealStieltjesSmoothCorrection
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    IntegrableOn (roughSaiasRealStieltjesSmoothCorrection x y)
      (Set.Ioc (1 : ℝ) x) := by
  have hbase :=
    (integrableOn_roughSaiasRealRhoCoordinateRightDerivative
      hx1 hy hu5).mono_set Set.Ioc_subset_Icc_self
  have hmul := hbase.const_mul (-x)
  apply IntegrableOn.congr_fun_ae hmul
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : t ≠ 0 := (zero_lt_one.trans ht.1).ne'
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  unfold roughSaiasRealStieltjesSmoothCorrection
  field_simp [ht0, hlogy]

/-! ## Fractional real contribution -/







/-! ## Exact real-endpoint identification -/



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

theorem roughSaiasFullyRealFractionalIntegral_eq_baseFree
    {x y : ℝ} (hy : 1 < y) :
    (∫ v in (0 : ℝ)..5,
        roughSaiasDickmanDerivative
            (Real.log x / Real.log y - v) *
          roughSaiasFullyRealFractionalWeight y v) =
      roughSaiasFullyRealBaseFreeFractionalIntegral x y := by
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
  have hchange :
      (∫ t in f '' Set.Icc (0 : ℝ) 5,
          roughSaiasFullyRealBaseFreeFractionalKernel x y t) =
        ∫ v in Set.Icc (0 : ℝ) 5,
          f' v • roughSaiasFullyRealBaseFreeFractionalKernel x y (f v) :=
    MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn
      measurableSet_Icc hfderiv hfmono
        (roughSaiasFullyRealBaseFreeFractionalKernel x y)
  have hpoint (v : ℝ) :
      f' v • roughSaiasFullyRealBaseFreeFractionalKernel x y (f v) =
        roughSaiasDickmanDerivative (Real.log x / Real.log y - v) *
          roughSaiasFullyRealFractionalWeight y v := by
    simpa [f, f', smul_eq_mul] using
      roughSaiasFullyRealBaseFreeKernel_rpow_mul_jacobian
        (x := x) hy v
  have hu : (1 : ℝ) ≤ y ^ (5 : ℝ) :=
    Real.one_le_rpow hy.le (by norm_num)
  unfold roughSaiasFullyRealBaseFreeFractionalIntegral
  calc
    (∫ v in (0 : ℝ)..5,
        roughSaiasDickmanDerivative (Real.log x / Real.log y - v) *
          roughSaiasFullyRealFractionalWeight y v) =
        ∫ v in Set.Icc (0 : ℝ) 5,
          roughSaiasDickmanDerivative (Real.log x / Real.log y - v) *
            roughSaiasFullyRealFractionalWeight y v := by
      rw [intervalIntegral.integral_of_le (by norm_num),
        MeasureTheory.integral_Icc_eq_integral_Ioc]
    _ = ∫ v in Set.Icc (0 : ℝ) 5,
          f' v • roughSaiasFullyRealBaseFreeFractionalKernel x y (f v) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro v _hv
      exact (hpoint v).symm
    _ = ∫ t in Set.Icc (1 : ℝ) (y ^ (5 : ℝ)),
          roughSaiasFullyRealBaseFreeFractionalKernel x y t := by
      rw [← hfimage]
      exact hchange.symm
    _ = ∫ t in (1 : ℝ)..y ^ (5 : ℝ),
          roughSaiasFullyRealBaseFreeFractionalKernel x y t := by
      rw [intervalIntegral.integral_of_le hu,
        MeasureTheory.integral_Icc_eq_integral_Ioc]

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

theorem roughSaiasFullyRealBaseFreeIntegral_eq_realCap
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    roughSaiasFullyRealBaseFreeFractionalIntegral x y =
      ∫ t in (1 : ℝ)..x,
        roughSaiasFullyRealBaseFreeFractionalKernel x y t := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hcap := roughSaiasFullyReal_le_rpow_five hx hy hu5
  have hxmem : x ∈ Set.uIcc (1 : ℝ) (y ^ (5 : ℝ)) := by
    rw [Set.uIcc_of_le (hx1.trans hcap)]
    exact ⟨hx1, hcap⟩
  have hint := roughSaiasFullyRealBaseFreeKernel_intervalIntegrable
    (x := x) hy hu5
  have hparts := (IntervalIntegrable.trans_iff hxmem).mp hint
  have hdivlt : x / y < x := div_lt_self hx hy
  have htail :
      (∫ t in x..y ^ (5 : ℝ),
          roughSaiasFullyRealBaseFreeFractionalKernel x y t) = 0 := by
    calc
      _ = ∫ _t in x..y ^ (5 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have htI : t ∈ Set.Icc x (y ^ (5 : ℝ)) := by
          rw [Set.uIcc_of_le hcap] at ht
          exact ht
        exact roughSaiasFullyRealBaseFreeKernel_eq_zero_of_div_lt
          hx hy (hdivlt.trans_le htI.1)
      _ = 0 := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hparts.1 hparts.2
  unfold roughSaiasFullyRealBaseFreeFractionalIntegral
  rw [← hsplit, htail, add_zero]

theorem roughSaiasFullyRealG_eq_rho_sub_baseFree
    {x y : ℝ} (hy : 1 < y) :
    roughSaiasFullyRealG y (Real.log x / Real.log y) =
      rho (Real.log x / Real.log y) -
        roughSaiasFullyRealBaseFreeFractionalIntegral x y := by
  unfold roughSaiasFullyRealG
  rw [roughSaiasFullyRealFractionalIntegral_eq_baseFree hy]

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

theorem roughSaiasRealStieltjesFractionalCorrection_eq_fullyRealBaseFree_of_ne
    {x y t : ℝ} (hx : 0 < x) (hy : 1 < y)
    (ht : 0 < t) (hne : t ≠ x / y) :
    roughSaiasRealStieltjesFractionalCorrection x y t =
      x * roughSaiasFullyRealBaseFreeFractionalKernel x y t := by
  have hypos : 0 < y := zero_lt_one.trans hy
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  have hcoordNe : roughSaiasStieltjesCoordinate x y t ≠ 1 := by
    intro hcoord
    have hlogEq : Real.log x - Real.log t = Real.log y := by
      unfold roughSaiasStieltjesCoordinate at hcoord
      field_simp [hlogy] at hcoord
      linarith
    have hlogDiv : Real.log (x / y) = Real.log x - Real.log y := by
      rw [Real.log_div hx.ne' hypos.ne']
    have hlogs : Real.log t = Real.log (x / y) := by
      rw [hlogDiv]
      linarith
    have hexp := congrArg Real.exp hlogs
    rw [Real.exp_log ht, Real.exp_log (div_pos hx hypos)] at hexp
    exact hne hexp
  unfold roughSaiasRealStieltjesFractionalCorrection
    roughSaiasFullyRealBaseFreeFractionalKernel
  rw [roughSaiasOpenFaceDickmanDerivative_eq_roughSaias hcoordNe]
  unfold roughSaiasStieltjesCoordinate
  field_simp [ht.ne', hlogy]

theorem integrableOn_roughSaiasFullyRealStieltjesFractionalCorrection
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    IntegrableOn (roughSaiasRealStieltjesFractionalCorrection x y)
      (Set.Ioc (1 : ℝ) x) := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hcap := roughSaiasFullyReal_le_rpow_five hx hy hu5
  have hfull := roughSaiasFullyRealBaseFreeKernel_intervalIntegrable
    (x := x) hy hu5
  have hcapInt : IntervalIntegrable
      (roughSaiasFullyRealBaseFreeFractionalKernel x y)
      volume (1 : ℝ) x := by
    apply hfull.mono_set
    rw [Set.uIcc_of_le hx1, Set.uIcc_of_le (hx1.trans hcap)]
    exact Set.Icc_subset_Icc le_rfl hcap
  have hbaseIcc :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx1).mp hcapInt
  have hbaseIccMul : IntegrableOn
      (fun t : ℝ => x * roughSaiasFullyRealBaseFreeFractionalKernel x y t)
      (Set.Icc (1 : ℝ) x) :=
    hbaseIcc.const_mul x
  have hbase := hbaseIccMul.mono_set Set.Ioc_subset_Icc_self
  apply IntegrableOn.congr_fun_ae hbase
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [((volume : Measure ℝ).ae_ne (x / y))] with t hne ht
  exact (roughSaiasRealStieltjesFractionalCorrection_eq_fullyRealBaseFree_of_ne
    hx hy (zero_lt_one.trans ht.1) hne).symm

theorem integral_roughSaiasFullyRealStieltjesFractionalCorrection
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    (∫ t in Set.Ioc (1 : ℝ) x,
        roughSaiasRealStieltjesFractionalCorrection x y t) =
      x * roughSaiasFullyRealBaseFreeFractionalIntegral x y := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  rw [← intervalIntegral.integral_of_le hx1]
  have heq :
      (∫ t in (1 : ℝ)..x,
          roughSaiasRealStieltjesFractionalCorrection x y t) =
        ∫ t in (1 : ℝ)..x,
          x * roughSaiasFullyRealBaseFreeFractionalKernel x y t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [((volume : Measure ℝ).ae_ne (x / y))]
      with t hne ht
    have htI : t ∈ Set.Icc (1 : ℝ) x := by
      simpa only [Set.uIcc_of_le hx1] using Set.uIoc_subset_uIcc ht
    exact roughSaiasRealStieltjesFractionalCorrection_eq_fullyRealBaseFree_of_ne
      hx hy (zero_lt_one.trans_le htI.1) hne
  rw [heq, intervalIntegral.integral_const_mul,
    ← roughSaiasFullyRealBaseFreeIntegral_eq_realCap hx1 hy hu5]

/-- Every inner real-base Lambda produced by continuous Buchstab is the
literal fully real Saias normal form. -/
theorem roughSaiasLambdaStieltjes_eq_fullyRealNormalForm
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    roughSaiasLambdaStieltjes x y =
      roughSaiasFullyRealLambdaNormalForm x y := by
  have hsmooth := integrableOn_roughSaiasRealStieltjesSmoothCorrection
    hx1 hy hu5
  have hfract :=
    integrableOn_roughSaiasFullyRealStieltjesFractionalCorrection
      hx1 hy hu5
  have hsplit := MeasureTheory.integral_sub hsmooth hfract
  rw [roughSaiasLambdaStieltjes_eq_floor_add_floorCorrection
    hx1 hy hu5]
  have hpoint :
      (∫ t in Set.Ioc (1 : ℝ) x,
          roughSaiasRealStieltjesFloorCorrection x y t) =
        ∫ t in Set.Ioc (1 : ℝ) x,
          (roughSaiasRealStieltjesSmoothCorrection x y t -
            roughSaiasRealStieltjesFractionalCorrection x y t) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact roughSaiasRealStieltjesFloorCorrection_eq_smooth_sub_fractional
      (zero_lt_one.trans ht.1) hy
  rw [hpoint, hsplit,
    integral_roughSaiasRealStieltjesSmoothCorrection hx1 hy hu5,
    integral_roughSaiasFullyRealStieltjesFractionalCorrection hx1 hy hu5]
  unfold roughSaiasFullyRealLambdaNormalForm
  rw [roughSaiasFullyRealG_eq_rho_sub_baseFree hy,
    roughSaiasNatFloor_cast_eq_sub_fract
      (zero_lt_one.trans_le hx1).le]
  ring



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasFunctionalBuchstab -/
section


/-!
# Lifting pointwise continuous Buchstab through the finite signed functional

The pointwise identity in `RoughSaiasContinuousBuchstab` is now lifted
through the finite atom-minus-density functional.  The finite atomic swap is
proved unconditionally.  The density swap is stated with its exact compact
Fubini datum; that datum is ordinary product integrability of an explicit
bounded measurable kernel, not an endpoint or defect estimate.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full.DickmanBasic

noncomputable section





/-- The endpoint face bound propagates from `t=1` to every positive
Stieltjes variable `t≥1`. -/
theorem roughSaias_log_div_t_ratio_le
    {x y t : ℝ} (hx : 0 < x) (hy : 1 < y) (ht : 1 ≤ t)
    {A : ℝ} (hu : Real.log x / Real.log y ≤ A) :
    Real.log (x / t) / Real.log y ≤ A := by
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht
  rw [Real.log_div hx.ne' htpos.ne']
  apply (div_le_iff₀ hlogy).2
  have hu' := (div_le_iff₀ hlogy).1 hu
  linarith

/-! ## Discharging the compact Fubini datum -/

theorem measurable_uncurry_roughSaiasBuchstabDensityKernel (x : ℝ) :
    Measurable (Function.uncurry (roughSaiasBuchstabDensityKernel x)) := by
  have hxs : Measurable (fun p : ℝ × ℝ ↦ x / p.1) :=
    measurable_const.div measurable_fst
  have hquot : Measurable (fun p : ℝ × ℝ ↦ (x / p.1) / p.2) :=
    hxs.div measurable_snd
  have hcoord : Measurable (fun p : ℝ × ℝ ↦
      Real.log ((x / p.1) / p.2) / Real.log p.1) :=
    (Real.measurable_log.comp hquot).div
      (Real.measurable_log.comp measurable_fst)
  have hprofile : Measurable (fun p : ℝ × ℝ ↦
      (x / p.1) * roughSaiasZeroExtendedRho
        (Real.log ((x / p.1) / p.2) / Real.log p.1)) :=
    hxs.mul (measurable_roughSaiasZeroExtendedRho.comp hcoord)
  have hcontinuous : Measurable (fun p : ℝ × ℝ ↦
      ((x / p.1) * roughSaiasZeroExtendedRho
        (Real.log ((x / p.1) / p.2) / Real.log p.1)) /
          Real.log p.1) :=
    hprofile.div (Real.measurable_log.comp measurable_fst)
  simpa [Function.uncurry, roughSaiasBuchstabDensityKernel,
    roughSaiasContinuousBuchstabProfile,
    roughSaiasStieltjesDickmanProfile] using
      hcontinuous.mul (measurable_roughSaiasFloorDensity.comp measurable_snd)

/-- One finite constant controls the zero-extended finite Dickman profile
through the sixth face.  No positivity estimate on the sixth face is
needed: this is only compact boundedness of the continuous function `rho`.
-/
theorem exists_roughSaiasZeroExtendedRho_abs_bound_six :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, u ≤ 6 →
      |roughSaiasZeroExtendedRho u| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    continuous_rho.continuousOn (s := Set.Icc (0 : ℝ) 6)
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 6 := by norm_num
  have hC0 : 0 ≤ C :=
    (norm_nonneg (rho 0)).trans (hC 0 hzero)
  use C, hC0
  intro u hu6
  by_cases hu0 : u < 0
  · simp [roughSaiasZeroExtendedRho_of_neg hu0, hC0]
  · rw [roughSaiasZeroExtendedRho_of_nonneg (le_of_not_gt hu0)]
    simpa only [Real.norm_eq_abs] using
      hC u ⟨le_of_not_gt hu0, hu6⟩

theorem roughSaiasFloorDensity_mem_unitInterval
    {t : ℝ} (ht1 : 1 ≤ t) :
    0 ≤ roughSaiasFloorDensity t ∧ roughSaiasFloorDensity t ≤ 1 := by
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hfloor0 : (0 : ℝ) ≤ (((⌊t⌋₊ : ℕ) : ℝ)) := by positivity
  have hfloort : (((⌊t⌋₊ : ℕ) : ℝ)) ≤ t := Nat.floor_le ht.le
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  unfold roughSaiasFloorDensity
  constructor
  · exact div_nonneg hfloor0 ht2.le
  · apply (div_le_one ht2).2
    exact hfloort.trans (by nlinarith)

/-- If the base is enlarged from `y` to `b` and `t ≥ 1`, the supported
Dickman coordinate stays below the original sixth-face endpoint. -/
theorem roughSaias_profile_coordinate_le_six
    {x y b t : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyb : y ≤ b) (ht1 : 1 ≤ t)
    (hu6 : Real.log x / Real.log y ≤ 6) :
    Real.log (x / t) / Real.log b ≤ 6 := by
  have hb : 1 < b := hy.trans_le hyb
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hq : 0 < x / t := div_pos hx ht
  by_cases hq1 : x / t ≤ 1
  · have hlogq : Real.log (x / t) ≤ 0 := Real.log_nonpos hq.le hq1
    have hlogb : 0 < Real.log b := Real.log_pos hb
    exact (div_nonpos_of_nonpos_of_nonneg hlogq hlogb.le).trans (by norm_num)
  · have hqone : 1 < x / t := lt_of_not_ge hq1
    have hlogq : 0 ≤ Real.log (x / t) := (Real.log_pos hqone).le
    have hlogyb : Real.log y ≤ Real.log b :=
      Real.log_le_log (zero_lt_one.trans hy) hyb
    calc
      Real.log (x / t) / Real.log b ≤
          Real.log (x / t) / Real.log y :=
        div_le_div_of_nonneg_left hlogq (Real.log_pos hy) hlogyb
      _ ≤ 6 := roughSaias_log_div_t_ratio_le hx hy ht1 hu6

theorem roughSaias_inner_profile_coordinate_le_six
    {x y s t : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hys : y ≤ s) (ht1 : 1 ≤ t)
    (hu6 : Real.log x / Real.log y ≤ 6) :
    Real.log ((x / s) / t) / Real.log s ≤ 6 := by
  have hs : 1 < s := hy.trans_le hys
  have hspos : 0 < s := zero_lt_one.trans hs
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hq : 0 < x / t := div_pos hx ht
  have hquotient : (x / s) / t = (x / t) / s := by
    field_simp [hspos.ne', ht.ne']
  have hcoord :
      Real.log ((x / s) / t) / Real.log s =
        Real.log (x / t) / Real.log s - 1 := by
    rw [hquotient, Real.log_div hq.ne' hspos.ne']
    field_simp [(Real.log_pos hs).ne']
  rw [hcoord]
  have hbase := roughSaias_profile_coordinate_le_six
    hx hy hys ht1 hu6
  linarith



theorem roughSaiasBuchstabDensityKernel_abs_le
    {x y s t C : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hys : y ≤ s) (ht1 : 1 ≤ t)
    (hu6 : Real.log x / Real.log y ≤ 6) (hC0 : 0 ≤ C)
    (hC : ∀ u : ℝ, u ≤ 6 → |roughSaiasZeroExtendedRho u| ≤ C) :
    |roughSaiasBuchstabDensityKernel x s t| ≤
      x * C / Real.log y := by
  have hs : 1 < s := hy.trans_le hys
  have hspos : 0 < s := zero_lt_one.trans hs
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hlogs : 0 < Real.log s := Real.log_pos hs
  have hlogys : Real.log y ≤ Real.log s :=
    Real.log_le_log (zero_lt_one.trans hy) hys
  have hxs : 0 ≤ x / s := (div_pos hx hspos).le
  have hxsle : x / s ≤ x := div_le_self hx.le hs.le
  have hcoord := roughSaias_inner_profile_coordinate_le_six
    hx hy hys ht1 hu6
  have hprofile :
      |roughSaiasStieltjesDickmanProfile (x / s) s t| ≤ x * C := by
    unfold roughSaiasStieltjesDickmanProfile
    rw [abs_mul, abs_of_nonneg hxs]
    calc
      (x / s) *
          |roughSaiasZeroExtendedRho
            (Real.log ((x / s) / t) / Real.log s)| ≤
        (x / s) * C := mul_le_mul_of_nonneg_left (hC _ hcoord) hxs
      _ ≤ x * C := mul_le_mul_of_nonneg_right hxsle hC0
  have hcontinuous :
      |roughSaiasContinuousBuchstabProfile x s t| ≤
        x * C / Real.log y := by
    unfold roughSaiasContinuousBuchstabProfile
    rw [abs_div, abs_of_pos hlogs]
    calc
      |roughSaiasStieltjesDickmanProfile (x / s) s t| / Real.log s ≤
          (x * C) / Real.log s :=
        div_le_div_of_nonneg_right hprofile hlogs.le
      _ ≤ x * C / Real.log y :=
        div_le_div_of_nonneg_left (mul_nonneg hx.le hC0) hlogy hlogys
  have hdensity := roughSaiasFloorDensity_mem_unitInterval ht1
  unfold roughSaiasBuchstabDensityKernel
  rw [abs_mul, abs_of_nonneg hdensity.1]
  calc
    |roughSaiasContinuousBuchstabProfile x s t| *
        roughSaiasFloorDensity t ≤
      (x * C / Real.log y) * 1 :=
        mul_le_mul hcontinuous hdensity.2 hdensity.1
          (div_nonneg (mul_nonneg hx.le hC0) hlogy.le)
    _ = x * C / Real.log y := mul_one _

theorem integrable_roughSaiasBuchstabDensityKernel
    {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (_hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6) :
    Integrable (Function.uncurry (roughSaiasBuchstabDensityKernel x))
      ((volume.restrict (Set.Ioc y z)).prod
        (volume.restrict (Set.Ioc (1 : ℝ) (R : ℝ)))) := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_roughSaiasZeroExtendedRho_abs_bound_six
  let μ : Measure ℝ := volume.restrict (Set.Ioc y z)
  let ν : Measure ℝ := volume.restrict (Set.Ioc (1 : ℝ) (R : ℝ))
  let K : ℝ × ℝ → ℝ :=
    Function.uncurry (roughSaiasBuchstabDensityKernel x)
  have hmeas : Measurable K := by
    simpa [K] using measurable_uncurry_roughSaiasBuchstabDensityKernel x
  have hconst : Integrable
      (fun _ : ℝ × ℝ ↦ x * C / Real.log y) (μ.prod ν) := by
    exact integrable_const _
  have hbound : ∀ᵐ p ∂(μ.prod ν),
      ‖K p‖ ≤ x * C / Real.log y := by
    rw [Measure.ae_prod_iff_ae_ae
      (measurableSet_le hmeas.norm measurable_const)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs]
    simpa [K, Function.uncurry] using
      roughSaiasBuchstabDensityKernel_abs_le hx hy hs.1.le ht.1.le
        hu6 hC0 hC
  have hK : Integrable K (μ.prod ν) :=
    hconst.mono' hmeas.aestronglyMeasurable hbound
  simpa [μ, ν, K] using hK



/-- Division by a scalar commutes exactly with the finite signed
functional. -/
theorem roughSaiasFiniteStieltjesFunctional_div
    (R : ℕ) (f : ℝ → ℝ) (c : ℝ) :
    roughSaiasFiniteStieltjesFunctional R (fun t ↦ f t / c) =
      roughSaiasFiniteStieltjesFunctional R f / c := by
  have hatom : roughSaiasStieltjesAtomPart R (fun t ↦ f t / c) =
      roughSaiasStieltjesAtomPart R f / c := by
    unfold roughSaiasStieltjesAtomPart
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hdensity :
      roughSaiasStieltjesDensityPart R (fun t ↦ f t / c) =
        roughSaiasStieltjesDensityPart R f / c := by
    unfold roughSaiasStieltjesDensityPart
    calc
      (∫ t in Set.Ioc (1 : ℝ) (R : ℝ),
          (f t / c) * roughSaiasFloorDensity t) =
        ∫ t in Set.Ioc (1 : ℝ) (R : ℝ),
          c⁻¹ * (f t * roughSaiasFloorDensity t) := by
            apply integral_congr_ae
            filter_upwards with t
            ring
      _ = c⁻¹ * ∫ t in Set.Ioc (1 : ℝ) (R : ℝ),
          f t * roughSaiasFloorDensity t := by
            rw [MeasureTheory.integral_const_mul]
      _ = (∫ t in Set.Ioc (1 : ℝ) (R : ℝ),
          f t * roughSaiasFloorDensity t) / c := by ring
  unfold roughSaiasFiniteStieltjesFunctional
  rw [hatom, hdensity]
  ring

/-- At a fixed Buchstab base, the functional of the pointwise kernel is
the capped Stieltjes Lambda at `x/s`, divided by `log s`. -/
theorem roughSaiasFiniteStieltjesFunctional_buchstabProfile
    (R : ℕ) (x s : ℝ) :
    roughSaiasFiniteStieltjesFunctional R
        (roughSaiasContinuousBuchstabProfile x s) =
      roughSaiasLambdaStieltjesWithCutoff R (x / s) s /
        Real.log s := by
  unfold roughSaiasContinuousBuchstabProfile
    roughSaiasLambdaStieltjesWithCutoff
  exact roughSaiasFiniteStieltjesFunctional_div R
    (roughSaiasStieltjesDickmanProfile (x / s) s) (Real.log s)

/-! ## The finite atomic lift -/



/-! ## The density Fubini lift -/



/-! ## Functional continuous Buchstab -/

private theorem intervalIntegrable_roughSaiasStieltjesAtomPart_buchstab
    {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6) :
    IntervalIntegrable
      (fun s ↦ roughSaiasStieltjesAtomPart R
        (roughSaiasContinuousBuchstabProfile x s)) volume y z := by
  unfold roughSaiasStieltjesAtomPart
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 R) :
      IntervalIntegrable
        (fun s ↦ roughSaiasContinuousBuchstabProfile x s (n : ℝ) /
          (n : ℝ)) volume y z := by
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn1real : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn1
    have hface := roughSaias_log_div_t_ratio_le hx hy
      hn1real hu6
    have hnposreal : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 0 < n by omega)
    exact (intervalIntegrable_roughSaiasContinuousBuchstabProfile hx
      hnposreal hy hyz hface).div_const _
  apply (IntervalIntegrable.sum (Finset.Icc 1 R) hterm).congr
  intro s _hs
  simp only [Finset.sum_apply]

/-- The capped Lambda integrand occurring in functional Buchstab is
interval-integrable; the product-kernel proof discharges the density part. -/
theorem intervalIntegrable_roughSaiasLambdaStieltjesWithCutoff_buchstab
    {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6) :
    IntervalIntegrable
      (fun s ↦ roughSaiasLambdaStieltjesWithCutoff R (x / s) s /
        Real.log s) volume y z := by
  have hAtom :=
    intervalIntegrable_roughSaiasStieltjesAtomPart_buchstab
      (R := R) hx hy hyz hu6
  have hK := integrable_roughSaiasBuchstabDensityKernel
    (R := R) hx hy hyz hu6
  have hDensityOn : IntegrableOn
      (fun s ↦ roughSaiasStieltjesDensityPart R
        (roughSaiasContinuousBuchstabProfile x s)) (Set.Ioc y z) := by
    simpa [roughSaiasStieltjesDensityPart,
      roughSaiasBuchstabDensityKernel, Function.uncurry] using
        hK.integral_prod_left
  have hDensity : IntervalIntegrable
      (fun s ↦ roughSaiasStieltjesDensityPart R
        (roughSaiasContinuousBuchstabProfile x s)) volume y z :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hyz).mpr hDensityOn
  have hFunctional : IntervalIntegrable
      (fun s ↦ roughSaiasFiniteStieltjesFunctional R
        (roughSaiasContinuousBuchstabProfile x s)) volume y z := by
    unfold roughSaiasFiniteStieltjesFunctional
    exact hAtom.sub hDensity
  apply hFunctional.congr
  intro s _hs
  exact roughSaiasFiniteStieltjesFunctional_buchstabProfile R x s











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasFullyRealBuchstabCells -/
section


/-!
# Unit-cell decomposition of the fully real Buchstab integral

The functional continuous-Buchstab identity is converted here into the
project's natural-base normal forms.  On a cell `s ∈ [m,m+1]`, the inner
term is split exactly into

* quotient drift at the current real base `s`, and
* real-base drift from `s` to the natural endpoint `m+1`.

No equality between the real and natural bases is left as a premise.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full

noncomputable section









/-- On the natural range `y ≤ s ≤ Z ≤ X`, the fixed outer cutoff
`X` is canonical for the inner Stieltjes functional, and the latter is the
fully real normal form. -/
theorem roughSaiasLambdaStieltjesWithCutoff_inner_eq_fullyReal
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    {s : ℝ} (hs : s ∈ Set.Icc (y : ℝ) (Z : ℝ)) :
    roughSaiasLambdaStieltjesWithCutoff X ((X : ℝ) / s) s =
      roughSaiasFullyRealLambdaNormalForm ((X : ℝ) / s) s := by
  have hyone : 1 < (y : ℝ) := by
    exact_mod_cast (show 1 < y by omega)
  have hsone : 1 < s := hyone.trans_le hs.1
  have hspos : 0 < s := zero_lt_one.trans hsone
  have hXposNat : 0 < X := by omega
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast hXposNat
  have hsX : s ≤ (X : ℝ) :=
    hs.2.trans (by exact_mod_cast hZX)
  have hinnerPos : 0 < (X : ℝ) / s := div_pos hXpos hspos
  have hinnerOne : 1 ≤ (X : ℝ) / s :=
    (one_le_div hspos).2 hsX
  have hinnerCap : (X : ℝ) / s ≤ (X : ℝ) :=
    div_le_self hXpos.le hsone.le
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos hyone
  have hlogs : 0 < Real.log s := Real.log_pos hsone
  have hlogX0 : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hlogys : Real.log (y : ℝ) ≤ Real.log s :=
    Real.log_le_log (zero_lt_one.trans hyone) hs.1
  have hratio : Real.log (X : ℝ) / Real.log s ≤ 5 :=
    (div_le_div_of_nonneg_left hlogX0 hlogy hlogys).trans hu5
  have hinnerFace :
      Real.log ((X : ℝ) / s) / Real.log s ≤ 5 := by
    rw [Real.log_div hXpos.ne' hspos.ne']
    calc
      (Real.log (X : ℝ) - Real.log s) / Real.log s =
          Real.log (X : ℝ) / Real.log s - 1 := by
        field_simp [hlogs.ne']
      _ ≤ 5 := by linarith
  rw [roughSaiasLambdaStieltjesWithCutoff_eq_canonical
    hinnerPos hsone hinnerCap]
  exact roughSaiasLambdaStieltjes_eq_fullyRealNormalForm
    hinnerOne hsone hinnerFace



theorem intervalIntegrable_roughSaiasFullyRealBuchstabNormalIntegrand
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    IntervalIntegrable
      (roughSaiasFullyRealBuchstabNormalIntegrand X)
      volume (y : ℝ) (Z : ℝ) := by
  have hXpos : 0 < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  have hyone : 1 < (y : ℝ) := by
    exact_mod_cast (show 1 < y by omega)
  have hyZR : (y : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hyZ
  have hcap :=
    intervalIntegrable_roughSaiasLambdaStieltjesWithCutoff_buchstab
      (R := X) hXpos hyone hyZR (hu5.trans (by norm_num))
  apply hcap.congr
  intro s hsU
  have hsI : s ∈ Set.Icc (y : ℝ) (Z : ℝ) := by
    have hsU' : s ∈ Set.uIcc (y : ℝ) (Z : ℝ) :=
      Set.uIoc_subset_uIcc hsU
    simpa [Set.uIcc_of_le hyZR] using hsU'
  unfold roughSaiasFullyRealBuchstabNormalIntegrand
  change
    roughSaiasLambdaStieltjesWithCutoff X ((X : ℝ) / s) s /
        Real.log s =
      roughSaiasFullyRealLambdaNormalForm ((X : ℝ) / s) s /
        Real.log s
  rw [roughSaiasLambdaStieltjesWithCutoff_inner_eq_fullyReal
    hy2 hyZ hZX hu5 hsI]

/-! ## Natural unit cells -/



/-- Right-endpoint sample on a unit cell, in the existing natural-base
theta weight. -/
theorem roughSaiasFullyRealBuchstabNormalIntegrand_nat
    (X m : ℕ) :
    roughSaiasFullyRealBuchstabNormalIntegrand X (m : ℝ) =
      roughSaiasNormalFormThetaWeight X m := by
  unfold roughSaiasFullyRealBuchstabNormalIntegrand
    roughSaiasNormalFormThetaWeight roughSaiasContinuousPrimeNormalForm
  rw [roughSaiasFullyRealLambdaNormalForm_nat]























theorem integral_roughSaiasFullyRealBuchstab_cell_eq_sample_add_remainder
    {X y Z m : ℕ} (hy2 : 2 ≤ y) (hyZ : y ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hm : m ∈ Finset.Ico y Z) :
    (∫ s in (m : ℝ)..(m + 1 : ℕ),
        roughSaiasFullyRealBuchstabNormalIntegrand X s) =
      roughSaiasNormalFormThetaWeight X (m + 1) +
        roughSaiasFullyRealBuchstabCellRemainder X m := by
  have hmData := Finset.mem_Ico.mp hm
  have hmle : m ≤ m + 1 := by omega
  have hym : y ≤ m := hmData.1
  have hmZ : m + 1 ≤ Z := by omega
  have hglobal :=
    intervalIntegrable_roughSaiasFullyRealBuchstabNormalIntegrand
      hy2 hyZ hZX hu5
  have hsubset : Set.uIcc (m : ℝ) (m + 1 : ℕ) ⊆
      Set.uIcc (y : ℝ) (Z : ℝ) := by
    rw [Set.uIcc_of_le (by exact_mod_cast hmle),
      Set.uIcc_of_le (by exact_mod_cast hyZ)]
    exact Set.Icc_subset_Icc (by exact_mod_cast hym) (by exact_mod_cast hmZ)
  have hcell := hglobal.mono_set hsubset
  have hconst : IntervalIntegrable
      (fun _ : ℝ ↦ roughSaiasNormalFormThetaWeight X (m + 1))
      volume (m : ℝ) (m + 1 : ℕ) :=
    continuous_const.intervalIntegrable _ _
  unfold roughSaiasFullyRealBuchstabCellRemainder
  rw [intervalIntegral.integral_sub hcell hconst]
  simp









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasFullyRealNaturalCells -/
section


/-!
# Fully real cells with the floor/frac-paired natural endpoint sample

Sampling a fully real Buchstab cell by the continuous real-quotient theta
weight leaves a separate signed floor correction.  Sampling instead by the
natural quotient theta weight pairs that correction inside the cell.  The
sum of these paired cells is therefore exactly the natural integer Abel
consistency defect, with no signed-floor term left over.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section





/-- On every cell occurring in the compact Buchstab interval, the paired
definition is literally the integral minus the natural endpoint sample. -/
theorem roughSaiasFullyRealNaturalBuchstabCellRemainder_eq_integral
    {X y Z m : ℕ} (hy2 : 2 ≤ y) (hyZ : y ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hm : m ∈ Finset.Ico y Z) :
    roughSaiasFullyRealNaturalBuchstabCellRemainder X m =
      ∫ s in (m : ℝ)..(m + 1 : ℕ),
        (roughSaiasFullyRealBuchstabNormalIntegrand X s -
          roughSaiasNaturalQuotientThetaWeight X (m + 1)) := by
  have hmData := Finset.mem_Ico.mp hm
  have hmle : m ≤ m + 1 := by omega
  have hym : y ≤ m := hmData.1
  have hmZ : m + 1 ≤ Z := by omega
  have hglobal :=
    intervalIntegrable_roughSaiasFullyRealBuchstabNormalIntegrand
      hy2 hyZ hZX hu5
  have hsubset : Set.uIcc (m : ℝ) (m + 1 : ℕ) ⊆
      Set.uIcc (y : ℝ) (Z : ℝ) := by
    rw [Set.uIcc_of_le (by exact_mod_cast hmle),
      Set.uIcc_of_le (by exact_mod_cast hyZ)]
    exact Set.Icc_subset_Icc (by exact_mod_cast hym) (by exact_mod_cast hmZ)
  have hcell := hglobal.mono_set hsubset
  have hconst : IntervalIntegrable
      (fun _ : ℝ ↦ roughSaiasNaturalQuotientThetaWeight X (m + 1))
      MeasureTheory.volume (m : ℝ) (m + 1 : ℕ) :=
    continuous_const.intervalIntegrable _ _
  have hsample :=
    integral_roughSaiasFullyRealBuchstab_cell_eq_sample_add_remainder
      hy2 hyZ hZX hu5 hm
  rw [intervalIntegral.integral_sub hcell hconst]
  simp
  have hsuccCast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by
    norm_num
  rw [hsuccCast] at hsample
  rw [hsample,
    roughSaiasNormalFormThetaWeight_eq_natural_add_fractional]
  unfold roughSaiasFullyRealNaturalBuchstabCellRemainder
  ring













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

/-- The signed real-quotient endpoint correction is uniformly bounded by
`20/log n` on every compact five-face block.  The only nontrivial point is
that multiplication by the integer quotient cancels the logarithmic gap
between `X/n` and `floor(X/n)`. -/
private theorem roughSaiasFractionalCorrectionThetaWeight_abs_le_twenty_inv_log
    {X a n : ℕ} (hX : 0 < X) (ha3 : 3 ≤ a) (han : a ≤ n)
    (hnX : n ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    |roughSaiasFractionalCorrectionThetaWeight X n| ≤
      20 / Real.log (n : ℝ) := by
  let r : ℝ := (X : ℝ) / (n : ℝ)
  let q : ℝ := ((X / n : ℕ) : ℝ)
  let u : ℝ := Real.log r / Real.log (n : ℝ)
  let v : ℝ := Real.log q / Real.log (n : ℝ)
  have hnOne : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hnpos : 0 < (n : ℝ) := zero_lt_one.trans hnOne
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos hnOne
  have hlognOne : 1 ≤ Real.log (n : ℝ) := by
    have hexp : Real.exp 1 < (n : ℝ) :=
      Real.exp_one_lt_three.trans_le (by exact_mod_cast (ha3.trans han))
    exact ((Real.lt_log_iff_exp_lt hnpos).2 hexp).le
  have hqNat : 1 ≤ X / n := Nat.div_pos hnX (by omega)
  have hqpos : 0 < q := by
    dsimp only [q]
    positivity
  have hrpos : 0 < r := by
    dsimp only [r]
    positivity
  have hfloor : r - Int.fract r = q := by
    simpa only [r, q] using roughSaiasRealQuotient_sub_fract_eq_natQuotient X n
  have hrEq : r = q + Int.fract r := by linarith
  have hqr : q ≤ r := by
    rw [hrEq]
    exact le_add_of_nonneg_right (Int.fract_nonneg r)
  have hsubNonneg : 0 ≤ r - q := sub_nonneg.mpr hqr
  have hsubOne : r - q ≤ 1 := by
    rw [hrEq]
    simpa only [add_sub_cancel_left] using (Int.fract_lt_one r).le
  have hlogGapNonneg : 0 ≤ Real.log r - Real.log q :=
    sub_nonneg.mpr (Real.log_le_log hqpos hqr)
  have hlogGap : Real.log r - Real.log q ≤ 1 / q := by
    have hratioPos : 0 < r / q := div_pos hrpos hqpos
    have hlogRatio := Real.log_le_sub_one_of_pos hratioPos
    calc
      Real.log r - Real.log q = Real.log (r / q) := by
        rw [Real.log_div hrpos.ne' hqpos.ne']
      _ ≤ r / q - 1 := hlogRatio
      _ = (r - q) / q := by
        rw [sub_div, div_self hqpos.ne']
      _ ≤ 1 / q := div_le_div_of_nonneg_right hsubOne hqpos.le
  have hu0 : 0 ≤ u := by
    have hrOne : 1 ≤ r := by
      dsimp only [r]
      exact (one_le_div hnpos).2 (by exact_mod_cast hnX)
    exact div_nonneg (Real.log_nonneg hrOne) hlogn.le
  have hqOne : (1 : ℝ) ≤ q := by
    dsimp only [q]
    exact_mod_cast hqNat
  have hv0 : 0 ≤ v :=
    div_nonneg (Real.log_nonneg hqOne) hlogn.le
  have hvu : v ≤ u := by
    dsimp only [u, v]
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hqpos hqr) hlogn.le
  have hu5' : u ≤ 5 := by
    have ha2 : 2 ≤ a := by omega
    have hanR : (a : ℝ) ≤ (n : ℝ) := by exact_mod_cast han
    have hnXR : (n : ℝ) ≤ (X : ℝ) := by exact_mod_cast hnX
    have hface := roughSaiasFullyRealHyperbolaCoordinate_le_five
      hX ha2 hanR hnXR
        (t := (1 : ℝ)) (by norm_num) hu5
    simpa only [u, r, roughSaiasFullyRealHyperbolaCoordinate,
      Real.log_one, sub_zero] using hface
  have hv5 : v ≤ 5 := hvu.trans hu5'
  have huvAbs : |u - v| ≤ 1 / q := by
    rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
    have hdiff : u - v =
        (Real.log r - Real.log q) / Real.log (n : ℝ) := by
      dsimp only [u, v]
      ring
    rw [hdiff]
    calc
      (Real.log r - Real.log q) / Real.log (n : ℝ) ≤
          (1 / q) / Real.log (n : ℝ) :=
        div_le_div_of_nonneg_right hlogGap hlogn.le
      _ ≤ 1 / q := by
        have hqInvNonneg : 0 ≤ 1 / q := by positivity
        apply (div_le_iff₀ hlogn).2
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hlognOne hqInvNonneg)
  have hGdiff : |roughSaiasG n u - roughSaiasG n v| ≤ 3 * |u - v| := by
    simpa only [roughSaiasFullyRealG_nat] using
      (roughSaiasFullyRealG_lipschitz_three hnOne
        (show u ∈ Set.Icc (0 : ℝ) 5 from ⟨hu0, hu5'⟩)
        (show v ∈ Set.Icc (0 : ℝ) 5 from ⟨hv0, hv5⟩))
  have hqG : q * |roughSaiasG n u - roughSaiasG n v| ≤ 3 := by
    calc
      q * |roughSaiasG n u - roughSaiasG n v| ≤ q * (3 * |u - v|) :=
        mul_le_mul_of_nonneg_left hGdiff hqpos.le
      _ ≤ q * (3 * (1 / q)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left huvAbs (by norm_num)) hqpos.le
      _ = 3 := by field_simp [hqpos.ne']
  have hGu : |roughSaiasG n u| ≤ 16 := by
    simpa only [roughSaiasFullyRealG_nat] using
      (roughSaiasFullyRealG_abs_le_sixteen hnOne
        (show u ∈ Set.Icc (0 : ℝ) 5 from ⟨hu0, hu5'⟩))
  have hfractTerm :
      |Int.fract r * (roughSaiasG n u - 1)| ≤ 17 := by
    rw [abs_mul, abs_of_nonneg (Int.fract_nonneg r)]
    have hGminus : |roughSaiasG n u - 1| ≤ |roughSaiasG n u| + 1 := by
      simpa only [abs_one] using (abs_sub (roughSaiasG n u) 1)
    calc
      Int.fract r * |roughSaiasG n u - 1| ≤
          1 * |roughSaiasG n u - 1| :=
        mul_le_mul_of_nonneg_right (Int.fract_lt_one r).le (abs_nonneg _)
      _ ≤ 1 * (|roughSaiasG n u| + 1) :=
        mul_le_mul_of_nonneg_left hGminus (by norm_num)
      _ ≤ 1 * (16 + 1) := by gcongr
      _ = 17 := by norm_num
  have hterm :
      |q * (roughSaiasG n u - roughSaiasG n v) +
          Int.fract r * (roughSaiasG n u - 1)| ≤ 20 := by
    calc
      |q * (roughSaiasG n u - roughSaiasG n v) +
          Int.fract r * (roughSaiasG n u - 1)| ≤
        |q * (roughSaiasG n u - roughSaiasG n v)| +
          |Int.fract r * (roughSaiasG n u - 1)| := abs_add_le _ _
      _ = q * |roughSaiasG n u - roughSaiasG n v| +
          |Int.fract r * (roughSaiasG n u - 1)| := by
        rw [abs_mul, abs_of_pos hqpos]
      _ ≤ 3 + 17 := add_le_add hqG hfractTerm
      _ = 20 := by norm_num
  unfold roughSaiasFractionalCorrectionThetaWeight
    roughSaiasSignedFractionalCorrectionTerm
  change |(q * (roughSaiasG n u - roughSaiasG n v) +
      Int.fract r * (roughSaiasG n u - 1)) / Real.log (n : ℝ)| ≤ _
  rw [abs_div, abs_of_pos hlogn]
  exact div_le_div_of_nonneg_right hterm hlogn.le

/-- Literal rho-minus-fractional-integral form of the fully real Buchstab
integrand. -/
private theorem roughSaiasFullyRealBuchstabNormalIntegrand_eq_rho_sub_fractional
    {X : ℕ} {s : ℝ} (hs : 1 < s) :
    roughSaiasFullyRealBuchstabNormalIntegrand X s =
      ((X : ℝ) / (s * Real.log s)) *
          (rho (Real.log ((X : ℝ) / s) / Real.log s) -
            roughSaiasFullyRealBaseFreeFractionalIntegral ((X : ℝ) / s) s) -
        Int.fract ((X : ℝ) / s) / Real.log s := by
  unfold roughSaiasFullyRealBuchstabNormalIntegrand
    roughSaiasFullyRealLambdaNormalForm
  rw [roughSaiasFullyRealG_eq_rho_sub_baseFree hs]
  ring

/-- The rho component has total variation at most one along the real
natural-endpoint hyperbola path. -/
private theorem sum_abs_rho_fullyRealHyperbolaLogRatio_succ_sub_le_one
    {X a b : ℕ} (hX : 0 < X) (ha2 : 2 ≤ a) (hab : a ≤ b)
    (hbX : b ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |rho (Real.log ((X : ℝ) / (m + 1 : ℕ)) /
              Real.log ((m + 1 : ℕ) : ℝ)) -
          rho (Real.log ((X : ℝ) / (m : ℝ)) /
              Real.log (m : ℝ))|) ≤ 1 := by
  let u : ℕ → ℝ := fun m =>
    Real.log ((X : ℝ) / (m : ℝ)) / Real.log (m : ℝ)
  have huBounds : ∀ m ∈ Finset.Icc a b, u m ∈ Set.Icc (0 : ℝ) 5 := by
    intro m hm
    have hmData := Finset.mem_Icc.mp hm
    have hmOne : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
    have hmX : m ≤ X := hmData.2.trans hbX
    have hu0 : 0 ≤ u m := by
      dsimp only [u]
      exact div_nonneg
        (Real.log_nonneg ((one_le_div (by positivity)).2 (by exact_mod_cast hmX)))
        (Real.log_pos hmOne).le
    have hamR : (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmData.1
    have hmXR : (m : ℝ) ≤ (X : ℝ) := by exact_mod_cast hmX
    have hu5m := roughSaiasFullyRealHyperbolaCoordinate_le_five
      hX ha2 hamR hmXR
        (t := (1 : ℝ)) (by norm_num) hu5
    have : u m ≤ 5 := by
      simpa only [u, roughSaiasFullyRealHyperbolaCoordinate,
        Real.log_one, sub_zero] using hu5m
    exact ⟨hu0, this⟩
  have huMono : ∀ m ∈ Finset.Ico a b, u (m + 1) ≤ u m := by
    intro m hm
    have hmData := Finset.mem_Ico.mp hm
    have hmOne : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
    have hnextOne : (1 : ℝ) < ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 < m + 1 by omega)
    have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos hmOne
    have hlogNext : 0 < Real.log ((m + 1 : ℕ) : ℝ) := Real.log_pos hnextOne
    have hlogLe : Real.log (m : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast (Nat.le_succ m))
    have hlogX0 : 0 ≤ Real.log (X : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
    have hXR : (X : ℝ) ≠ 0 := by positivity
    have hmNe : (m : ℝ) ≠ 0 := by positivity
    have hnextNe : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    dsimp only [u]
    rw [Real.log_div hXR hnextNe, Real.log_div hXR hmNe]
    have hratio := div_le_div_of_nonneg_left hlogX0 hlogm hlogLe
    calc
      (Real.log (X : ℝ) - Real.log ((m + 1 : ℕ) : ℝ)) /
          Real.log ((m + 1 : ℕ) : ℝ) =
        Real.log (X : ℝ) / Real.log ((m + 1 : ℕ) : ℝ) - 1 := by
          field_simp [hlogNext.ne']
      _ ≤ Real.log (X : ℝ) / Real.log (m : ℝ) - 1 :=
        sub_le_sub_right hratio 1
      _ = (Real.log (X : ℝ) - Real.log (m : ℝ)) /
          Real.log (m : ℝ) := by
        field_simp [hlogm.ne']
  have hrhoMono : ∀ m ∈ Finset.Ico a b, rho (u m) ≤ rho (u (m + 1)) := by
    intro m hm
    have hmData := Finset.mem_Ico.mp hm
    exact roughRho_antitoneOn_zero_five
      (huBounds (m + 1) (by rw [Finset.mem_Icc]; omega))
      (huBounds m (by rw [Finset.mem_Icc]; omega))
      (huMono m hm)
  have htelescope :
      (∑ m ∈ Finset.Ico a b, |rho (u (m + 1)) - rho (u m)|) =
        rho (u b) - rho (u a) := by
    calc
      (∑ m ∈ Finset.Ico a b, |rho (u (m + 1)) - rho (u m)|) =
          ∑ m ∈ Finset.Ico a b, (rho (u (m + 1)) - rho (u m)) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [abs_of_nonneg (sub_nonneg.mpr (hrhoMono m hm))]
      _ = rho (u b) - rho (u a) := by
        exact Finset.sum_Ico_sub (fun m => rho (u m)) hab
  have hrhoA0 : 0 ≤ rho (u a) :=
    (rho_pos_on_zero_five (huBounds a (by simp [hab])).1
      (huBounds a (by simp [hab])).2).le
  have hrhoB1 : rho (u b) ≤ 1 :=
    FriableAsymptotic.rho_le_one_of_le_five
      (huBounds b (by simp [hab])).2
  change (∑ m ∈ Finset.Ico a b,
    |rho (u (m + 1)) - rho (u m)|) ≤ 1
  rw [htelescope]
  linarith [hrhoA0, hrhoB1]

set_option maxHeartbeats 800000 in
/-- Pointwise right-endpoint quadrature bound for the full fully-real
Buchstab integrand on a lower natural cell.  Its four terms are,
respectively, coefficient drift, rho variation, the real-hyperbola
fractional-integral ledger, and the harmless bounded sawtooth endpoint. -/
private theorem roughSaiasFullyRealBuchstabNormalIntegrand_cell_abs_sub_right_le
    {X a b m : ℕ} (hX : 0 < X) (ha3 : 3 ≤ a) (hab : a ≤ b)
    (hbX : b ≤ X) (hm : m ∈ Finset.Ico a b)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5)
    {s : ℝ} (hs : s ∈ Set.Icc (m : ℝ) (m + 1 : ℕ)) :
    |roughSaiasFullyRealBuchstabNormalIntegrand X s -
        roughSaiasFullyRealBuchstabNormalIntegrand X (m + 1 : ℕ)| ≤
      16 *
          ((X : ℝ) / ((m : ℝ) * Real.log (m : ℝ)) -
            (X : ℝ) /
              (((m + 1 : ℕ) : ℝ) * Real.log ((m + 1 : ℕ) : ℝ))) +
        ((X : ℝ) / ((a : ℝ) * Real.log (a : ℝ))) *
          ((rho (Real.log ((X : ℝ) / (m + 1 : ℕ)) /
                  Real.log ((m + 1 : ℕ) : ℝ)) -
              rho (Real.log ((X : ℝ) / (m : ℝ)) /
                  Real.log (m : ℝ))) +
            roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger
              X a m) +
        2 / Real.log (m : ℝ) := by
  let A : ℝ → ℝ := fun r => (X : ℝ) / (r * Real.log r)
  let u : ℝ → ℝ := fun r => Real.log ((X : ℝ) / r) / Real.log r
  let J : ℝ → ℝ := fun r =>
    roughSaiasFullyRealBaseFreeFractionalIntegral ((X : ℝ) / r) r
  let H : ℝ → ℝ := fun r => rho (u r) - J r
  let P : ℝ → ℝ := fun r => Int.fract ((X : ℝ) / r) / Real.log r
  let n : ℝ := ((m + 1 : ℕ) : ℝ)
  have hmData := Finset.mem_Ico.mp hm
  have hm3 : 3 ≤ m := ha3.trans hmData.1
  have hnextX : m + 1 ≤ X := by omega
  have haOne : (1 : ℝ) < (a : ℝ) := by exact_mod_cast (show 1 < a by omega)
  have hmOne : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
  have hsOne : 1 < s := hmOne.trans_le hs.1
  have hnOne : 1 < n := by
    dsimp only [n]
    exact_mod_cast (show 1 < m + 1 by omega)
  have hloga : 0 < Real.log (a : ℝ) := Real.log_pos haOne
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos hmOne
  have hlogs : 0 < Real.log s := Real.log_pos hsOne
  have hlogn : 0 < Real.log n := Real.log_pos hnOne
  have hXreal : 0 < (X : ℝ) := by exact_mod_cast hX
  have has : (a : ℝ) ≤ s :=
    (by exact_mod_cast hmData.1 : (a : ℝ) ≤ (m : ℝ)).trans hs.1
  have hsn : s ≤ n := by simpa only [n] using hs.2
  have hnX : n ≤ (X : ℝ) := by
    dsimp only [n]
    exact_mod_cast hnextX
  have ha2 : 2 ≤ a := by omega
  have hamR : (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmData.1
  have hmXR : (m : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast (show m ≤ X by omega)
  have hfaceM := roughSaiasFullyRealHyperbolaCoordinate_le_five
    hX ha2 hamR hmXR
      (t := (1 : ℝ)) (by norm_num) hu5
  have hfaceS := roughSaiasFullyRealHyperbolaCoordinate_le_five
    hX ha2 has (hsn.trans hnX) (t := (1 : ℝ)) (by norm_num) hu5
  have hfaceN := roughSaiasFullyRealHyperbolaCoordinate_le_five
    hX ha2 (has.trans hsn) hnX (t := (1 : ℝ)) (by norm_num) hu5
  have huM5 : u (m : ℝ) ≤ 5 := by
    simpa only [u, roughSaiasFullyRealHyperbolaCoordinate,
      Real.log_one, sub_zero] using hfaceM
  have huS5 : u s ≤ 5 := by
    simpa only [u, roughSaiasFullyRealHyperbolaCoordinate,
      Real.log_one, sub_zero] using hfaceS
  have huN5 : u n ≤ 5 := by
    simpa only [u, n, roughSaiasFullyRealHyperbolaCoordinate,
      Real.log_one, sub_zero] using hfaceN
  have huM0 : 0 ≤ u (m : ℝ) := by
    dsimp only [u]
    exact div_nonneg
      (Real.log_nonneg ((one_le_div (by positivity)).2
        (by exact_mod_cast (show m ≤ X by omega)))) hlogm.le
  have huS0 : 0 ≤ u s := by
    dsimp only [u]
    exact div_nonneg
      (Real.log_nonneg ((one_le_div (by positivity)).2 (hsn.trans hnX))) hlogs.le
  have huN0 : 0 ≤ u n := by
    dsimp only [u]
    exact div_nonneg
      (Real.log_nonneg ((one_le_div (by positivity)).2 hnX)) hlogn.le
  have huAntitone : ∀ {r₀ r₁ : ℝ}, 1 < r₀ → r₀ ≤ r₁ → r₁ ≤ (X : ℝ) →
      u r₁ ≤ u r₀ := by
    intro r₀ r₁ hr₀One hr₀r₁ hr₁X
    have hr₀pos : 0 < r₀ := zero_lt_one.trans hr₀One
    have hr₁One : 1 < r₁ := hr₀One.trans_le hr₀r₁
    have hr₁pos : 0 < r₁ := zero_lt_one.trans hr₁One
    have hlogr₀ : 0 < Real.log r₀ := Real.log_pos hr₀One
    have hlogr₁ : 0 < Real.log r₁ := Real.log_pos hr₁One
    have hlogLe : Real.log r₀ ≤ Real.log r₁ :=
      Real.log_le_log hr₀pos hr₀r₁
    have hlogX0 : 0 ≤ Real.log (X : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
    have hratio := div_le_div_of_nonneg_left hlogX0 hlogr₀ hlogLe
    dsimp only [u]
    rw [Real.log_div hXreal.ne' hr₁pos.ne',
      Real.log_div hXreal.ne' hr₀pos.ne']
    calc
      (Real.log (X : ℝ) - Real.log r₁) / Real.log r₁ =
          Real.log (X : ℝ) / Real.log r₁ - 1 := by
        field_simp [hlogr₁.ne']
      _ ≤ Real.log (X : ℝ) / Real.log r₀ - 1 :=
        sub_le_sub_right hratio 1
      _ = (Real.log (X : ℝ) - Real.log r₀) / Real.log r₀ := by
        field_simp [hlogr₀.ne']
  have huNS : u n ≤ u s := huAntitone hsOne hsn hnX
  have huSM : u s ≤ u (m : ℝ) :=
    huAntitone hmOne hs.1 (hsn.trans hnX)
  have hrhoMS : rho (u (m : ℝ)) ≤ rho (u s) :=
    roughRho_antitoneOn_zero_five
      (show u s ∈ Set.Icc (0 : ℝ) 5 from ⟨huS0, huS5⟩)
      (show u (m : ℝ) ∈ Set.Icc (0 : ℝ) 5 from ⟨huM0, huM5⟩)
      huSM
  have hrhoSN : rho (u s) ≤ rho (u n) :=
    roughRho_antitoneOn_zero_five
      (show u n ∈ Set.Icc (0 : ℝ) 5 from ⟨huN0, huN5⟩)
      (show u s ∈ Set.Icc (0 : ℝ) 5 from ⟨huS0, huS5⟩)
      huNS
  have hrhoDiff : |rho (u s) - rho (u n)| ≤
      rho (u n) - rho (u (m : ℝ)) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hrhoSN)]
    linarith
  have hJdiff : |J s - J n| ≤
      roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m := by
    dsimp only [J, n]
    exact
      roughSaiasFullyRealBaseFreeFractionalIntegral_hyperbola_cell_abs_sub_le
        hX ha2 hab hbX hm hu5 hs
  have hHdiff : |H s - H n| ≤
      (rho (u n) - rho (u (m : ℝ))) +
        roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m := by
    dsimp only [H]
    calc
      |(rho (u s) - J s) - (rho (u n) - J n)| ≤
          |rho (u s) - rho (u n)| + |J s - J n| := by
        have := abs_sub (rho (u s) - rho (u n)) (J s - J n)
        convert this using 1
        all_goals ring
      _ ≤ (rho (u n) - rho (u (m : ℝ))) +
          roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m :=
        add_le_add hrhoDiff hJdiff
  have hHdiffNonneg : 0 ≤
      (rho (u n) - rho (u (m : ℝ))) +
        roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m :=
    (abs_nonneg (H s - H n)).trans hHdiff
  have hHn : |H n| ≤ 16 := by
    have hG := roughSaiasFullyRealG_abs_le_sixteen hnOne
      (show u n ∈ Set.Icc (0 : ℝ) 5 from ⟨huN0, huN5⟩)
    have hEq := roughSaiasFullyRealG_eq_rho_sub_baseFree
      (x := (X : ℝ) / n) hnOne
    dsimp only [H, J]
    rw [← hEq]
    exact hG
  have hlogMS : Real.log (m : ℝ) ≤ Real.log s :=
    Real.log_le_log (zero_lt_one.trans hmOne) hs.1
  have hlogSN : Real.log s ≤ Real.log n :=
    Real.log_le_log (zero_lt_one.trans hsOne) hsn
  have hdenomMS : (m : ℝ) * Real.log (m : ℝ) ≤ s * Real.log s :=
    mul_le_mul hs.1 hlogMS hlogm.le (by positivity)
  have hdenomSN : s * Real.log s ≤ n * Real.log n :=
    mul_le_mul hsn hlogSN hlogs.le (by positivity)
  have hdenomAM : (a : ℝ) * Real.log (a : ℝ) ≤
      (m : ℝ) * Real.log (m : ℝ) := by
    have hlogAM : Real.log (a : ℝ) ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hmData.1)
    exact mul_le_mul (by exact_mod_cast hmData.1) hlogAM hloga.le (by positivity)
  have hAnAs : A n ≤ A s := by
    dsimp only [A]
    exact div_le_div_of_nonneg_left hXreal.le (mul_pos (by positivity) hlogs) hdenomSN
  have hAsAm : A s ≤ A (m : ℝ) := by
    dsimp only [A]
    exact div_le_div_of_nonneg_left hXreal.le
      (mul_pos (by positivity) hlogm) hdenomMS
  have hAmAa : A (m : ℝ) ≤ A (a : ℝ) := by
    dsimp only [A]
    exact div_le_div_of_nonneg_left hXreal.le
      (mul_pos (by positivity) hloga) hdenomAM
  have hAs0 : 0 ≤ A s := by dsimp only [A]; positivity
  have hcoeffDiff : 0 ≤ A s - A n := sub_nonneg.mpr hAnAs
  have hcoeffBound : A s - A n ≤ A (m : ℝ) - A n :=
    sub_le_sub_right hAsAm _
  have hPs0 : 0 ≤ P s := by
    dsimp only [P]
    exact div_nonneg (Int.fract_nonneg _) hlogs.le
  have hPn0 : 0 ≤ P n := by
    dsimp only [P]
    exact div_nonneg (Int.fract_nonneg _) hlogn.le
  have hPs : P s ≤ 1 / Real.log (m : ℝ) := by
    dsimp only [P]
    calc
      Int.fract ((X : ℝ) / s) / Real.log s ≤ 1 / Real.log s :=
        div_le_div_of_nonneg_right
          (Int.fract_lt_one ((X : ℝ) / s)).le hlogs.le
      _ ≤ 1 / Real.log (m : ℝ) :=
        one_div_le_one_div_of_le hlogm hlogMS
  have hPn : P n ≤ 1 / Real.log (m : ℝ) := by
    dsimp only [P]
    calc
      Int.fract ((X : ℝ) / n) / Real.log n ≤ 1 / Real.log n :=
        div_le_div_of_nonneg_right
          (Int.fract_lt_one ((X : ℝ) / n)).le hlogn.le
      _ ≤ 1 / Real.log (m : ℝ) :=
        one_div_le_one_div_of_le hlogm (hlogMS.trans hlogSN)
  have hPdiff : |P s - P n| ≤ 2 / Real.log (m : ℝ) := by
    calc
      |P s - P n| ≤ |P s| + |P n| := abs_sub _ _
      _ = P s + P n := by rw [abs_of_nonneg hPs0, abs_of_nonneg hPn0]
      _ ≤ 1 / Real.log (m : ℝ) + 1 / Real.log (m : ℝ) :=
        add_le_add hPs hPn
      _ = 2 / Real.log (m : ℝ) := by ring
  have hFs := roughSaiasFullyRealBuchstabNormalIntegrand_eq_rho_sub_fractional
    (X := X) hsOne
  have hFn := roughSaiasFullyRealBuchstabNormalIntegrand_eq_rho_sub_fractional
    (X := X) hnOne
  rw [hFs, hFn]
  change |(A s * H s - P s) - (A n * H n - P n)| ≤ _
  calc
    |(A s * H s - P s) - (A n * H n - P n)| ≤
        |A s * H s - A n * H n| + |P s - P n| := by
      have := abs_sub (A s * H s - A n * H n) (P s - P n)
      convert this using 1
      all_goals ring
    _ ≤ ((A s - A n) * |H n| + A s * |H s - H n|) +
        |P s - P n| := by
      have hmain : |A s * H s - A n * H n| ≤
          (A s - A n) * |H n| + A s * |H s - H n| := by
        calc
          |A s * H s - A n * H n| =
              |(A s - A n) * H n + A s * (H s - H n)| := by
            congr 1
            ring
          _ ≤ |(A s - A n) * H n| + |A s * (H s - H n)| :=
            abs_add_le _ _
          _ = (A s - A n) * |H n| + A s * |H s - H n| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hcoeffDiff,
              abs_of_nonneg hAs0]
      exact add_le_add hmain le_rfl
    _ ≤ (A s - A n) * 16 +
          A s * ((rho (u n) - rho (u (m : ℝ))) +
            roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m) +
        2 / Real.log (m : ℝ) := by
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left hHn hcoeffDiff)
          (mul_le_mul_of_nonneg_left hHdiff hAs0))
        hPdiff
    _ ≤ 16 * (A (m : ℝ) - A n) +
          A (a : ℝ) * ((rho (u n) - rho (u (m : ℝ))) +
            roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m) +
        2 / Real.log (m : ℝ) := by
      have hfirst := mul_le_mul_of_nonneg_right hcoeffBound (by norm_num : (0 : ℝ) ≤ 16)
      have hsecond := mul_le_mul_of_nonneg_right (hAsAm.trans hAmAa) hHdiffNonneg
      nlinarith
    _ = 16 *
          ((X : ℝ) / ((m : ℝ) * Real.log (m : ℝ)) -
            (X : ℝ) /
              (((m + 1 : ℕ) : ℝ) * Real.log ((m + 1 : ℕ) : ℝ))) +
        ((X : ℝ) / ((a : ℝ) * Real.log (a : ℝ))) *
          ((rho (Real.log ((X : ℝ) / (m + 1 : ℕ)) /
                  Real.log ((m + 1 : ℕ) : ℝ)) -
              rho (Real.log ((X : ℝ) / (m : ℝ)) /
                  Real.log (m : ℝ))) +
            roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m) +
        2 / Real.log (m : ℝ) := by
      rfl

/-- The paired natural cell itself satisfies the same quadrature ledger,
with `20/log m` added for the exact real-quotient endpoint correction. -/
private theorem roughSaiasFullyRealNaturalBuchstabCellRemainder_abs_le_lowerLedger
    {X a b m : ℕ} (hX : 0 < X) (ha3 : 3 ≤ a) (hab : a ≤ b)
    (hbX : b ≤ X) (hm : m ∈ Finset.Ico a b)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    |roughSaiasFullyRealNaturalBuchstabCellRemainder X m| ≤
      16 *
          ((X : ℝ) / ((m : ℝ) * Real.log (m : ℝ)) -
            (X : ℝ) /
              (((m + 1 : ℕ) : ℝ) * Real.log ((m + 1 : ℕ) : ℝ))) +
        ((X : ℝ) / ((a : ℝ) * Real.log (a : ℝ))) *
          ((rho (Real.log ((X : ℝ) / (m + 1 : ℕ)) /
                  Real.log ((m + 1 : ℕ) : ℝ)) -
              rho (Real.log ((X : ℝ) / (m : ℝ)) /
                  Real.log (m : ℝ))) +
            roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger
              X a m) +
        22 / Real.log (m : ℝ) := by
  have hmData := Finset.mem_Ico.mp hm
  have ha2 : 2 ≤ a := by omega
  have hm3 : 3 ≤ m := ha3.trans hmData.1
  have hnextX : m + 1 ≤ X := by omega
  have hmOne : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
  have hnextOne : (1 : ℝ) < ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < m + 1 by omega)
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos hmOne
  have hlogNext : 0 < Real.log ((m + 1 : ℕ) : ℝ) := Real.log_pos hnextOne
  have hlogmNext : Real.log (m : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (Nat.le_succ m))
  have hinvNext : 20 / Real.log ((m + 1 : ℕ) : ℝ) ≤
      20 / Real.log (m : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hlogm hlogmNext
  have hendpoint :
      roughSaiasFullyRealBuchstabNormalIntegrand X (m + 1 : ℕ) -
          roughSaiasNaturalQuotientThetaWeight X (m + 1) =
        roughSaiasFractionalCorrectionThetaWeight X (m + 1) := by
    rw [roughSaiasFullyRealBuchstabNormalIntegrand_nat,
      roughSaiasNormalFormThetaWeight_eq_natural_add_fractional]
    ring
  have hendpointAbs :
      |roughSaiasFullyRealBuchstabNormalIntegrand X (m + 1 : ℕ) -
          roughSaiasNaturalQuotientThetaWeight X (m + 1)| ≤
        20 / Real.log (m : ℝ) := by
    rw [hendpoint]
    exact (roughSaiasFractionalCorrectionThetaWeight_abs_le_twenty_inv_log
      hX ha3 (by omega : a ≤ m + 1) hnextX hu5).trans hinvNext
  let C : ℝ :=
    16 *
        ((X : ℝ) / ((m : ℝ) * Real.log (m : ℝ)) -
          (X : ℝ) /
            (((m + 1 : ℕ) : ℝ) * Real.log ((m + 1 : ℕ) : ℝ))) +
      ((X : ℝ) / ((a : ℝ) * Real.log (a : ℝ))) *
        ((rho (Real.log ((X : ℝ) / (m + 1 : ℕ)) /
                Real.log ((m + 1 : ℕ) : ℝ)) -
            rho (Real.log ((X : ℝ) / (m : ℝ)) /
                Real.log (m : ℝ))) +
          roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger
            X a m) +
      22 / Real.log (m : ℝ)
  have hpoint : ∀ s ∈ Set.Icc (m : ℝ) (m + 1 : ℕ),
      |roughSaiasFullyRealBuchstabNormalIntegrand X s -
          roughSaiasNaturalQuotientThetaWeight X (m + 1)| ≤ C := by
    intro s hs
    have hcontinuous :=
      roughSaiasFullyRealBuchstabNormalIntegrand_cell_abs_sub_right_le
        hX ha3 hab hbX hm hu5 hs
    calc
      |roughSaiasFullyRealBuchstabNormalIntegrand X s -
          roughSaiasNaturalQuotientThetaWeight X (m + 1)| ≤
        |roughSaiasFullyRealBuchstabNormalIntegrand X s -
            roughSaiasFullyRealBuchstabNormalIntegrand X (m + 1 : ℕ)| +
          |roughSaiasFullyRealBuchstabNormalIntegrand X (m + 1 : ℕ) -
            roughSaiasNaturalQuotientThetaWeight X (m + 1)| :=
        abs_sub_le _ _ _
      _ ≤
        (16 *
            ((X : ℝ) / ((m : ℝ) * Real.log (m : ℝ)) -
              (X : ℝ) /
                (((m + 1 : ℕ) : ℝ) * Real.log ((m + 1 : ℕ) : ℝ))) +
          ((X : ℝ) / ((a : ℝ) * Real.log (a : ℝ))) *
            ((rho (Real.log ((X : ℝ) / (m + 1 : ℕ)) /
                    Real.log ((m + 1 : ℕ) : ℝ)) -
                rho (Real.log ((X : ℝ) / (m : ℝ)) /
                    Real.log (m : ℝ))) +
              roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger
                X a m) +
          2 / Real.log (m : ℝ)) +
        20 / Real.log (m : ℝ) := add_le_add hcontinuous hendpointAbs
      _ = C := by
        dsimp only [C]
        ring
  rw [roughSaiasFullyRealNaturalBuchstabCellRemainder_eq_integral
    ha2 hab hbX hu5 hm]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun s : ℝ =>
      roughSaiasFullyRealBuchstabNormalIntegrand X s -
        roughSaiasNaturalQuotientThetaWeight X (m + 1))
    (C := C) (a := (m : ℝ)) (b := (m + 1 : ℕ)) (fun s hsU => by
      rw [Real.norm_eq_abs]
      apply hpoint s
      have hs := Set.uIoc_subset_uIcc hsU
      simpa [Set.uIcc_of_le
        (by norm_num : (m : ℝ) ≤ (m + 1 : ℕ))] using hs)
  simpa only [Real.norm_eq_abs, Nat.cast_add, Nat.cast_one,
    add_sub_cancel_left, abs_one, mul_one, C] using hnorm

/-- The complete lower fully-real natural-cell block has the required
inverse-log-square size.  The constant `40` records, without hidden
cancellation, coefficient drift (`16`), rho variation (`1`), continuous
fractional variation (`1` after scaling), and the two endpoint sawtooth
costs (`22`). -/
theorem abs_sum_roughSaiasFullyRealNaturalCells_lower_le_forty_invLogSq
    {X a b : ℕ} (hX : 0 < X) (ha3 : 3 ≤ a) (hab : a ≤ b)
    (hbX : b ≤ X) (hbSqrt : b ≤ Nat.sqrt X + 1)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    |∑ m ∈ Finset.Ico a b,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m| ≤
      40 * (X : ℝ) / Real.log (a : ℝ) ^ 2 := by
  rcases hab.eq_or_lt with rfl | habLt
  · simp only [Finset.Ico_self, Finset.sum_empty, abs_zero]
    positivity
  · let A : ℕ → ℝ := fun m =>
      (X : ℝ) / ((m : ℝ) * Real.log (m : ℝ))
    let R : ℕ → ℝ := fun m =>
      rho (Real.log ((X : ℝ) / (m : ℝ)) / Real.log (m : ℝ))
    let B : ℕ → ℝ := fun m =>
      roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m
    have hloga : 0 < Real.log (a : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < a by omega))
    have ha2 : 2 ≤ a := by omega
    have hapos : 0 < (a : ℝ) := by positivity
    have hlogale : Real.log (a : ℝ) ≤ (a : ℝ) := by
      have h := Real.log_le_sub_one_of_pos hapos
      linarith
    have hdenom : Real.log (a : ℝ) ^ 2 ≤
        (a : ℝ) * Real.log (a : ℝ) := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right hlogale hloga.le
    have hAaTarget : A a ≤ (X : ℝ) / Real.log (a : ℝ) ^ 2 := by
      dsimp only [A]
      exact div_le_div_of_nonneg_left (by positivity)
        (sq_pos_of_pos hloga) hdenom
    have haSqrt : a ≤ Nat.sqrt X := by omega
    have hlengthSqrt : b - a ≤ Nat.sqrt X := by omega
    have hmulNat : (b - a) * a ≤ X := by
      calc
        (b - a) * a ≤ Nat.sqrt X * Nat.sqrt X :=
          Nat.mul_le_mul hlengthSqrt haSqrt
        _ = (Nat.sqrt X) ^ 2 := by ring
        _ ≤ X := Nat.sqrt_le' X
    have hlength : ((Finset.Ico a b).card : ℝ) ≤ (X : ℝ) / (a : ℝ) := by
      rw [Nat.card_Ico]
      apply (le_div_iff₀ hapos).2
      exact_mod_cast hmulNat
    have hcoeffTelescope :
        (∑ m ∈ Finset.Ico a b, (A m - A (m + 1))) = A a - A b := by
      simpa only [neg_sub_neg] using
        (Finset.sum_Ico_sub (fun m => -A m) hab)
    have hcoeffSum :
        (∑ m ∈ Finset.Ico a b, (A m - A (m + 1))) ≤ A a := by
      rw [hcoeffTelescope]
      have hAb : 0 ≤ A b := by
        dsimp only [A]
        have hbOne : (1 : ℝ) < (b : ℝ) := by
          exact_mod_cast (show 1 < b by omega)
        exact div_nonneg (by positivity)
          (mul_nonneg (by positivity) (Real.log_pos hbOne).le)
      linarith
    have hrhoSum :
        (∑ m ∈ Finset.Ico a b, (R (m + 1) - R m)) ≤ 1 := by
      calc
        (∑ m ∈ Finset.Ico a b, (R (m + 1) - R m)) ≤
            ∑ m ∈ Finset.Ico a b, |R (m + 1) - R m| := by
          apply Finset.sum_le_sum
          intro m _hm
          exact le_abs_self _
        _ ≤ 1 := by
          simpa only [R] using
            (sum_abs_rho_fullyRealHyperbolaLogRatio_succ_sub_le_one
              hX ha2 habLt.le hbX hu5)
    have hBSum : (∑ m ∈ Finset.Ico a b, B m) ≤
        2 / Real.log (a : ℝ) := by
      simpa only [B] using
        (sum_roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger_le_two_inv_log
          hX ha2 habLt.le hbX hu5)
    have hinvSum :
        (∑ m ∈ Finset.Ico a b, 1 / Real.log (m : ℝ)) ≤
          ((Finset.Ico a b).card : ℝ) / Real.log (a : ℝ) := by
      calc
        (∑ m ∈ Finset.Ico a b, 1 / Real.log (m : ℝ)) ≤
            ∑ _m ∈ Finset.Ico a b, 1 / Real.log (a : ℝ) := by
          apply Finset.sum_le_sum
          intro m hm
          have hmData := Finset.mem_Ico.mp hm
          have hlogam : Real.log (a : ℝ) ≤ Real.log (m : ℝ) :=
            Real.log_le_log hapos (by exact_mod_cast hmData.1)
          exact one_div_le_one_div_of_le hloga hlogam
        _ = ((Finset.Ico a b).card : ℝ) / Real.log (a : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
    have hInvAtA :
        ((Finset.Ico a b).card : ℝ) / Real.log (a : ℝ) ≤ A a := by
      dsimp only [A]
      calc
        ((Finset.Ico a b).card : ℝ) / Real.log (a : ℝ) ≤
            ((X : ℝ) / (a : ℝ)) / Real.log (a : ℝ) :=
          div_le_div_of_nonneg_right hlength hloga.le
        _ = (X : ℝ) / ((a : ℝ) * Real.log (a : ℝ)) := by ring
    have hJTarget : A a * (2 / Real.log (a : ℝ)) ≤
        (X : ℝ) / Real.log (a : ℝ) ^ 2 := by
      have htwoA : (2 : ℝ) / (a : ℝ) ≤ 1 := by
        rw [div_le_one hapos]
        exact_mod_cast ha2
      have htargetNonneg : 0 ≤ (X : ℝ) / Real.log (a : ℝ) ^ 2 := by
        positivity
      calc
        A a * (2 / Real.log (a : ℝ)) =
            ((2 : ℝ) / (a : ℝ)) *
              ((X : ℝ) / Real.log (a : ℝ) ^ 2) := by
          dsimp only [A]
          field_simp [hapos.ne', hloga.ne']
        _ ≤ 1 * ((X : ℝ) / Real.log (a : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right htwoA htargetNonneg
        _ = (X : ℝ) / Real.log (a : ℝ) ^ 2 := one_mul _
    let E : ℕ → ℝ := fun m =>
      16 * (A m - A (m + 1)) +
        A a * ((R (m + 1) - R m) + B m) +
        22 * (1 / Real.log (m : ℝ))
    have hcells :
        |∑ m ∈ Finset.Ico a b,
            roughSaiasFullyRealNaturalBuchstabCellRemainder X m| ≤
          ∑ m ∈ Finset.Ico a b, E m := by
      calc
        |∑ m ∈ Finset.Ico a b,
            roughSaiasFullyRealNaturalBuchstabCellRemainder X m| ≤
          ∑ m ∈ Finset.Ico a b,
            |roughSaiasFullyRealNaturalBuchstabCellRemainder X m| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ Finset.Ico a b, E m := by
          apply Finset.sum_le_sum
          intro m hm
          have hcell :=
            roughSaiasFullyRealNaturalBuchstabCellRemainder_abs_le_lowerLedger
              hX ha3 habLt.le hbX hm hu5
          simpa only [E, A, R, B, div_eq_mul_inv, one_mul] using hcell
    have hEexpand :
        (∑ m ∈ Finset.Ico a b, E m) =
          (∑ m ∈ Finset.Ico a b, 16 * (A m - A (m + 1))) +
          (∑ m ∈ Finset.Ico a b, A a * (R (m + 1) - R m)) +
          (∑ m ∈ Finset.Ico a b, A a * B m) +
          ∑ m ∈ Finset.Ico a b, 22 * (1 / Real.log (m : ℝ)) := by
      simp only [E, mul_add, Finset.sum_add_distrib]
      ring
    have htermCoeff :
        (∑ m ∈ Finset.Ico a b, 16 * (A m - A (m + 1))) ≤
          16 * A a := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hcoeffSum (by norm_num)
    have htermRho :
        (∑ m ∈ Finset.Ico a b, A a * (R (m + 1) - R m)) ≤ A a := by
      rw [← Finset.mul_sum]
      have hAa0 : 0 ≤ A a := by dsimp only [A]; positivity
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hrhoSum hAa0
    have htermB :
        (∑ m ∈ Finset.Ico a b, A a * B m) ≤
          (X : ℝ) / Real.log (a : ℝ) ^ 2 := by
      rw [← Finset.mul_sum]
      exact (mul_le_mul_of_nonneg_left hBSum (by dsimp only [A]; positivity)).trans
        hJTarget
    have htermInv :
        (∑ m ∈ Finset.Ico a b, 22 * (1 / Real.log (m : ℝ))) ≤
          22 * A a := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hinvSum.trans hInvAtA) (by norm_num)
    rw [hEexpand] at hcells
    calc
      |∑ m ∈ Finset.Ico a b,
          roughSaiasFullyRealNaturalBuchstabCellRemainder X m| ≤
        (∑ m ∈ Finset.Ico a b, 16 * (A m - A (m + 1))) +
        (∑ m ∈ Finset.Ico a b, A a * (R (m + 1) - R m)) +
        (∑ m ∈ Finset.Ico a b, A a * B m) +
        ∑ m ∈ Finset.Ico a b, 22 * (1 / Real.log (m : ℝ)) := hcells
      _ ≤ 16 * A a + A a +
          (X : ℝ) / Real.log (a : ℝ) ^ 2 + 22 * A a :=
        add_le_add (add_le_add (add_le_add htermCoeff htermRho) htermB) htermInv
      _ = 39 * A a + (X : ℝ) / Real.log (a : ℝ) ^ 2 := by ring
      _ ≤ 39 * ((X : ℝ) / Real.log (a : ℝ) ^ 2) +
          (X : ℝ) / Real.log (a : ℝ) ^ 2 :=
        add_le_add
          (mul_le_mul_of_nonneg_left hAaTarget
            (by norm_num : (0 : ℝ) ≤ 39))
          le_rfl
      _ = 40 * (X : ℝ) / Real.log (a : ℝ) ^ 2 := by ring













































/-! ## Closed sharp defect and endpoint witnesses -/











end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_002 := by
  exact @Erdos390.WholePaper.abs_sum_roughSaiasFullyRealNaturalCells_lower_le_forty_invLogSq
