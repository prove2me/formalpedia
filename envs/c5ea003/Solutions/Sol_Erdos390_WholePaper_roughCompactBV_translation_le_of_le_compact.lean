-- Prove2me | solution 1 for Erdos390.WholePaper.roughCompactBV_translation_le_of_le_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:42:30.805907+00:00
-- url     : https://prove2.me/submissions/2742f49b-8764-4e99-bde7-9ed96d3d4571

import Definitions.Def_erdos390_remaining_analytic_propositions_008
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

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

/-- The ordered form of the compact `L¹` translation estimate. -/
theorem roughCompactBV_translation_le_of_le
    {f : ℝ → ℝ}
    (hfvar : eVariationOn f (Icc (-5 : ℝ) 5) ≤ ENNReal.ofReal 2)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 5)
    (hb : b ∈ Icc (0 : ℝ) 5) (hab : a ≤ b) :
    (∫ v in (0 : ℝ)..5, |f (a - v) - f (b - v)|) ≤
      2 * (b - a) := by
  let s : Set ℝ := Icc (-5 : ℝ) 5
  let V : ℝ → ℝ := fun x => variationOnFromTo f s (-5) x
  let W : ℝ → ℝ := fun x => V x - f x
  have hfvar' : eVariationOn f s ≤ ENNReal.ofReal 2 := by
    simpa only [s] using hfvar
  have hfBV : BoundedVariationOn f s :=
    (hfvar'.trans_lt ENNReal.ofReal_lt_top).ne
  have hfLocal : LocallyBoundedVariationOn f s :=
    hfBV.locallyBoundedVariationOn
  have hminus : (-5 : ℝ) ∈ s := by simp [s]
  have hfive : (5 : ℝ) ∈ s := by simp [s]
  have hVmono : MonotoneOn V s := by
    simpa only [V] using
      variationOnFromTo.monotoneOn hfLocal hminus
  have hWmono : MonotoneOn W s := by
    simpa only [W, V, Pi.sub_apply] using
      variationOnFromTo.sub_self_monotoneOn hfLocal hminus

  have hVint : ∀ {x y : ℝ}, x ∈ s → y ∈ s →
      IntervalIntegrable V volume x y := by
    intro x y hx hy
    have hxy : uIcc x y ⊆ s := by
      simpa only [s] using
        (uIcc_subset_Icc
          (show x ∈ Icc (-5 : ℝ) 5 by simpa only [s] using hx)
          (show y ∈ Icc (-5 : ℝ) 5 by simpa only [s] using hy))
    exact (hVmono.mono hxy).intervalIntegrable
  have hWint : ∀ {x y : ℝ}, x ∈ s → y ∈ s →
      IntervalIntegrable W volume x y := by
    intro x y hx hy
    have hxy : uIcc x y ⊆ s := by
      simpa only [s] using
        (uIcc_subset_Icc
          (show x ∈ Icc (-5 : ℝ) 5 by simpa only [s] using hx)
          (show y ∈ Icc (-5 : ℝ) 5 by simpa only [s] using hy))
    exact (hWmono.mono hxy).intervalIntegrable

  have hVtranslated : ∀ (c : ℝ), c ∈ Icc (0 : ℝ) 5 →
      IntervalIntegrable (fun v => V (c - v)) volume 0 5 := by
    intro c hc
    have hcMinus : c - 5 ∈ s := by
      dsimp only [s]
      constructor <;> linarith [hc.1, hc.2]
    have hcS : c ∈ s := by
      dsimp only [s]
      constructor <;> linarith [hc.1, hc.2]
    have hcomp := (hVint hcMinus hcS).comp_sub_left c
    convert hcomp.symm using 1 <;> ring
  have hWtranslated : ∀ (c : ℝ), c ∈ Icc (0 : ℝ) 5 →
      IntervalIntegrable (fun v => W (c - v)) volume 0 5 := by
    intro c hc
    have hcMinus : c - 5 ∈ s := by
      dsimp only [s]
      constructor <;> linarith [hc.1, hc.2]
    have hcS : c ∈ s := by
      dsimp only [s]
      constructor <;> linarith [hc.1, hc.2]
    have hcomp := (hWint hcMinus hcS).comp_sub_left c
    convert hcomp.symm using 1 <;> ring
  have hftranslated : ∀ (c : ℝ), c ∈ Icc (0 : ℝ) 5 →
      IntervalIntegrable (fun v => f (c - v)) volume 0 5 := by
    intro c hc
    simpa only [W, sub_sub_cancel] using
      (hVtranslated c hc).sub (hWtranslated c hc)

  have haS : a ∈ s := by
    dsimp only [s]
    constructor <;> linarith [ha.1, ha.2]
  have hbS : b ∈ s := by
    dsimp only [s]
    constructor <;> linarith [hb.1, hb.2]
  have haMinus : a - 5 ∈ s := by
    dsimp only [s]
    constructor <;> linarith [ha.1, ha.2]
  have hbMinus : b - 5 ∈ s := by
    dsimp only [s]
    constructor <;> linarith [hb.1, hb.2]

  have hpointwise : ∀ v ∈ Icc (0 : ℝ) 5,
      |f (a - v) - f (b - v)| ≤ V (b - v) - V (a - v) := by
    intro v hv
    have hav : a - v ∈ s := by
      dsimp only [s]
      constructor <;> linarith [ha.1, ha.2, hv.1, hv.2]
    have hbv : b - v ∈ s := by
      dsimp only [s]
      constructor <;> linarith [hb.1, hb.2, hv.1, hv.2]
    have habv : a - v ≤ b - v := sub_le_sub_right hab v
    have hdist :
        dist (f (a - v)) (f (b - v)) ≤
          variationOnFromTo f s (a - v) (b - v) := by
      rw [variationOnFromTo.eq_of_le f s habv, dist_edist]
      apply ENNReal.toReal_mono (hfLocal (a - v) (b - v) hav hbv)
      apply eVariationOn.edist_le f
      exact ⟨hav, le_rfl, habv⟩
      exact ⟨hbv, habv, le_rfl⟩
    have hadd := variationOnFromTo.add hfLocal hminus hav hbv
    have hvariation :
        variationOnFromTo f s (a - v) (b - v) =
          V (b - v) - V (a - v) := by
      change V (a - v) + variationOnFromTo f s (a - v) (b - v) =
        V (b - v) at hadd
      linarith
    calc
      |f (a - v) - f (b - v)| =
          dist (f (a - v)) (f (b - v)) := by rw [Real.dist_eq]
      _ ≤ variationOnFromTo f s (a - v) (b - v) := hdist
      _ = V (b - v) - V (a - v) := hvariation

  have hintegral :
      (∫ v in (0 : ℝ)..5, |f (a - v) - f (b - v)|) ≤
        ∫ v in (0 : ℝ)..5, V (b - v) - V (a - v) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((hftranslated a ha).sub (hftranslated b hb)).abs
      ((hVtranslated b hb).sub (hVtranslated a ha))
    exact hpointwise

  have hsplitB :
      (∫ t in b - 5..a, V t) + (∫ t in a..b, V t) =
        ∫ t in b - 5..b, V t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hVint hbMinus haS) (hVint haS hbS)
  have hsplitA :
      (∫ t in a - 5..b - 5, V t) + (∫ t in b - 5..a, V t) =
        ∫ t in a - 5..a, V t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hVint haMinus hbMinus) (hVint hbMinus haS)
  have hshift :
      (∫ v in (0 : ℝ)..5, V (b - v) - V (a - v)) =
        (∫ t in a..b, V t) - ∫ t in a - 5..b - 5, V t := by
    rw [intervalIntegral.integral_sub (hVtranslated b hb)
        (hVtranslated a ha),
      intervalIntegral.integral_comp_sub_left V b,
      intervalIntegral.integral_comp_sub_left V a]
    simp only [sub_zero]
    rw [← hsplitB, ← hsplitA]
    ring

  have hupper :
      (∫ t in a..b, V t) ≤ (b - a) * V 5 := by
    calc
      (∫ t in a..b, V t) ≤ ∫ _t in a..b, V 5 := by
        apply intervalIntegral.integral_mono_on hab
          (hVint haS hbS) intervalIntegrable_const
        intro t ht
        have htS : t ∈ s := by
          dsimp only [s]
          constructor <;> linarith [ha.1, hb.2, ht.1, ht.2]
        exact hVmono htS hfive (by linarith [ht.2, hb.2])
      _ = (b - a) * V 5 := by
        simp only [intervalIntegral.integral_const, smul_eq_mul]
  have hlower :
      (b - a) * V (-5) ≤ ∫ t in a - 5..b - 5, V t := by
    calc
      (b - a) * V (-5) =
          ∫ _t in a - 5..b - 5, V (-5) := by
        simp only [intervalIntegral.integral_const, smul_eq_mul]
        ring
      _ ≤ ∫ t in a - 5..b - 5, V t := by
        apply intervalIntegral.integral_mono_on (by linarith)
          intervalIntegrable_const (hVint haMinus hbMinus)
        intro t ht
        have htS : t ∈ s := by
          dsimp only [s]
          constructor <;> linarith [ha.1, hb.2, ht.1, ht.2]
        exact hVmono hminus htS (by linarith [ht.1, ha.1])
  have hboundary :
      (∫ t in a..b, V t) - (∫ t in a - 5..b - 5, V t) ≤
        (b - a) * (V 5 - V (-5)) := by
    calc
      (∫ t in a..b, V t) - (∫ t in a - 5..b - 5, V t) ≤
          (b - a) * V 5 - (b - a) * V (-5) :=
        sub_le_sub hupper hlower
      _ = (b - a) * (V 5 - V (-5)) := by ring

  have hVminus : V (-5) = 0 := by
    dsimp only [V]
    exact variationOnFromTo.self f s (-5)
  have hVfive : V 5 = (eVariationOn f s).toReal := by
    dsimp only [V]
    rw [variationOnFromTo.eq_of_le f s (by norm_num)]
    simp only [s, inter_self]
  have hVspan : V 5 - V (-5) = (eVariationOn f s).toReal := by
    rw [hVfive, hVminus, sub_zero]
  have htotal : (eVariationOn f s).toReal ≤ 2 := by
    have h := ENNReal.toReal_mono
      (show ENNReal.ofReal (2 : ℝ) ≠ ∞ by simp) hfvar'
    simpa using h

  calc
    (∫ v in (0 : ℝ)..5, |f (a - v) - f (b - v)|) ≤
        ∫ v in (0 : ℝ)..5, V (b - v) - V (a - v) := hintegral
    _ = (∫ t in a..b, V t) - ∫ t in a - 5..b - 5, V t := hshift
    _ ≤ (b - a) * (V 5 - V (-5)) := hboundary
    _ = (b - a) * (eVariationOn f s).toReal := by rw [hVspan]
    _ ≤ (b - a) * 2 :=
      mul_le_mul_of_nonneg_left htotal (sub_nonneg.mpr hab)
    _ = 2 * (b - a) := by ring



/-! ## Unconditional forms of the normalization estimates -/









end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_019 := by
  exact @Erdos390.WholePaper.roughCompactBV_translation_le_of_le
