-- Prove2me | solution 1 for Zeta23.LeafIntegrals.W3_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:42:44.905363+00:00
-- url     : https://prove2.me/submissions/4c09540c-5868-4e83-9681-03173277edac

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

-- from Zeta23.Defs.LeafIntegrals
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
Zeta23/Defs/LeafIntegrals.lean — self-contained elementary integral bounds used as drop-ins by
§5's lem:ends (Zeta23/PrimeSideA/EndsE1.lean). Imports only Mathlib.
-/

open MeasureTheory Real Set

noncomputable section

namespace Zeta23.LeafIntegrals




/-! ## (W3) core: ∫ ψ(r)² (2+|r|)² dr ≤ 18 L² + 18 (c/w)² for any even 0 ≤ ψ ≤ L with ψ(r) ≤ c/(w r²) -/


end Zeta23.LeafIntegrals
end
open MeasureTheory Real Set

theorem solution (ψ : ℝ → ℝ) (L c w : ℝ) (hw : 0 < w)
    (habs : ∀ r, ψ |r| = ψ r) (hnn : ∀ r, 0 ≤ ψ r) (hleL : ∀ r, ψ r ≤ L)
    (hdecay : ∀ r, r ≠ 0 → ψ r ≤ c / (w * r ^ 2)) (hint : Integrable (fun r => ψ r ^ 2)) :
    Integrable (fun r => ψ r ^ 2 * (2 + |r|) ^ 2) ∧
    ∫ r, ψ r ^ 2 * (2 + |r|) ^ 2 ≤ 18 * L ^ 2 + 18 * (c / w) ^ 2 := by
  have hK : 0 ≤ (c / w) ^ 2 := sq_nonneg _
  -- pointwise bounds
  have hP1 : ∀ r : ℝ, |r| ≤ 1 → ψ r ^ 2 * (2 + |r|) ^ 2 ≤ 9 * L ^ 2 := by
    intro r hr
    have h1 : ψ r ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (hnn r) (hleL r) 2
    have h2 : (2 + |r|) ^ 2 ≤ 9 := by nlinarith [abs_nonneg r]
    nlinarith [sq_nonneg (ψ r), sq_nonneg (2 + |r|)]
  have hP2 : ∀ r : ℝ, 1 ≤ |r| → ψ r ^ 2 * (2 + |r|) ^ 2 ≤ 9 * (c / w) ^ 2 * (r ^ 2)⁻¹ := by
    intro r hr
    have hr0 : r ≠ 0 := by intro h; rw [h, abs_zero] at hr; linarith
    have hr2 : 0 < r ^ 2 := by positivity
    have hψ : ψ r ≤ c / w * (r ^ 2)⁻¹ := by
      have := hdecay r hr0; rwa [show c / (w * r ^ 2) = c / w * (r ^ 2)⁻¹ by field_simp] at this
    have hψ0 := hnn r
    have h1 : ψ r ^ 2 ≤ (c / w) ^ 2 * (r ^ 2)⁻¹ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hψ0 hψ 2
    have h2 : (2 + |r|) ^ 2 ≤ 9 * r ^ 2 := by
      have : r ^ 2 = |r| ^ 2 := (sq_abs r).symm
      rw [this]; nlinarith
    calc ψ r ^ 2 * (2 + |r|) ^ 2 ≤ ((c / w) ^ 2 * (r ^ 2)⁻¹ ^ 2) * (9 * r ^ 2) :=
          mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
      _ = 9 * (c / w) ^ 2 * (r ^ 2)⁻¹ := by field_simp
  -- integrable majorant 18 (L² + (c/w)²) / (1 + r²)
  have hmaj : ∀ r : ℝ, ψ r ^ 2 * (2 + |r|) ^ 2 ≤ 18 * (L ^ 2 + (c / w) ^ 2) * (1 + r ^ 2)⁻¹ := by
    intro r
    have h1r : 0 < 1 + r ^ 2 := by positivity
    rcases le_or_gt |r| 1 with hr | hr
    · have hf := hP1 r hr
      have : r ^ 2 ≤ 1 := by have := (sq_abs r).symm; nlinarith [abs_nonneg r]
      rw [← div_eq_mul_inv, le_div_iff₀ h1r]
      nlinarith
    · have hf := hP2 r hr.le
      have hr2 : 1 ≤ r ^ 2 := by have := (sq_abs r).symm; nlinarith
      have hrpos : 0 < r ^ 2 := by positivity
      rw [← div_eq_mul_inv, le_div_iff₀ h1r]
      rw [← div_eq_mul_inv, le_div_iff₀ hrpos] at hf
      nlinarith
  have hmeas : AEStronglyMeasurable (fun r => ψ r ^ 2 * (2 + |r|) ^ 2) volume :=
    hint.aestronglyMeasurable.mul (by fun_prop : Continuous fun r : ℝ => (2 + |r|) ^ 2).aestronglyMeasurable
  have hInt : Integrable (fun r => ψ r ^ 2 * (2 + |r|) ^ 2) := by
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (18 * (L ^ 2 + (c / w) ^ 2))) hmeas
      (Filter.Eventually.of_forall fun r => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hmaj r
  refine ⟨hInt, ?_⟩
  -- reduce to (0, ∞) by evenness
  set g : ℝ → ℝ := fun u => ψ u ^ 2 * (2 + u) ^ 2 with hg
  have hfg : (fun r => ψ r ^ 2 * (2 + |r|) ^ 2) = fun r => g |r| := by
    funext r; simp only [hg, habs]
  rw [hfg, integral_comp_abs]
  have hgInt : IntegrableOn g (Ioi 0) := by
    refine IntegrableOn.congr_fun hInt.integrableOn (fun u hu => ?_) measurableSet_Ioi
    simp only [hg, abs_of_pos (mem_Ioi.mp hu)]
  -- split (0,∞) = (0,1] ∪ (1,∞)
  have hsplit : ∫ u in Ioi (0:ℝ), g u = (∫ u in Ioc (0:ℝ) 1, g u) + ∫ u in Ioi (1:ℝ), g u := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hgInt.mono_set Ioc_subset_Ioi_self) (hgInt.mono_set (Ioi_subset_Ioi zero_le_one))]
  have hJ1 : ∫ u in Ioc (0:ℝ) 1, g u ≤ 9 * L ^ 2 := by
    have h := setIntegral_mono_on (hgInt.mono_set Ioc_subset_Ioi_self)
      (integrableOn_const (μ := volume) (s := Ioc (0:ℝ) 1) (C := 9 * L ^ 2) (by simp))
      measurableSet_Ioc
      (fun u hu => by
        have hu1 : |u| ≤ 1 := by rw [abs_of_pos hu.1]; exact hu.2
        simpa only [hg, abs_of_pos hu.1] using hP1 u hu1)
    simpa using h
  have hJ2 : ∫ u in Ioi (1:ℝ), g u ≤ 9 * (c / w) ^ 2 := by
    have hrp : IntegrableOn (fun u : ℝ => 9 * (c / w) ^ 2 * u ^ (-2:ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _
    have h := setIntegral_mono_on (hgInt.mono_set (Ioi_subset_Ioi zero_le_one)) hrp
      measurableSet_Ioi
      (fun u hu => by
        have hu0 : 0 < u := lt_trans one_pos hu
        have hu1 : 1 ≤ |u| := by rw [abs_of_pos hu0]; exact hu.le
        have := hP2 u hu1
        simp only [hg]
        rw [abs_of_pos hu0] at this
        rwa [Real.rpow_neg hu0.le, Real.rpow_two])
    refine h.trans (le_of_eq ?_)
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) one_pos]
    norm_num
  linarith
