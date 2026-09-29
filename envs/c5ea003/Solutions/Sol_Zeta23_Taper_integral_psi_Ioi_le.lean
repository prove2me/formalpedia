-- Prove2me | solution 1 for Zeta23.Taper.integral_psi_Ioi_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T01:25:35.631995+00:00
-- url     : https://prove2.me/submissions/dec8d4ba-ff07-4276-bec7-64f817f49324

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Taper_Basic
import Theorems.Thm_Zeta23_Taper_four_le_cRho
import Theorems.Thm_Zeta23_Taper_psi_mul_sq_le
import Theorems.Thm_Zeta23_Taper_psi_nonneg

-- from Zeta23.Taper.Decay
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — Taper/Decay.lean.  Two sections, `GBounds` and `Psi`.
Names and statements here are used by the umbrella Zeta23/Taper.lean (and the Params layer)
and by downstream files.
Canonical text: the paper, §2.2 [subsec:family].  See Zeta23/Taper.lean header for conventions:
generic parameters (ϱ : ℝ → ℝ) (L w : ℝ); paper's side condition is 1 ≤ w ≤ L/8 [eq:wrange];
each lemma carries the minimal hypothesis it needs.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23

namespace Taper

/-! ### [eq:gbounds]: "`(L − 2w − |y|)₊ ≤ g(y) ≤ A_φ(y) ≤ (L − |y|)₊`" -/

section GBounds

variable {ϱ : ℝ → ℝ} {L w : ℝ}

/-! Helpers on the autocorrelation `(v ⋆ v)(y) := ∫ v(u) v(u+y) du` [eq:PhigA] of a real function:
evenness (translation invariance of Lebesgue measure), the interval-overlap length
`|[−M,M] ∩ ([−M,M] − y)| = (2M − |y|)₊`, the two comparison bounds, vanishing for `|y| ≥ 2M`,
and continuity in `y` (parametric integral over the compact support). -/








/-! The taper instances: `A_φ = φ ⋆ φ` (support `[−L/2, L/2]`, `0 ≤ φ ≤ 1`) and `g = φ² ⋆ φ²`
(plateau `φ² = 1` on `[−L/2+w, L/2−w]`). -/















end GBounds

/-! ### [eq:psidef]: "`max(|φ̂(r)|, |Φ(r)|) ≤ ψ(r) := min(L, 2/|r|, c_ϱ/(w r²))`"
We give the three bounds separately (division-free) and then the `ψ` form. -/

section Psi 
variable {ϱ : ℝ → ℝ} {L w : ℝ}

/-! #### Helpers: first-order [eq:hfbound], and the ℂ-valued φ² -/




















theorem psi_le_L (_hϱ : TaperProfile ϱ) (_hw : 1 ≤ w) (_hwL : 2 * w ≤ L) (r : ℝ) :
    psi ϱ L w r ≤ L := by
  unfold psi
  split_ifs with hr
  · exact le_rfl
  · exact min_le_left _ _

theorem psi_mul_abs_le (_hϱ : TaperProfile ϱ) (_hw : 1 ≤ w) (_hwL : 2 * w ≤ L) (r : ℝ) :
    psi ϱ L w r * |r| ≤ 2 := by
  unfold psi
  split_ifs with hr
  · simp [hr]
  · have hra : 0 < |r| := abs_pos.mpr hr
    rw [← le_div_iff₀ hra]
    exact (min_le_right _ _).trans (min_le_left _ _)


/-! #### Measurability / integrability of ψ -/



/-- For r > 0: ψ(r) ≤ (c_ϱ/w) · r^{−2} (rpow form). -/
theorem psi_le_rpow_neg_two (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 2 * w ≤ L) {r : ℝ}
    (hr : 0 < r) : psi ϱ L w r ≤ cRho ϱ / w * r ^ (-2:ℝ) := by
  have h := psi_mul_sq_le hϱ hw hwL r
  rw [Real.rpow_neg hr.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast,
    ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact h











/-! ### [eq:psiints].  We record upper bounds — every downstream citation of [eq:psiints] in §5 is
"≪ log L" or "≤ 8L".  (Paper: "a direct computation (split at |r| = 2/L and |r| = c_ϱ/2w; note
c_ϱ L/4w ≥ 1 by [eq:wrange]) gives Ψ₀ = 4 + 2 log(c_ϱ L/4w), ∫ψ²|r| = 8 + 8 log(c_ϱ L/4w),
∫ψ² ≤ 8L".) -/

/-- Constants for [eq:psiints]: A := 2/L ≤ B := c_ϱ/(2w) ("note c_ϱ L/4w ≥ 1 by
[eq:wrange]"), B/A = c_ϱ L/(4w). -/
theorem psiints_consts (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    0 < 2 / L ∧ 0 < cRho ϱ / (2 * w) ∧ 2 / L ≤ cRho ϱ / (2 * w) ∧
    (cRho ϱ / (2 * w)) / (2 / L) = cRho ϱ * L / (4 * w) := by
  have hc := four_le_cRho hϱ
  have hL : 0 < L := by linarith
  have hw0 : 0 < w := by linarith
  refine ⟨by positivity, by positivity, ?_, ?_⟩
  · rw [div_le_div_iff₀ hL (by positivity)]; nlinarith
  · field_simp; ring

/-- On (0, ∞), ψ is dominated by the three-piece majorant L·1_{(0,A]} + (2/r)·1_{(A,B]} +
(c_ϱ/w) r⁻²·1_{(B,∞)} (in fact with equality; ≤ is all we use). -/
theorem indicator_psi_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) (r : ℝ) :
    (Ioi (0:ℝ)).indicator (psi ϱ L w) r
      ≤ (Ioc 0 (2 / L)).indicator (fun _ => L) r
        + (Ioc (2 / L) (cRho ϱ / (2 * w))).indicator (fun x => 2 * x⁻¹) r
        + (Ioi (cRho ϱ / (2 * w))).indicator (fun x => cRho ϱ / w * x ^ (-2:ℝ)) r := by
  obtain ⟨hA, hB, hAB, -⟩ := psiints_consts hϱ hw hwL
  have hwL' : 2 * w ≤ L := by linarith
  by_cases hr : r ∈ Ioi (0:ℝ)
  · have hr0 : 0 < r := hr
    rw [indicator_of_mem hr]
    by_cases h1 : r ≤ 2 / L
    · rw [indicator_of_mem (show r ∈ Ioc 0 (2 / L) from ⟨hr0, h1⟩),
        indicator_of_notMem (show r ∉ Ioc (2 / L) (cRho ϱ / (2 * w)) from
          fun h => not_lt.mpr h1 h.1),
        indicator_of_notMem (show r ∉ Ioi (cRho ϱ / (2 * w)) from
          fun h => not_lt.mpr (h1.trans hAB) h), add_zero, add_zero]
      exact psi_le_L hϱ hw hwL' r
    · rw [not_le] at h1
      by_cases h2 : r ≤ cRho ϱ / (2 * w)
      · rw [indicator_of_notMem (show r ∉ Ioc 0 (2 / L) from fun h => not_le.mpr h1 h.2),
          indicator_of_mem (show r ∈ Ioc (2 / L) (cRho ϱ / (2 * w)) from ⟨h1, h2⟩),
          indicator_of_notMem (show r ∉ Ioi (cRho ϱ / (2 * w)) from fun h => not_lt.mpr h2 h),
          zero_add, add_zero]
        have := psi_mul_abs_le hϱ hw hwL' r
        rw [abs_of_pos hr0] at this
        rw [← div_eq_mul_inv, le_div_iff₀ hr0]
        exact this
      · rw [not_le] at h2
        rw [indicator_of_notMem (show r ∉ Ioc 0 (2 / L) from fun h => not_le.mpr h1 h.2),
          indicator_of_notMem (show r ∉ Ioc (2 / L) (cRho ϱ / (2 * w)) from
            fun h => not_le.mpr h2 h.2),
          indicator_of_mem (show r ∈ Ioi (cRho ϱ / (2 * w)) from h2), zero_add, zero_add]
        exact psi_le_rpow_neg_two hϱ hw hwL' hr0
  · rw [indicator_of_notMem hr]
    have hr0 : r ≤ 0 := not_lt.mp hr
    rw [indicator_of_notMem (show r ∉ Ioc 0 (2 / L) from fun h => hr h.1),
      indicator_of_notMem (show r ∉ Ioc (2 / L) (cRho ϱ / (2 * w)) from
        fun h => hr (lt_trans hA h.1)),
      indicator_of_notMem (show r ∉ Ioi (cRho ϱ / (2 * w)) from fun h => hr (lt_trans hB h)),
      add_zero, add_zero]







/-! #### Generic moment bounds from |F| ≤ ψ-type information -/














end Psi


end Taper

end Zeta23
open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
open Zeta23
open Taper
variable {ϱ : ℝ → ℝ} {L w : ℝ}

theorem solution (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ r in Ioi 0, psi ϱ L w r ≤ 4 + 2 * Real.log (cRho ϱ * L / (4 * w)) := by
  obtain ⟨hA, hB, hAB, hBA⟩ := psiints_consts hϱ hw hwL
  have hwL' : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hw0 : 0 < w := by linarith
  have hc0 : 0 < cRho ϱ := lt_of_lt_of_le (by norm_num) (four_le_cRho hϱ)
  set A := 2 / L with hAdef
  set B := cRho ϱ / (2 * w) with hBdef
  -- integrability of the three pieces
  have i1 : IntegrableOn (fun _ : ℝ => L) (Ioc 0 A) := integrableOn_const (by simp)
  have i2 : IntegrableOn (fun x : ℝ => 2 * x⁻¹) (Ioc A B) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    exact continuousOn_const.mul
      ((continuousOn_inv₀).mono fun x hx => ne_of_gt (lt_of_lt_of_le hA hx.1))
  have i3 : IntegrableOn (fun x : ℝ => cRho ϱ / w * x ^ (-2:ℝ)) (Ioi B) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hB).const_mul _
  have I1 := i1.integrable_indicator measurableSet_Ioc
  have I2 := i2.integrable_indicator measurableSet_Ioc
  have I3 := i3.integrable_indicator measurableSet_Ioi
  -- the three integrals
  have e1 : ∫ r, (Ioc 0 A).indicator (fun _ => L) r = 2 := by
    rw [integral_indicator measurableSet_Ioc, setIntegral_const, measureReal_def,
      Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul, sub_zero, hAdef]
    field_simp
  have e2 : ∫ r, (Ioc A B).indicator (fun x => 2 * x⁻¹) r = 2 * Real.log (B / A) := by
    rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hAB,
      intervalIntegral.integral_const_mul, integral_inv]
    exact fun h => by
      have := (Set.mem_uIcc.mp h); rcases this with h | h <;> linarith [h.1, h.2]
  have e3 : ∫ r, (Ioi B).indicator (fun x => cRho ϱ / w * x ^ (-2:ℝ)) r = 2 := by
    rw [integral_indicator measurableSet_Ioi, integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num) hB]
    norm_num
    rw [Real.rpow_neg_one, hBdef]
    field_simp
  have I12 : Integrable (fun r => (Ioc 0 A).indicator (fun _ => L) r
      + (Ioc A B).indicator (fun x => 2 * x⁻¹) r) := I1.add I2
  calc ∫ r in Ioi 0, psi ϱ L w r
      = ∫ r, (Ioi (0:ℝ)).indicator (psi ϱ L w) r := (integral_indicator measurableSet_Ioi).symm
    _ ≤ ∫ r, ((Ioc 0 A).indicator (fun _ => L) r
          + (Ioc A B).indicator (fun x => 2 * x⁻¹) r
          + (Ioi B).indicator (fun x => cRho ϱ / w * x ^ (-2:ℝ)) r) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun r => ?_) ((I1.add I2).add I3)
          (Eventually.of_forall fun r => indicator_psi_le hϱ hw hwL r)
        exact Set.indicator_nonneg (fun x _ => psi_nonneg hϱ hw hwL' x) _
    _ = (∫ r, ((Ioc 0 A).indicator (fun _ => L) r + (Ioc A B).indicator (fun x => 2 * x⁻¹) r))
          + ∫ r, (Ioi B).indicator (fun x => cRho ϱ / w * x ^ (-2:ℝ)) r := integral_add I12 I3
    _ = ((∫ r, (Ioc 0 A).indicator (fun _ => L) r) + ∫ r, (Ioc A B).indicator (fun x => 2 * x⁻¹) r)
          + ∫ r, (Ioi B).indicator (fun x => cRho ϱ / w * x ^ (-2:ℝ)) r := by
        rw [integral_add I1 I2]
    _ = 2 + 2 * Real.log (B / A) + 2 := by rw [e1, e2, e3]
    _ = 4 + 2 * Real.log (cRho ϱ * L / (4 * w)) := by rw [hBA]; ring
