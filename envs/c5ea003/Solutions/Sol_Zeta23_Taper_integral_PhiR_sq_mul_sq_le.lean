-- Prove2me | solution 1 for Zeta23.Taper.integral_PhiR_sq_mul_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T01:36:31.023845+00:00
-- url     : https://prove2.me/submissions/fd388aa9-0cb9-4df4-9224-92872eaa497e

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
import Theorems.Thm_Zeta23_Taper_abs_PhiR_mul_abs_le
import Theorems.Thm_Zeta23_Taper_abs_PhiR_mul_sq_le
import Theorems.Thm_Zeta23_Taper_four_le_cRho

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























/-! #### Measurability / integrability of ψ -/




/-- The common integrable plateau majorant: `a` on [−1,1] and `b·|r|⁻²` outside (ψ: a = L, b = c_ϱ/w;
r²-moments: a = 4, b = C²).  ∫ = 2a + 2b. -/
noncomputable def plateauMaj (a b : ℝ) (r : ℝ) : ℝ :=
  (Icc (-1:ℝ) 1).indicator (fun _ => a) r
    + b * ((Ioi (1:ℝ)).indicator (fun x => x ^ (-2:ℝ)) r + (Ioi (1:ℝ)).indicator (fun x => x ^ (-2:ℝ)) (-r))

theorem tail_indicator_integrable :
    Integrable ((Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ))) :=
  (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).integrable_indicator measurableSet_Ioi

theorem plateauMaj_integrable (a b : ℝ) : Integrable (plateauMaj a b) :=
  ((integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))).add
    ((tail_indicator_integrable.add tail_indicator_integrable.comp_neg).const_mul _)

theorem integral_plateauMaj (a b : ℝ) : ∫ r, plateauMaj a b r = 2 * a + 2 * b := by
  have h1 : Integrable ((Icc (-1:ℝ) 1).indicator (fun _ => a)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
  have h2 := tail_indicator_integrable
  have h3 : Integrable (fun r => (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) (-r)) := h2.comp_neg
  have e1 : ∫ r, (Icc (-1:ℝ) 1).indicator (fun _ => a) r = 2 * a := by
    rw [integral_indicator measurableSet_Icc, setIntegral_const, measureReal_def,
      Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num), smul_eq_mul]
    norm_num
  have e2 : ∫ r, (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) r = 1 := by
    rw [integral_indicator measurableSet_Ioi, integral_Ioi_rpow_of_lt (by norm_num) one_pos]
    norm_num
  have e3 : ∫ r, (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) (-r) = 1 := by
    rw [MeasureTheory.integral_neg_eq_self ((Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ))) volume]
    exact e2
  have h23 : Integrable (fun r => (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) r
      + (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) (-r)) := h2.add h3
  unfold plateauMaj
  calc ∫ r, ((Icc (-1:ℝ) 1).indicator (fun _ => a) r
        + b * ((Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) r
          + (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) (-r)))
      = (∫ r, (Icc (-1:ℝ) 1).indicator (fun _ => a) r)
        + ∫ r, b * ((Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) r
          + (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) (-r)) :=
        integral_add h1 (h23.const_mul _)
    _ = 2 * a + b * ((∫ r, (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) r)
          + ∫ r, (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) (-r)) := by
        rw [e1, integral_const_mul]
        congr 2
        exact integral_add h2 h3
    _ = 2 * a + 2 * b := by rw [e2, e3]; ring







/-! ### [eq:psiints].  We record upper bounds — every downstream citation of [eq:psiints] in §5 is
"≪ log L" or "≤ 8L".  (Paper: "a direct computation (split at |r| = 2/L and |r| = c_ϱ/2w; note
c_ϱ L/4w ≥ 1 by [eq:wrange]) gives Ψ₀ = 4 + 2 log(c_ϱ L/4w), ∫ψ²|r| = 8 + 8 log(c_ϱ L/4w),
∫ψ² ≤ 8L".) -/









/-! #### Generic moment bounds from |F| ≤ ψ-type information -/


/-- The integrable majorant for the r²-moments: 4 on [−1,1] and C²|r|⁻² outside. -/
noncomputable abbrev momMaj (C : ℝ) : ℝ → ℝ := plateauMaj 4 (C ^ 2)

theorem momMaj_integrable (C : ℝ) : Integrable (momMaj C) := plateauMaj_integrable _ _

theorem integral_momMaj (C : ℝ) : ∫ r, momMaj C r = 8 + 2 * C ^ 2 := by
  rw [integral_plateauMaj]; ring

/-- Pointwise: |F(r)|·|r| ≤ 2 and |F(r)|·r² ≤ C give F(r)² r² ≤ momMaj C r. -/
theorem sq_mul_sq_le_momMaj {F : ℝ → ℝ} {C : ℝ} (_hC : 0 ≤ C)
    (h1 : ∀ r, |F r| * |r| ≤ 2) (h2 : ∀ r, |F r| * r ^ 2 ≤ C) (r : ℝ) :
    F r ^ 2 * r ^ 2 ≤ momMaj C r := by
  have hind : ∀ s : ℝ, 0 ≤ (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) s := fun s =>
    Set.indicator_nonneg (fun x hx => Real.rpow_nonneg (le_trans zero_le_one (le_of_lt hx)) _) _
  have hsq : ∀ s : ℝ, 1 < s → F r ^ 2 * s ^ 2 * s ^ 2 ≤ C ^ 2 → F r ^ 2 * s ^ 2 ≤ C ^ 2 * s ^ (-2:ℝ) := by
    intro s hs h
    have hs0 : 0 < s := by linarith
    rw [Real.rpow_neg hs0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast,
      ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    exact h
  unfold momMaj plateauMaj
  by_cases h : r ∈ Icc (-1:ℝ) 1
  · rw [Set.indicator_of_mem h]
    have hb : F r ^ 2 * r ^ 2 ≤ 4 := by
      have := h1 r
      have h0 : 0 ≤ |F r| * |r| := by positivity
      calc F r ^ 2 * r ^ 2 = (|F r| * |r|) ^ 2 := by rw [mul_pow, sq_abs, sq_abs]
        _ ≤ 2 ^ 2 := pow_le_pow_left₀ h0 this 2
        _ = 4 := by norm_num
    nlinarith [hind r, hind (-r), sq_nonneg C]
  · rw [Set.indicator_of_notMem h, zero_add]
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    have hFsq : F r ^ 2 * r ^ 2 * r ^ 2 ≤ C ^ 2 := by
      have := h2 r
      have h0 : 0 ≤ |F r| * r ^ 2 := by positivity
      calc F r ^ 2 * r ^ 2 * r ^ 2 = (|F r| * r ^ 2) ^ 2 := by rw [mul_pow, sq_abs]; ring
        _ ≤ C ^ 2 := pow_le_pow_left₀ h0 this 2
    rcases h with h | h
    · -- r < -1
      rw [Set.indicator_of_notMem (show r ∉ Ioi (1:ℝ) by simp; linarith),
        Set.indicator_of_mem (show -r ∈ Ioi (1:ℝ) by simp; linarith), zero_add]
      have := hsq (-r) (by linarith) (by simpa using hFsq)
      simpa using this
    · -- 1 < r
      rw [Set.indicator_of_mem (show r ∈ Ioi (1:ℝ) from h),
        Set.indicator_of_notMem (show -r ∉ Ioi (1:ℝ) by simp; linarith), add_zero]
      exact hsq r h hFsq


theorem integral_sq_mul_sq_le_of_bounds {F : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (h1 : ∀ r, |F r| * |r| ≤ 2) (h2 : ∀ r, |F r| * r ^ 2 ≤ C) :
    ∫ r, F r ^ 2 * r ^ 2 ≤ 8 + 2 * C ^ 2 := by
  rw [← integral_momMaj C]
  exact integral_mono_of_nonneg (Eventually.of_forall fun r => by positivity)
    (momMaj_integrable C) (Eventually.of_forall fun r => sq_mul_sq_le_momMaj hC h1 h2 r)







end Psi


end Taper

end Zeta23
open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
open Zeta23
open Taper
variable {ϱ : ℝ → ℝ} {L w : ℝ}

theorem solution (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ x, PhiR ϱ L w x ^ 2 * x ^ 2 ≤ 8 + 2 * (cRho ϱ / w) ^ 2 := by
  have hw0 : 0 < w := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  exact integral_sq_mul_sq_le_of_bounds
    (div_nonneg (le_trans (by norm_num) (four_le_cRho hϱ)) hw0.le)
    (abs_PhiR_mul_abs_le hϱ hw0 hwL') (abs_PhiR_mul_sq_le hϱ hw hwL')
