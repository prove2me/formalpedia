-- Prove2me | solution 1 for Zeta23.Taper.autocorr_le_of_support
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T02:05:21.002636+00:00
-- url     : https://prove2.me/submissions/3aadec3e-3423-4ae7-b4e3-a353f3681fab

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


/-- `|[−M, M] ∩ ([−M, M] − y)| = max (2M − |y|) 0`. -/
theorem volume_Icc_inter_shift (M y : ℝ) :
    (volume (Icc (-M) M ∩ Icc (-M - y) (M - y))).toReal = max (2 * M - |y|) 0 := by
  rw [Icc_inter_Icc, Real.volume_Icc, ENNReal.toReal_ofReal']
  congr 1
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg h, max_eq_left (by linarith), min_eq_right (by linarith)]; ring
  · rw [abs_of_nonpos h, max_eq_right (by linarith), min_eq_left (by linarith)]; ring

theorem integrable_indicator_Icc_inter (M y : ℝ) :
    Integrable ((Icc (-M) M ∩ Icc (-M - y) (M - y)).indicator (1 : ℝ → ℝ)) := by
  rw [Icc_inter_Icc]
  exact (integrable_indicator_iff measurableSet_Icc).mpr
    ((integrableOn_const_iff).mpr (Or.inr (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)))





/-! The taper instances: `A_φ = φ ⋆ φ` (support `[−L/2, L/2]`, `0 ≤ φ ≤ 1`) and `g = φ² ⋆ φ²`
(plateau `φ² = 1` on `[−L/2+w, L/2−w]`). -/















end GBounds

/-! ### [eq:psidef]: "`max(|φ̂(r)|, |Φ(r)|) ≤ ψ(r) := min(L, 2/|r|, c_ϱ/(w r²))`"
We give the three bounds separately (division-free) and then the `ψ` form. -/

section Psi 
variable {ϱ : ℝ → ℝ} {L w : ℝ}

/-! #### Helpers: first-order [eq:hfbound], and the ℂ-valued φ² -/























/-! #### Measurability / integrability of ψ -/














/-! ### [eq:psiints].  We record upper bounds — every downstream citation of [eq:psiints] in §5 is
"≪ log L" or "≤ 8L".  (Paper: "a direct computation (split at |r| = 2/L and |r| = c_ϱ/2w; note
c_ϱ L/4w ≥ 1 by [eq:wrange]) gives Ψ₀ = 4 + 2 log(c_ϱ L/4w), ∫ψ²|r| = 8 + 8 log(c_ϱ L/4w),
∫ψ² ≤ 8L".) -/









/-! #### Generic moment bounds from |F| ≤ ψ-type information -/














end Psi


end Taper

end Zeta23
open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
open Zeta23
open Taper
variable {ϱ : ℝ → ℝ} {L w : ℝ}

theorem solution (v : ℝ → ℝ) {M : ℝ} (h0 : ∀ u, 0 ≤ v u) (h1 : ∀ u, v u ≤ 1)
    (hz : ∀ u, M ≤ |u| → v u = 0) (y : ℝ) :
    Params.autocorr v y ≤ max (2 * M - |y|) 0 := by
  unfold Params.autocorr
  set S := Icc (-M) M ∩ Icc (-M - y) (M - y) with hS
  have hSm : MeasurableSet S := measurableSet_Icc.inter measurableSet_Icc
  have hle : ∀ u, v u * v (u + y) ≤ S.indicator 1 u := by
    intro u
    by_cases hu : u ∈ S
    · rw [indicator_of_mem hu, Pi.one_apply]
      exact mul_le_one₀ (h1 u) (h0 _) (h1 _)
    · rw [indicator_of_notMem hu]
      simp only [hS, mem_inter_iff, mem_Icc, not_and_or, not_le] at hu
      rcases hu with (hu | hu) | (hu | hu)
      · rw [hz u (by linarith [neg_le_abs u]), zero_mul]
      · rw [hz u (by linarith [le_abs_self u]), zero_mul]
      · rw [hz (u + y) (by linarith [neg_le_abs (u + y)]), mul_zero]
      · rw [hz (u + y) (by linarith [le_abs_self (u + y)]), mul_zero]
  calc ∫ u, v u * v (u + y) ≤ ∫ u, S.indicator 1 u :=
        integral_mono_of_nonneg (ae_of_all _ fun u => mul_nonneg (h0 _) (h0 _))
          (integrable_indicator_Icc_inter M y) (ae_of_all _ hle)
    _ = (volume S).toReal := integral_indicator_one hSm
    _ = max (2 * M - |y|) 0 := volume_Icc_inter_shift M y
