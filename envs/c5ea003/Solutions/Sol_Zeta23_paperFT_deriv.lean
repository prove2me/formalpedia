-- Prove2me | solution 1 for Zeta23.paperFT_deriv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:01:05.862378+00:00
-- url     : https://prove2.me/submissions/df21cd43-fe30-4324-b824-f8738d75b515

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs

-- from Zeta23.Poisson.PaperFT
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The paper's Fourier convention and the bound [eq:hfbound].

Reference: the paper, §2.1 [subsec:weil].
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23

/-! `Zeta23.paperFT (f : ℝ → ℂ) (z : ℂ) : ℂ := ∫ u, f u * cexp (I * z * u)` is defined in
`Zeta23/Defs.lean`: the paper's convention [subsec:weil] "h_f(z) := f̂(z) = ∫ f(u) e^{izu} du",
sign `+i`, no `2π`, complex argument.  This file supplies the dictionary to Mathlib's `𝓕`
(`∫ f(v) e^{-2πi v w} dv`) and the decay bound [eq:hfbound]. -/

theorem paperFT_def (f : ℝ → ℂ) (z : ℂ) : paperFT f z = ∫ u : ℝ, f u * cexp (I * z * u) := rfl

/-! Mathlib's `integral_const_mul` / `integral_mul_const` are stated for a general `RCLike L`,
and their instance path (RCLike-derived `NormedAddCommGroup ℂ`) does not match the
directly-synthesized `Complex.instNormedAddCommGroup` under `rw`'s reducible unification.
These ℂ-specialized restatements (same proofs) rewrite reliably. -/





/-! ### [eq:hfbound]

"`|h_f(x+iy)| ≤ e^{|y|Λ_f} min(‖f‖₁, ‖f''‖₁ |x+iy|⁻²)`, `supp f ⊂ [−Λ_f, Λ_f]`, by two integrations
by parts (`h_f(z) = (iz)⁻² ∫ f''(u) e^{izu} du` and `|e^{izu}| = e^{−yu} ≤ e^{|y|Λ_f}` on
`supp f`)."  We prove the two bounds separately, in multiplied-out form. -/










end Zeta23
open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
open Zeta23

theorem solution {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hsupp : HasCompactSupport f) (z : ℂ) :
    paperFT (deriv f) z = -(I * z) * paperFT f z := by
  have hf' : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hfd : ∀ x, HasDerivAt f (deriv f x) x := fun x => (hf.differentiable (by norm_num) x).hasDerivAt
  have hv : ∀ x : ℝ, HasDerivAt (fun u : ℝ => cexp (I * z * u)) (I * z * cexp (I * z * x)) x := by
    intro x
    have h1 : HasDerivAt (fun u : ℝ => I * z * u) (I * z * 1) x :=
      ((hasDerivAt_id x).ofReal_comp).const_mul (I * z)
    simpa [mul_comm] using h1.cexp
  have hcv : Continuous (fun u : ℝ => cexp (I * z * u)) := by fun_prop
  have hcv' : Continuous (fun u : ℝ => I * z * cexp (I * z * u)) := by fun_prop
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := f)
    (v := fun u : ℝ => cexp (I * z * u)) (u' := deriv f)
    (v' := fun x : ℝ => I * z * cexp (I * z * x))
    (fun x _ => hfd x) (fun x _ => hv x)
    ((hf.continuous.mul hcv').integrable_of_hasCompactSupport hsupp.mul_right)
    ((hf'.mul hcv).integrable_of_hasCompactSupport hsupp.deriv.mul_right)
    ((hf.continuous.mul hcv).integrable_of_hasCompactSupport hsupp.mul_right)
  have : (fun u : ℝ => f u * (I * z * cexp (I * z * u))) = fun u => (I * z) * (f u * cexp (I * z * u)) := by
    funext u; ring
  rw [this, integral_const_mul] at key
  have key' : I * z * paperFT f z = -paperFT (deriv f) z := by
    rw [paperFT_def, paperFT_def]; exact key
  linear_combination key'
