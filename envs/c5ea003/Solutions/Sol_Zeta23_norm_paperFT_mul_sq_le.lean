-- Prove2me | solution 1 for Zeta23.norm_paperFT_mul_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:00:19.930595+00:00
-- url     : https://prove2.me/submissions/da4b6216-f324-43e8-8e66-9fa3d975a764

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
import Theorems.Thm_Zeta23_norm_paperFT_le
import Theorems.Thm_Zeta23_paperFT_deriv

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


/-! Mathlib's `integral_const_mul` / `integral_mul_const` are stated for a general `RCLike L`,
and their instance path (RCLike-derived `NormedAddCommGroup ℂ`) does not match the
directly-synthesized `Complex.instNormedAddCommGroup` under `rw`'s reducible unification.
These ℂ-specialized restatements (same proofs) rewrite reliably. -/





/-! ### [eq:hfbound]

"`|h_f(x+iy)| ≤ e^{|y|Λ_f} min(‖f‖₁, ‖f''‖₁ |x+iy|⁻²)`, `supp f ⊂ [−Λ_f, Λ_f]`, by two integrations
by parts (`h_f(z) = (iz)⁻² ∫ f''(u) e^{izu} du` and `|e^{izu}| = e^{−yu} ≤ e^{|y|Λ_f}` on
`supp f`)."  We prove the two bounds separately, in multiplied-out form. -/





/-- Two integrations by parts: `(f'')^(z) = −z² · f̂(z)`, i.e. "`h_f(z) = (iz)⁻² ∫ f''(u)e^{izu} du`". -/
theorem paperFT_deriv_deriv {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f)
    (z : ℂ) : paperFT (deriv (deriv f)) z = -z ^ 2 * paperFT f z := by
  have h1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  rw [paperFT_deriv h1 hsupp.deriv, paperFT_deriv (hf.of_le (by norm_num)) hsupp]
  ring_nf
  rw [I_sq]
  ring

theorem hasCompactSupport_of_support_subset_abs {E : Type*} [Zero E] {f : ℝ → E} {Λ : ℝ}
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) : HasCompactSupport f := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -Λ) (b := Λ)) ?_
  intro u hu
  exact abs_le.mp (hsupp u hu)

theorem tsupport_subset_of_support_subset_abs {E : Type*} [Zero E] {f : ℝ → E} {Λ : ℝ}
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) : tsupport f ⊆ Icc (-Λ) Λ :=
  closure_minimal (fun u hu => abs_le.mp (hsupp u hu)) isClosed_Icc



end Zeta23
open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
open Zeta23

theorem solution {f : ℝ → ℂ} {Λ : ℝ} (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) (z : ℂ) :
    ‖paperFT f z‖ * ‖z‖ ^ 2 ≤ Real.exp (|z.im| * Λ) * ∫ u, ‖deriv (deriv f) u‖ := by
  have hcs : HasCompactSupport f := hasCompactSupport_of_support_subset_abs hsupp
  have hts := tsupport_subset_of_support_subset_abs hsupp
  have hsupp2 : ∀ u, deriv (deriv f) u ≠ 0 → |u| ≤ Λ := by
    intro u hu
    have : u ∈ tsupport f :=
      tsupport_deriv_subset (support_deriv_subset (Function.mem_support.mpr hu))
    exact abs_le.mpr (hts this)
  have hint : Integrable (deriv (deriv f)) :=
    (hf.deriv'.continuous_deriv le_rfl).integrable_of_hasCompactSupport hcs.deriv.deriv
  have := norm_paperFT_le hint hsupp2 z
  rw [paperFT_deriv_deriv hf hcs, norm_mul, norm_neg, norm_pow, mul_comm] at this
  exact this
