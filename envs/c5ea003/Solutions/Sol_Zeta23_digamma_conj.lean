-- Prove2me | solution 1 for Zeta23.digamma_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:09:32.831079+00:00
-- url     : https://prove2.me/submissions/0384df07-b2ab-4fb2-afa9-deb2a456c66d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs

-- from Zeta23.GammaFacts
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/GammaFacts.lean — the even and smooth clauses of H-Γ [eq:mufacts].

Paper [eq:mufacts] asserts: "μ is even, smooth, increasing in |τ|, μ ≥ μ(0) > −1,
μ(τ) = (1/2π)log(|τ|/2π) + O(τ⁻²), μ′(τ) ≪ |τ|⁻¹ (|τ| ≥ 1)" plus [eq:muints].

This file proves the EVEN and SMOOTH clauses against Mathlib's
Complex.digamma (= logDeriv Gamma):
  • digamma_conj : Γ'/Γ commutes with conjugation (from Complex.Gamma_conj +
    deriv_conj_conj);
  • mu_even : μ(−τ) = μ(τ);
  • mu_smooth : ContDiff ℝ ∞ μ (Γ is holomorphic hence analytic on Re > 0,
    so digamma is analytic there; compose with the affine line τ ↦ 1/4 + iτ/2).

The remaining clauses (monotonicity in |τ|, μ(0) > −1, the Stirling asymptotic
with O(τ⁻²), the derivative bound, and [eq:muints]) are the fields of
Zeta23.GammaFacts in Hypotheses.lean; they are proved in the files under
Zeta23/GammaFacts/ and assembled in Zeta23/GammaFacts/Complete.lean (`gammaFacts`).
The route: the digamma partial-fraction series
  digamma z = −γ_E + Σ_{n≥0} (1/(n+1) − 1/(n+z))  on ℂ ∖ (−ℕ)
(Zeta23/GammaFacts/Series.lean), from which monotonicity and μ ≥ μ(0) are termwise
monotonicity of (n+σ)/((n+σ)²+t²) in t², μ(0) > −1 is a finite partial-sum bound,
and the derivative bound is termwise differentiation; the Stirling clause uses a
vertical-line Stirling estimate (Zeta23/GammaFacts/StirlingVert.lean,
Zeta23/Analytic/Stirling.lean), and the integrals [eq:muints] follow by integrating
the asymptotic (Zeta23/GammaFacts/IntMu.lean).
-/

namespace Zeta23

open Complex

open scoped ContDiff





-- The set_option below is Mathlib's own workaround for instance-path defeq on
-- IsScalarTower ℝ ℂ ℂ (cf. Analysis/CStarAlgebra/ContinuousFunctionalCalculus/
-- RealImaginaryPart.lean, "fails to find IsScalarTower ℝ ℂ A").

end Zeta23
open Zeta23
open Complex
open scoped ContDiff

theorem solution (z : ℂ) :
    Complex.digamma ((starRingEnd ℂ) z) = (starRingEnd ℂ) (Complex.digamma z) := by
  have hG : (starRingEnd ℂ) ∘ Complex.Gamma ∘ (starRingEnd ℂ) = Complex.Gamma := by
    funext w
    simp only [Function.comp_apply]
    rw [Complex.Gamma_conj]
    exact Complex.conj_conj _
  have hd : deriv Complex.Gamma ((starRingEnd ℂ) z)
      = (starRingEnd ℂ) (deriv Complex.Gamma z) := by
    conv_lhs => rw [← hG, deriv_conj_conj]
    simp only [Function.comp_apply, Complex.conj_conj]
  simp only [Complex.digamma_def, logDeriv_apply]
  rw [hd, Complex.Gamma_conj, ← map_div₀]
