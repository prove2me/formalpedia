-- Prove2me | Theorems.Thm_Zeta23_WeilEF_gamma_line_shift
-- name    : Zeta23.WeilEF.gamma_line_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:53:15.332304+00:00
-- url     : https://prove2.me/theorems/4fb2a541-7fa0-4580-a53a-eb8dae896c13
-- title:
--   Archimedean line shift: moving the $\Gamma_{\mathbb{R}}'/\Gamma_{\mathbb{R}}$ integrals to the critical line
-- statement:
--   Let $k : \mathbb{R} \to \mathbb{C}$ be $C^2$ with compact support, let $\widehat{k}(z) = \int k(u)e^{izu}\,du$ be its paper Fourier transform, and let $H(s) = \widehat{k}((s-1/2)/i)$ (the project's `Hfn k`). Let $\Gamma_{\mathbb{R}}(s) = \pi^{-s/2}\Gamma(s/2)$, and fix $c$ with $1 < c \le 3/2$.
--
--   Then the Archimedean part of the two vertical-line integrals shifts to the critical line:
--   $$\int_{\mathbb{R}} \bigl[H(c+it) + H(1-c-it)\bigr]\,\frac{\Gamma_{\mathbb{R}}'}{\Gamma_{\mathbb{R}}}(c+it)\,dt \;=\; \int_{\mathbb{R}} \widehat{k}(t)\,\Bigl[\frac{\Gamma_{\mathbb{R}}'}{\Gamma_{\mathbb{R}}}\Bigl(\frac12+it\Bigr) + \frac{\Gamma_{\mathbb{R}}'}{\Gamma_{\mathbb{R}}}\Bigl(\frac12-it\Bigr)\Bigr]\,dt.$$
--   The shift is a contour deformation across the rectangle between $\operatorname{Re} s = 1/2$ and $\operatorname{Re} s = c$: $\Gamma_{\mathbb{R}}'/\Gamma_{\mathbb{R}}$ has no poles in $\operatorname{Re} s > 0$, and the horizontal pieces vanish because the digamma growth bound is beaten by the quadratic decay [eq:hfbound] of $\widehat{k}$ along horizontal directions.
--
--   Combined with `gammaR_bracket`, this puts the Archimedean term of the Weil explicit formula into its final critical-line form; it is consumed by `EF_lit_zeta`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/VerticalLine.lean#L640-L785, docstring tag [eq:hfbound]

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_ExplicitFormula
import Definitions.Def_Zeta23_GammaFacts_Series
import Definitions.Def_Zeta23_GammaFacts_StirlingVert
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_WeilEF_VerticalLine

open Zeta23
open WeilEF
open Complex MeasureTheory
open scoped ArithmeticFunction

theorem Zeta23.WeilEF.gamma_line_shift {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3/2) :
    ∫ t : ℝ, (Hfn k (c + t * I) + Hfn k (1 - c - t * I)) * logDeriv Complex.Gammaℝ (c + t * I)
      = ∫ t : ℝ, paperFT k t
        * (logDeriv Complex.Gammaℝ (1/2 + t * I) + logDeriv Complex.Gammaℝ (1/2 - t * I)) := by sorry
