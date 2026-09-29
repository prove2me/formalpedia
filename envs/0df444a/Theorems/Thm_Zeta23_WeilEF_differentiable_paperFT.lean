-- Prove2me | Theorems.Thm_Zeta23_WeilEF_differentiable_paperFT
-- name    : Zeta23.WeilEF.differentiable_paperFT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:48:42.946899+00:00
-- url     : https://prove2.me/theorems/f3550c4c-b07a-4ef8-9c11-982fbd0b0e0c
-- title:
--   The paper Fourier transform of a continuous compactly supported function is entire
-- statement:
--   For $k : \mathbb{R} \to \mathbb{C}$, the project's "paper Fourier transform" is defined for complex arguments by
--   $$\widehat{k}(z) \;=\; \operatorname{paperFT} k\,(z) \;=\; \int_{\mathbb{R}} k(u)\, e^{izu}\, du,$$
--   following the paper's normalization $h_f(z) := \int f(u) e^{izu}\,du$ [subsec:weil].
--
--   The theorem asserts: if $k$ is continuous and has compact support, then $\operatorname{paperFT} k$ is an entire function, i.e. complex-differentiable at every point of $\mathbb{C}$. The proof is differentiation under the integral sign, legitimate because the integrand is supported in a fixed compact set.
--
--   Analyticity of the transform is what makes the test function $H(s) = \widehat{k}((s - 1/2)/i)$ (the function `Hfn k`) analytic in $s$, which is needed for every contour argument in the Weil explicit-formula development; it is consumed by `EF_lit_zeta`, `gamma_line_shift`, `integrable_Fline`, `rectangle_identity`, and `verticals_eq`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/VerticalLine.lean#L495-L549

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

theorem Zeta23.WeilEF.differentiable_paperFT {k : ℝ → ℂ} (hk : Continuous k) (hkc : HasCompactSupport k) :
    Differentiable ℂ (paperFT k) := by sorry
