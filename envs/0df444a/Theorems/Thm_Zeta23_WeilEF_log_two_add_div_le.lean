-- Prove2me | Theorems.Thm_Zeta23_WeilEF_log_two_add_div_le
-- name    : Zeta23.WeilEF.log_two_add_div_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:52:32.700505+00:00
-- url     : https://prove2.me/theorems/2b202cac-8d75-4d82-9bc3-869f4e3581ec
-- title:
--   Elementary bound: $\log(2+x)/(1+x^2) \le 6\,(1+x)^{-3/2}$ for $x \ge 0$
-- statement:
--   For every real $x \ge 0$,
--   $$\frac{\log(2 + x)}{1 + x^2} \;\le\; 6\,(1 + x)^{-3/2},$$
--   where the right-hand side uses the real power function. This is an elementary calculus inequality: the logarithm grows more slowly than any positive power, so the quadratic denominator on the left dominates the $3/2$-power decay on the right with a modest explicit constant.
--
--   In the project it packages the comparison "logarithmic growth times quadratic decay is integrable with $(1+x)^{-3/2}$ margin": it is consumed by `gamma_line_shift`, where the digamma growth $\log(2+|t|)$ of $\Gamma_{\mathbb{R}}'/\Gamma_{\mathbb{R}}$ multiplied by the $1/(1+t^2)$ decay of the Fourier transform of the test function must be dominated by an explicitly integrable function on the horizontal contour pieces.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/VerticalLine.lean#L551-L575

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

theorem Zeta23.WeilEF.log_two_add_div_le {x : ℝ} (hx : 0 ≤ x) :
    Real.log (2 + x) / (1 + x ^ 2) ≤ 6 * (1 + x) ^ (-(3 / 2 : ℝ)) := by sorry
