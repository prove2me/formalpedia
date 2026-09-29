-- Prove2me | Theorems.Thm_Zeta23_WeilEF_norm_logDeriv_GammaR_le
-- name    : Zeta23.WeilEF.norm_logDeriv_GammaR_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:52:38.800914+00:00
-- url     : https://prove2.me/theorems/51d7ccdc-ba0b-49a3-a8ab-4668977da16c
-- title:
--   Logarithmic growth of $\Gamma_{\mathbb{R}}'/\Gamma_{\mathbb{R}}$ on the strip $1/2 \le \sigma \le 3/2$
-- statement:
--   Here $\Gamma_{\mathbb{R}}(s) = \pi^{-s/2}\, \Gamma(s/2)$ is the archimedean factor of the completed Riemann zeta function (Mathlib's `Complex.Gammaℝ`).
--
--   **Statement.** There is a constant $C > 0$ such that for all real $\sigma, t$ with $1/2 \le \sigma \le 3/2$,
--   $$\Bigl\| \frac{\Gamma_{\mathbb{R}}'}{\Gamma_{\mathbb{R}}}(\sigma + it) \Bigr\| \le C \, \log(2 + |t|).$$
--   So on the closed strip $1/2 \le \operatorname{Re} s \le 3/2$ the logarithmic derivative of the $\Gamma_{\mathbb{R}}$-factor grows at most logarithmically in the height — the standard Stirling-type estimate, in the exact quantitative form needed on vertical lines.
--
--   **Role.** In the module `Zeta23.WeilEF.VerticalLine` it feeds `gamma_line_shift`, which moves the archimedean term of the explicit formula from the line $\operatorname{Re} s = c$ to the critical line $\operatorname{Re} s = 1/2$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/VerticalLine.lean#L609-L638

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

theorem Zeta23.WeilEF.norm_logDeriv_GammaR_le : ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 2 →
    ‖logDeriv Complex.Gammaℝ (σ + t * I)‖ ≤ C * Real.log (2 + |t|) := by sorry
