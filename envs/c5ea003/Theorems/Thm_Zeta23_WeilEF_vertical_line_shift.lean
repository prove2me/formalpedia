-- Prove2me | Theorems.Thm_Zeta23_WeilEF_vertical_line_shift
-- name    : Zeta23.WeilEF.vertical_line_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:52:50.646515+00:00
-- url     : https://prove2.me/theorems/0d9cd723-28c9-4700-8996-e75fc9226aae
-- title:
--   Contour shift between vertical lines under a uniform integrable majorant
-- statement:
--   Let $a \le b$ be real, and let $f : \mathbb{C} \to \mathbb{C}$ be holomorphic on the closed strip $a \le \operatorname{Re} s \le b$ (differentiable at every point of the strip). Suppose there is an integrable function $\varphi : \mathbb{R} \to \mathbb{R}$ with
--   $$\| f(\sigma + it) \| \le \varphi(t) \qquad \text{for all } \sigma \in [a, b],\ t \in \mathbb{R},$$
--   and $\varphi(t) \to 0$ as $t \to +\infty$ and as $t \to -\infty$.
--
--   **Statement.**
--   $$\int_{\mathbb{R}} f(b + it)\, dt \;=\; \int_{\mathbb{R}} f(a + it)\, dt.$$
--   The proof runs Cauchy's theorem on rectangles $[a, b] \times [-R, R]$ (via the `RectangleIntegral` machinery, `HolomorphicOn.vanishesOnRectangle`): the horizontal sides vanish as $R \to \infty$ because $\varphi \to 0$, and the vertical integrals converge by domination.
--
--   **Role.** In the module `Zeta23.WeilEF.VerticalLine` this general shift lemma is applied in `gamma_line_shift` to move the archimedean term of the explicit formula from the line $\operatorname{Re} s = c$ to the critical line.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/VerticalLine.lean#L424-L492

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

theorem Zeta23.WeilEF.vertical_line_shift {f : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → DifferentiableAt ℂ f s)
    {φ : ℝ → ℝ} (hφ : Integrable φ)
    (hbound : ∀ (σ t : ℝ), a ≤ σ → σ ≤ b → ‖f (σ + t * I)‖ ≤ φ t)
    (hφtop : Filter.Tendsto φ Filter.atTop (nhds 0))
    (hφbot : Filter.Tendsto φ Filter.atBot (nhds 0)) :
    ∫ t : ℝ, f (b + t * I) = ∫ t : ℝ, f (a + t * I) := by sorry
