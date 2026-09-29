-- Prove2me | Theorems.Thm_Zeta23_RvM_logDeriv_GammaR
-- name    : Zeta23.RvM.logDeriv_GammaR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:39:20.922688+00:00
-- url     : https://prove2.me/theorems/2afed0c9-b0d0-4ad7-933e-0212f56f381e
-- title:
--   Logarithmic derivative of $\Gamma_{\mathbb R}$: $\frac{\Gamma_{\mathbb R}'}{\Gamma_{\mathbb R}}(s) = -\frac{\log \pi}{2} + \frac{1}{2}\psi(s/2)$
-- statement:
--   **Setup.** $\Gamma_{\mathbb R}(s) = \pi^{-s/2}\Gamma(s/2)$ is the archimedean factor (Mathlib's `Complex.Gammaℝ`), and $\psi = \Gamma'/\Gamma$ is the digamma function (Mathlib's `Complex.digamma`).
--
--   **Statement.** For every complex $s$ with $\mathrm{Re}\, s > 0$,
--
--   $$\frac{\Gamma_{\mathbb R}'}{\Gamma_{\mathbb R}}(s) \;=\; -\frac{\log \pi}{2} \;+\; \frac{1}{2}\,\psi\!\Bigl(\frac{s}{2}\Bigr).$$
--
--   This is the chain rule applied to $\log \Gamma_{\mathbb R}(s) = -\tfrac{s}{2}\log\pi + \log\Gamma(s/2)$, valid on the right half-plane where $\Gamma(s/2)$ is analytic and nonvanishing.
--
--   **Role.** In `Zeta23.RvM.GammaSide` this expresses the $\Gamma$-side integrand of the Riemann–von Mangoldt contour in terms of the digamma function; restricted to the critical line it gives $\mathrm{Re}\,(\Gamma_{\mathbb R}'/\Gamma_{\mathbb R})(\tfrac12 + it) = \pi\,\mu(t)$ with $\mu$ the density of [eq:mudef]. Consumed by `Zeta23.RvM.gamma_side`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/GammaSide.lean#L64-L104

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_RvM_Defs
import Definitions.Def_Zeta23_RvM_GammaSide
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ZetaReflect

open Complex MeasureTheory Set
open scoped Interval
open Zeta23
open Zeta23.RvM

theorem Zeta23.RvM.logDeriv_GammaR {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s = -(Real.log Real.pi : ℂ) / 2 + (1/2 : ℂ) * Complex.digamma (s / 2) := by sorry
