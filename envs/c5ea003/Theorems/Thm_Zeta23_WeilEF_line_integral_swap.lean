-- Prove2me | Theorems.Thm_Zeta23_WeilEF_line_integral_swap
-- name    : Zeta23.WeilEF.line_integral_swap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:53:09.259348+00:00
-- url     : https://prove2.me/theorems/5aa55a24-264c-40b5-8846-7576542cd186
-- title:
--   Integral-sum swap for the prime-side Dirichlet series against the Fourier transform
-- statement:
--   Let $k : \mathbb{R} \to \mathbb{C}$ be $C^2$ with compact support and $c > 1$. Write $\widehat{f}(t) = \operatorname{paperFT} f(t) = \int f(u)e^{itu}\,du$ for the paper Fourier transform, $\operatorname{tilt} k\,b\,(u) = k(u)\,e^{bu}$ for the exponentially tilted test function, $\Lambda(n)$ for the von Mangoldt function, and $\operatorname{LSeries.term}(f, s, n)$ for Mathlib's $n$-th $L$-series term $f(n)/n^s$ (equal to $0$ at $n = 0$).
--
--   The theorem swaps the integral over $t \in \mathbb{R}$ with the sum over $n$:
--   $$\int_{\mathbb{R}} \sum_{n=0}^{\infty} \widehat{k_{c-1/2}}(t)\,\frac{\Lambda(n)}{n^{c+it}}\,dt \;=\; \sum_{n=0}^{\infty} \int_{\mathbb{R}} \widehat{k_{c-1/2}}(t)\,\frac{\Lambda(n)}{n^{c+it}}\,dt,$$
--   where $k_{c-1/2} = \operatorname{tilt} k\,(c - 1/2)$ and both sides are `tsum`s over $\mathbb{N}$. The swap is justified by dominated convergence: the terms are dominated by $\|\widehat{k_{c-1/2}}(t)\| \in L^1$ times the convergent series $\sum_n \Lambda(n)\,n^{-c} < \infty$.
--
--   This is Step 3 of the vertical-line computation: it turns the line integral of $H \cdot \zeta'/\zeta$ on $\operatorname{Re} s = c$ into the explicit prime sum, and is consumed by `prime_side_line` in the Weil explicit-formula development.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/VerticalLine.lean#L160-L218

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

theorem Zeta23.WeilEF.line_integral_swap {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) :
    ∫ t : ℝ, (∑' n : ℕ, paperFT (tilt k (c - 1/2)) t
        * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n)
      = ∑' n : ℕ, ∫ t : ℝ, paperFT (tilt k (c - 1/2)) t
        * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n := by sorry
