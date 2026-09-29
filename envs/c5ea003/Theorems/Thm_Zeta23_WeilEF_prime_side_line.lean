-- Prove2me | Theorems.Thm_Zeta23_WeilEF_prime_side_line
-- name    : Zeta23.WeilEF.prime_side_line
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:53:27.907927+00:00
-- url     : https://prove2.me/theorems/553c70a5-6bdc-4702-8dd2-429d82264f9c
-- title:
--   Prime side of the explicit formula on the line $\operatorname{Re} s = c > 1$
-- statement:
--   Let $k : \mathbb{R} \to \mathbb{C}$ be twice continuously differentiable with compact support, and let $c > 1$. Let $H(s) = \int k(u)\, e^{(s-1/2)u}\, du$ be the analytic weight attached to $k$ (`Hfn k`), and $\Lambda$ the von Mangoldt function.
--
--   **Statement.**
--   $$\frac{1}{2\pi} \int_{\mathbb{R}} H(c + it) \, \Bigl( -\frac{\zeta'}{\zeta}(c + it) \Bigr)\, dt \;=\; \sum_{n \ge 1} \frac{\Lambda(n)}{\sqrt{n}}\; k(\log n),$$
--   the right-hand side being a `tsum` over $\mathbb{N}$ (the $n = 0$ term vanishes since $\Lambda(0)=0$). To the right of the 1-line the Dirichlet series $-\zeta'/\zeta = \sum_n \Lambda(n) n^{-s}$ converges absolutely, so the line integral may be computed term by term via the per-$n$ evaluation (`per_n_line_integral`), each term contributing $\Lambda(n) n^{-1/2} k(\log n)$.
--
--   **Role.** This identifies the prime side of the Weil explicit formula before the contour is moved: it is consumed by `EF_lit_zeta` in `Zeta23.WeilEF`, the literature-form explicit formula from which the paper-form hypothesis H-EF is derived.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/VerticalLine.lean#L220-L240

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

theorem Zeta23.WeilEF.prime_side_line {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Hfn k (c + t * I) * (-logDeriv riemannZeta (c + t * I))
      = ∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) := by sorry
