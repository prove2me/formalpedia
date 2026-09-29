-- Prove2me | Theorems.Thm_Zeta23_WeilEF_norm_paperFT_le_uniform
-- name    : Zeta23.WeilEF.norm_paperFT_le_uniform
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:52:45.213809+00:00
-- url     : https://prove2.me/theorems/1e6aefed-4586-4a61-b55a-e02b1641354e
-- title:
--   Uniform decay of the transform $h_k$ near the real axis
-- statement:
--   For $k : \mathbb{R} \to \mathbb{C}$, write $h_k(z) := \int_{\mathbb{R}} k(u)\, e^{izu}\, du$ (the paper's transform, `paperFT` in Lean). Assume $k$ is twice continuously differentiable and integrable, and that its support is contained in $[-\Lambda, \Lambda]$ for some $\Lambda \ge 0$ (formally: $k(u) \ne 0$ implies $|u| \le \Lambda$).
--
--   **Statement.** For every complex $z$ with $|\operatorname{Im} z| \le 1$,
--   $$\| h_k(z) \| \le \frac{2\, e^{\Lambda} \bigl( \|k\|_1 + \|k''\|_1 \bigr)}{1 + (\operatorname{Re} z)^2},$$
--   where $\|k\|_1 = \int \|k(u)\|\, du$ and $\|k''\|_1 = \int \|k''(u)\|\, du$ are the $L^1$ norms of $k$ and of its second derivative (written in Lean as integrals of the pointwise norms, with $k'' = $ `deriv (deriv k)`).
--
--   **Role.** In the module `Zeta23.WeilEF.VerticalLine` this uniform quadratic decay on the unit horizontal strip is the majorant needed by `gamma_line_shift` to move the archimedean integral of the explicit formula between vertical lines by dominated convergence.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/VerticalLine.lean#L577-L607

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

theorem Zeta23.WeilEF.norm_paperFT_le_uniform {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hki : Integrable k) {Lam : ℝ}
    (hLam : 0 ≤ Lam) (hsupp : ∀ u, k u ≠ 0 → |u| ≤ Lam) {z : ℂ} (hz : |z.im| ≤ 1) :
    ‖paperFT k z‖ ≤ 2 * Real.exp Lam * ((∫ u, ‖k u‖) + ∫ u, ‖deriv (deriv k) u‖) / (1 + z.re ^ 2) := by sorry
