-- Prove2me | Theorems.Thm_Zeta23_WeilEF_digamma_growth_strip
-- name    : Zeta23.WeilEF.digamma_growth_strip
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:50:20.337074+00:00
-- url     : https://prove2.me/theorems/26517efa-22e1-472f-b1fa-da07585f12b3
-- title:
--   Logarithmic growth of the digamma function on the strip $1/4 \le \operatorname{Re} s \le 1$
-- statement:
--   Let $\psi$ denote the complex digamma function $\Gamma'/\Gamma$ (Mathlib's `Complex.digamma`).
--
--   There exists a constant $C > 0$ such that for every $s \in \mathbb{C}$ with $1/4 \le \operatorname{Re} s \le 1$,
--   $$\|\psi(s)\| \;\le\; C\,\log\bigl(2 + |\operatorname{Im} s|\bigr).$$
--   This is a coarse growth estimate on a fixed vertical strip in the right half-plane; any polynomial-in-$\log$ bound of this shape suffices for its applications, and it is dischargeable via a Stirling-type estimate.
--
--   In the project this bound controls the Archimedean factor $\Gamma_{\mathbb{R}}'/\Gamma_{\mathbb{R}}$ along vertical lines and horizontal segments: it is consumed by `horizontal_vanish` (the horizontal contour pieces vanish as the height grows), by the integrability lemma `integrable_mul_logDeriv_GammaR_of_decay`, and by the pointwise bound `norm_logDeriv_GammaR_le`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/VerticalLine.lean#L242-L411

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

theorem Zeta23.WeilEF.digamma_growth_strip : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1/4 ≤ s.re → s.re ≤ 1 →
    ‖Complex.digamma s‖ ≤ C * Real.log (2 + |s.im|) := by sorry
