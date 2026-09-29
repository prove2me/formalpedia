-- Prove2me | Theorems.Thm_Zeta23_WeilEF_horizontal_vanish
-- name    : Zeta23.WeilEF.horizontal_vanish
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:50:54.13894+00:00
-- url     : https://prove2.me/theorems/9e3c0d46-42db-43dd-8b46-021d782b552f
-- title:
--   The horizontal contour pieces of $H \cdot \Lambda'/\Lambda$ vanish along good heights
-- statement:
--   Setup. Let $k : \mathbb{R} \to \mathbb{C}$ be $C^2$ with compact support, $H = H_k$ the associated test function (`Hfn k`, i.e. $H(s) = \widehat{k}((s-1/2)/i)$), $\Lambda$ the completed zeta function, and $1 < c \le 3/2$. For a function $f$ and reals $x_1, x_2, y$, write $\operatorname{HIntegral}(f, x_1, x_2, y) = \int_{x_1}^{x_2} f(x + iy)\,dx$ for the integral along the horizontal segment at height $y$.
--
--   Assume the good-heights data: constants $C_g > 0$ and heights $R_j \in [j+7, j+8]$ such that on both segments $\operatorname{Im} s = \pm R_j$, $1/2 \le \operatorname{Re} s \le 2$, one has $\zeta(s) \ne 0$ and $\|\zeta'/\zeta(s)\| \le C_g \log^2(j+10)$.
--
--   Assertion. Both sequences of horizontal integrals of $s \mapsto H(s)\,\Lambda'/\Lambda(s)$ across the strip $1-c \le \operatorname{Re} s \le c$ tend to zero:
--   $$\operatorname{HIntegral}\bigl(H \cdot \tfrac{\Lambda'}{\Lambda},\, 1-c,\, c,\, R_j\bigr) \;\longrightarrow\; 0 \quad \text{and} \quad \operatorname{HIntegral}\bigl(H \cdot \tfrac{\Lambda'}{\Lambda},\, 1-c,\, c,\, -R_j\bigr) \;\longrightarrow\; 0 \qquad (j \to \infty).$$
--   The polylogarithmic bound on $\zeta'/\zeta$ and the digamma growth of $\Gamma_{\mathbb{R}}'/\Gamma_{\mathbb{R}}$ are beaten by the $1/R^2$ decay of $H$ on horizontal lines.
--
--   This is the interface lemma that lets `full_line_identity` pass from rectangle contours to the full vertical lines in the Weil explicit-formula argument.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/Horizontal.lean#L26-L167

import Batteries.Tactic.Lemma
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_ExplicitFormula
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_GammaFacts_Series
import Definitions.Def_Zeta23_GammaFacts_StirlingVert
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_WeilEF_VerticalLine

open Zeta23
open WeilEF
open Complex Topology Filter Set MeasureTheory

theorem Zeta23.WeilEF.horizontal_vanish {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3/2) {Cg : ℝ} (hCg : 0 < Cg) {R : ℕ → ℝ}
    (hR : ∀ j : ℕ, (j : ℝ) + 7 ≤ R j ∧ R j ≤ (j : ℝ) + 8 ∧
      ∀ s : ℂ, (s.im = R j ∨ s.im = -R j) → 1/2 ≤ s.re → s.re ≤ 2 →
        riemannZeta s ≠ 0 ∧ ‖logDeriv riemannZeta s‖ ≤ Cg * (Real.log ((j : ℝ) + 10)) ^ 2) :
    Tendsto (fun j : ℕ => HIntegral (fun s => Hfn k s * logDeriv completedRiemannZeta s)
        (1 - c) c (R j)) atTop (𝓝 0)
    ∧ Tendsto (fun j : ℕ => HIntegral (fun s => Hfn k s * logDeriv completedRiemannZeta s)
        (1 - c) c (-(R j))) atTop (𝓝 0) := by sorry
