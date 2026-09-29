-- Prove2me | Theorems.Thm_Zeta23_WeilEF_full_line_identity
-- name    : Zeta23.WeilEF.full_line_identity
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:52:14.867382+00:00
-- url     : https://prove2.me/theorems/f936c46a-7213-4407-922d-2cd931999b4f
-- title:
--   Full-line identity: the two-sided vertical integral of $H \cdot \Lambda'/\Lambda$ equals the zero sum minus $H(0) + H(1)$
-- statement:
--   Setup. Let $k : \mathbb{R} \to \mathbb{C}$ be a $C^2$ function with compact support, and let $H = H_k$ be the associated test function $H(s) = \widehat{k}\bigl((s - 1/2)/i\bigr)$ (the project's `Hfn k`, built from the paper Fourier transform $\widehat{k}(z) = \int k(u)e^{izu}du$). Let $\Lambda$ be the completed zeta function, $\operatorname{logDeriv}\Lambda = \Lambda'/\Lambda$, and fix $c$ with $1 < c \le 3/2$. The hypothesis `ZetaSeam` packages classical facts about the nontrivial zeros of $\zeta$ (multiplicities $\ge 1$, reflection symmetry $\rho \mapsto 1 - \overline{\rho}$, local finiteness), and `zetaZeros hs` is the resulting zero configuration: its carrier is exactly the set of nontrivial zeros $\{\rho : \zeta(\rho) = 0,\ 0 < \operatorname{Re}\rho < 1\}$ and its multiplicity function is the analytic order $m_\rho$ of $\zeta$ at $\rho$.
--
--   Assertion.
--   $$\frac{1}{2\pi}\int_{\mathbb{R}} \bigl[H(c + it) + H(1 - c - it)\bigr]\,\frac{\Lambda'}{\Lambda}(c + it)\,dt \;=\; \sum_{\rho} m_\rho\, H(\rho) \;-\; H(0) \;-\; H(1),$$
--   where the sum on the right runs over the nontrivial zeros $\rho$ of $\zeta$ weighted by multiplicity $m_\rho$, formalized as an (absolutely convergent) `tsum` over the carrier of `zetaZeros hs`.
--
--   Role. This is the $R \to \infty$ limit of the rectangle contour identity: the rectangle $1-c \le \operatorname{Re} s \le c$, $|\operatorname{Im} s| \le R$ is sent to the full strip along a sequence of good heights (`good_heights`), the horizontal pieces vanishing by `horizontal_vanish` together with the digamma growth bound and the $1/R^2$ decay of $H$. Its terms $-H(0) - H(1)$ record the pole of $\Lambda$ at $s = 0$ and $s = 1$. It is the direct input to `EF_lit_zeta`, the literal Weil explicit formula of the project.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/FullLineAssembly.lean#L35-L89

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
import Definitions.Def_Zeta23_GammaFacts_Series
import Definitions.Def_Zeta23_GammaFacts_StirlingVert
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_WeilEF_VerticalLine

open Zeta23
open WeilEF
open Complex Topology Filter Set MeasureTheory

theorem Zeta23.WeilEF.full_line_identity (hs : ZetaSeam) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3/2) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (Hfn k ((c:ℂ) + t * I) + Hfn k (1 - c - t * I))
        * logDeriv completedRiemannZeta ((c:ℂ) + t * I)
      = (∑' ρ : (zetaZeros hs).carrier, ((zetaZeros hs).mult ρ : ℂ) * Hfn k ρ)
        - Hfn k 0 - Hfn k 1 := by sorry
