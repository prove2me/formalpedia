-- Prove2me | Theorems.Thm_Zeta23_RvM_halfContour_completedZeta_split
-- name    : Zeta23.RvM.halfContour_completedZeta_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:39:35.374881+00:00
-- url     : https://prove2.me/theorems/0df7ef96-d56d-4c7a-9b8d-872fceebdef8
-- title:
--   Splitting the half-contour of $\Lambda'/\Lambda$ into $\zeta$- and $\Gamma_{\mathbb R}$-parts
-- statement:
--   **Setup.** $\Lambda(s) = \pi^{-s/2}\Gamma(s/2)\,\zeta(s) = \Gamma_{\mathbb R}(s)\,\zeta(s)$ is the completed Riemann zeta function (Mathlib's `completedRiemannZeta`), and $\Gamma_{\mathbb R}(s) = \pi^{-s/2}\Gamma(s/2)$. For a function $F$, `halfContour F T₁ T₂` is the integral of $F$ along the right half-contour $\tfrac12 + iT_1 \to 2 + iT_1 \to 2 + iT_2 \to \tfrac12 + iT_2$ (bottom horizontal, right vertical, minus top horizontal). $T$ is a *good height* (`GoodHeight T`) if no nontrivial zero of $\zeta$ has ordinate $T$.
--
--   **Statement.** For $1 \le T_1 < T_2$ with both $T_1$ and $T_2$ good heights,
--
--   $$\mathrm{halfContour}\Bigl(\frac{\Lambda'}{\Lambda}\Bigr) \;=\; \mathrm{halfContour}\Bigl(\frac{\zeta'}{\zeta}\Bigr) \;+\; \mathrm{halfContour}\Bigl(\frac{\Gamma_{\mathbb R}'}{\Gamma_{\mathbb R}}\Bigr),$$
--
--   all three half-contours taken between heights $T_1$ and $T_2$. The identity $\log$-derivative of a product = sum of $\log$-derivatives is valid pointwise on the contour because good heights keep the horizontal segments away from zeros of $\zeta$, and the integrands are integrable there.
--
--   **Role.** In `Zeta23.RvM.MainTerm` this decomposes the argument-principle contour integral of $\Lambda'/\Lambda$ into the $\Gamma$-side (yielding the smooth main term $\int \mu$, via `gamma_side`) and the $\zeta$-side (the $O(\log T)$ remainder, via Backlund's bound). Consumed by `Zeta23.RvM.rvM_main_param`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/MainTerm.lean#L82-L191

import Batteries.Tactic.Lemma
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_RvM_Defs
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ZetaReflect

open Complex MeasureTheory
attribute [-instance] LieAlgebra.ofAssociativeAlgebra
open Zeta23
open Zeta23.RvM

theorem Zeta23.RvM.halfContour_completedZeta_split {T₁ T₂ : ℝ} (h1 : 1 ≤ T₁) (h12 : T₁ < T₂)
    (hg1 : GoodHeight T₁) (hg2 : GoodHeight T₂) :
    halfContour (logDeriv completedRiemannZeta) T₁ T₂ =
      halfContour (logDeriv riemannZeta) T₁ T₂ + halfContour (logDeriv Complex.Gammaℝ) T₁ T₂ := by sorry
