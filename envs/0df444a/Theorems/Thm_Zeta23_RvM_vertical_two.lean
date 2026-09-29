-- Prove2me | Theorems.Thm_Zeta23_RvM_vertical_two
-- name    : Zeta23.RvM.vertical_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:42:25.922179+00:00
-- url     : https://prove2.me/theorems/1cc7958d-a1fe-461c-8365-eba40152aa05
-- title:
--   Vertical side on the 2-line: $\bigl|\operatorname{Im}\int \zeta'/\zeta(2+it)\,i\,dt\bigr| \le \pi$
-- statement:
--   For **all** real $T_1, T_2$ (no ordering or size restriction),
--   $$\Bigl|\operatorname{Im}\int_{T_1}^{T_2} \frac{\zeta'}{\zeta}(2 + it)\cdot i\,dt\Bigr| \;\le\; \pi,$$
--   where $\zeta$ is Mathlib's `riemannZeta` and the factor $i$ realizes $ds = i\,dt$ along the vertical segment.
--
--   The proof idea recorded in the source: $\log\zeta(2+it)$ is a primitive of the integrand along the line, and $|\arg\zeta(2+it)| \le \pi/2$ because $\operatorname{Re}\,\zeta(2+it) > 0$ (the Dirichlet series at $\operatorname{Re} s = 2$ is dominated by its first term), so the imaginary part of the integral is a difference of two arguments each of modulus at most $\pi/2$. A sharper constant $2\log 3$ holds, but an absolute constant suffices downstream.
--
--   This is the vertical-side contribution to the argument-principle count in the Riemann-von Mangoldt argument; it is consumed by `Zeta23.RvM.rvM_main` (as one of the two contour hypotheses of `rvM_main_aux`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/Backlund.lean#L396-L413

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
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
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
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic

open Complex Set MeasureTheory Real intervalIntegral
attribute [-instance] LieAlgebra.ofAssociativeAlgebra

theorem Zeta23.RvM.vertical_two : ∀ T₁ T₂ : ℝ,
    |(∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im| ≤ Real.pi := by sorry
