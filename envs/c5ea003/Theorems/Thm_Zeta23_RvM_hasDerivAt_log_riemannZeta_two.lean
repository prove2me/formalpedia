-- Prove2me | Theorems.Thm_Zeta23_RvM_hasDerivAt_log_riemannZeta_two
-- name    : Zeta23.RvM.hasDerivAt_log_riemannZeta_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:40:36.692156+00:00
-- url     : https://prove2.me/theorems/41d3df9b-62e5-4a3d-9c18-b04dd150f35f
-- title:
--   $t \mapsto \log \zeta(2 + it)$ is a primitive of $t \mapsto i\,\zeta'/\zeta(2 + it)$
-- statement:
--   **Statement.** For every real $t$, the function
--
--   $$t \;\longmapsto\; \log \zeta(2 + it)$$
--
--   (with $\log$ the principal branch, Mathlib's `Complex.log`) is differentiable at $t$ with derivative
--
--   $$\frac{d}{dt} \log \zeta(2 + it) \;=\; \frac{\zeta'}{\zeta}(2 + it)\cdot i.$$
--
--   No hypotheses are needed: on the line $\mathrm{Re}\,s = 2$ one has $\|\zeta(s) - 1\| \le \pi^2/6 - 1 < 1$, so $\zeta(2+it)$ stays in the open right half-plane, where the principal logarithm is analytic; the chain rule then gives the formula.
--
--   **Role.** In `Zeta23.RvM.Backlund` this lets the vertical-segment integral $\int \zeta'/\zeta(2+it)\,i\,dt$ be evaluated by the fundamental theorem of calculus as a difference of logarithms, which is bounded since $\zeta$ is bounded and bounded away from $0$ on $\mathrm{Re}\,s = 2$. Consumed by `Zeta23.RvM.vertical_two`, the $O(1)$ bound on the right vertical side of the Riemann–von Mangoldt contour.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/Backlund.lean#L361-L380

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

theorem Zeta23.RvM.hasDerivAt_log_riemannZeta_two (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.log (riemannZeta (2 + t * I)))
      (logDeriv riemannZeta (2 + t * I) * I) t := by sorry
