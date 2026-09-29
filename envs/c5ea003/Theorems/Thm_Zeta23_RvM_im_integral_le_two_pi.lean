-- Prove2me | Theorems.Thm_Zeta23_RvM_im_integral_le_two_pi
-- name    : Zeta23.RvM.im_integral_le_two_pi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:38:06.331342+00:00
-- url     : https://prove2.me/theorems/44f5c084-40bc-488d-ba46-59cdcf3db48e
-- title:
--   Backlund base case: $\bigl|\mathrm{Im}\int_u^v \zeta'/\zeta(\sigma+iT)\,d\sigma\bigr| \le 2\pi$ when $\mathrm{Re}\,\zeta$ has no zero
-- statement:
--   **Statement.** Let $T \ne 0$ be a real number such that $\zeta(\sigma + iT) \ne 0$ for all $\sigma \in [1/2, 2]$, and let $u < v$ with $[u, v] \subseteq [1/2, 2]$. Suppose $\mathrm{Re}\,\zeta(\sigma + iT) \ne 0$ for every $\sigma$ in the open interval $(u, v)$. Then
--
--   $$\Bigl|\,\mathrm{Im} \int_{u}^{v} \frac{\zeta'}{\zeta}(\sigma + iT)\, d\sigma\,\Bigr| \;\le\; 2\pi.$$
--
--   The imaginary part of $\int \zeta'/\zeta$ along the segment measures the variation of $\arg \zeta$; while $\mathrm{Re}\,\zeta(\sigma + iT)$ keeps a constant sign, the values stay in one open half-plane, so the continuous argument can vary by at most $\pi$ across the interval — comfortably within the stated $2\pi$ once endpoint effects are accounted for.
--
--   **Role.** The base case of Backlund's argument in `Zeta23.RvM.Backlund`: the induction `Zeta23.RvM.im_integral_logDeriv_le_aux` splits $[u, v]$ at the zeros of $\mathrm{Re}\,\zeta(\cdot + iT)$ and applies this bound on each zero-free piece, giving $|\mathrm{Im}\int_{1/2}^2 \zeta'/\zeta| \le 2\pi(\#\text{zeros} + 1)$ and hence the $O(\log T)$ horizontal bound of the Riemann–von Mangoldt formula.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/Backlund.lean#L102-L182

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
variable {T : ℝ}

theorem Zeta23.RvM.im_integral_le_two_pi (hT : T ≠ 0)
    (hnz : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0)
    {u v : ℝ} (hu : 1/2 ≤ u) (huv : u < v) (hv : v ≤ 2)
    (hno : ∀ σ ∈ Set.Ioo u v, (riemannZeta (σ + T * I)).re ≠ 0) :
    |(∫ σ in u..v, logDeriv riemannZeta (σ + T * I)).im| ≤ 2 * Real.pi := by sorry
