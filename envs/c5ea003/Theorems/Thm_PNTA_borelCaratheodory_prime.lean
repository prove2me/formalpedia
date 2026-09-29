-- Prove2me | Theorems.Thm_PNTA_borelCaratheodory_prime
-- name    : PNTA.borelCaratheodory_prime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-12T06:05:15.023366+00:00
-- url     : https://prove2.me/theorems/61522628-3cb4-4532-b0c1-d4e23f6d0be0
-- title:
--   Borel–Carathéodory: $|f(z)| \le \dfrac{2Mr}{R-r}$ from a bound on $\mathrm{Re}\, f$
-- statement:
--   The Borel–Carathéodory inequality bounds the modulus of an analytic function in terms of a bound on its real part alone.
--
--   Let $R > 0$ and let $f$ be analytic on the open disc $D(0,R)$ with $f(0) = 0$, and suppose the real part is bounded above by $M > 0$ on that disc, i.e. $\mathrm{Re}\, f(z) \le M$ for all $|z| < R$. Then for every radius $r < R$ and every $z$ with $|z| \le r$,
--   $$|f(z)| \;\le\; \frac{2Mr}{R - r}.$$
--
--   The point is that a one-sided bound on the *real part* — much weaker information than a bound on the modulus — already controls the full modulus on any strictly smaller disc, at the cost of a factor blowing up as $r \to R$. This is the workhorse behind zero-free-region arguments, where $\log$ of an analytic function has a controlled real part (namely $\log$ of a modulus) but no a priori bound on its imaginary part.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/StrongPNT.lean#L71-L93

/-
Extracted from PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
commit f55e85551ac10e96d98262a354cfcaac2825f2da, Apache 2.0 license.
Wrapped in namespace PNTA for the Prove2Me platform.
-/

import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Algebra.Group.Support
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory
open Classical

theorem PNTA.borelCaratheodory_prime {M r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (Rpos : 0 < R) (hyp_r : r < R)
    (analytic : AnalyticOn ℂ f (Metric.ball 0 R))
    (zeroAtZero : f 0 = 0)
    (realPartBounded : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (hyp_z : z ∈ Metric.closedBall 0 r) :
    ‖f z‖ ≤ (2 * M * r) / (R - r) := by sorry
