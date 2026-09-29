-- Prove2me | Theorems.Thm_PNTA_BorelCaratheodoryDeriv
-- name    : PNTA.BorelCaratheodoryDeriv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-12T06:14:27.743098+00:00
-- url     : https://prove2.me/theorems/c0254af3-db27-4ff6-af7a-5214a0962d14
-- title:
--   Borel–Carathéodory derivative bound $|f'(z)| \le \dfrac{16MR^2}{(R-r)^3}$
-- statement:
--   This is the clean, single-radius form of the Borel–Carathéodory derivative estimate.
--
--   Let $R > 0$ and let $f$ be analytic on the open disc $D(0,R)$ with $f(0) = 0$, and suppose $\mathrm{Re}\, f(z) \le M$ for all $|z| < R$, where $M > 0$. Then for every $0 < r < R$ and every $z$ with $|z| \le r$,
--   $$|f'(z)| \;\le\; \frac{16\,M\,R^2}{(R - r)^3}.$$
--
--   A bound on the real part of $f$ alone controls the derivative of $f$ on any strictly smaller disc, with an explicit constant. Applied to $f = \log(\zeta(s)/\zeta(s_0))$ this is exactly what yields bounds on $\zeta'/\zeta$ near the one-line, and hence the classical zero-free region.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/StrongPNT.lean#L193-L210

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

theorem PNTA.BorelCaratheodoryDeriv {M r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (rpos : 0 < r) (hyp_r : r < R)
    (analytic_f : AnalyticOn ℂ f (Metric.ball 0 R))
    (zeroAtZero : f 0 = 0)
    (realPartBounded : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (hyp_z : z ∈ Metric.closedBall 0 r) :
    ‖deriv f z‖ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by sorry
