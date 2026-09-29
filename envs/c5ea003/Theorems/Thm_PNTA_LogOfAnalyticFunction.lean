-- Prove2me | Theorems.Thm_PNTA_LogOfAnalyticFunction
-- name    : PNTA.LogOfAnalyticFunction
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-12T05:44:26.525757+00:00
-- url     : https://prove2.me/theorems/321c32b1-d3e4-4adc-af32-474bda100d09
-- title:
--   Analytic logarithm of a nonvanishing function, with $\mathrm{Re}\, J_B = \log|B|$
-- statement:
--   A nonvanishing analytic function on a disc admits an analytic logarithm, normalised to vanish at the origin.
--
--   Let $0 < r < R$ and let $B$ be analytic on a neighbourhood of the closed disc $\overline{D}(0,R)$ with $B(z) \neq 0$ for every $|z| \le R$. Then there is a function $J_B$, analytic on the open disc $D(0,R)$, such that
--
--   - $J_B(0) = 0$;
--   - $J_B'(z) = B'(z)/B(z)$ for every $z$ in the closed disc of radius $r$; and
--   - $\mathrm{Re}\, J_B(z) = \log|B(z)| - \log|B(0)|$ for every $z$ in $D(0,R)$.
--
--   So $J_B$ is a branch of $\log(B/B(0))$: its derivative is the logarithmic derivative of $B$, and its real part is the normalised log-modulus. The third property is what makes this the bridge to Borel–Carathéodory — an upper bound on $|B|$ becomes an upper bound on $\mathrm{Re}\, J_B$, and the Borel–Carathéodory inequality then controls $J_B'= B'/B$ itself.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/StrongPNT.lean#L249-L309

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

theorem PNTA.LogOfAnalyticFunction {r R : ℝ} {B : ℂ → ℂ}
    (zero_lt_r : 0 < r) (r_lt_R : r < R)
    (BanalyticOnNhdOfDR : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (Bnonzero : ∀ z ∈ Metric.closedBall (0 : ℂ) R, B z ≠ 0) :
    ∃ (J_B : ℂ → ℂ), (AnalyticOnNhd ℂ J_B (Metric.ball 0 R)) ∧
      (J_B 0 = 0) ∧
      (∀ z ∈ Metric.closedBall 0 r, (deriv J_B) z = (deriv B) z / (B z)) ∧
      (∀ z ∈ Metric.ball 0 R, Real.log ‖B z‖ - Real.log ‖B 0‖ = (J_B z).re) := by sorry
