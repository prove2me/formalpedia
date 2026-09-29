-- Prove2me | Theorems.Thm_PNTA_CfAnalytic
-- name    : PNTA.CfAnalytic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-12T06:10:33.658533+00:00
-- url     : https://prove2.me/theorems/914d8293-0dbc-40c6-803b-7df7c58479d6
-- title:
--   The zero-divided-out function $C_f$ is analytic on the disc
-- statement:
--   Dividing out the zeros of an analytic function leaves an analytic function.
--
--   Let $f$ be analytic on a neighbourhood of the closed unit disc with $f(0) \neq 0$, and let $r < R < 1$. Let
--   $$C_f(z) \;=\; \frac{f(z)}{\prod_{\rho} (z - \rho)^{m_\rho}}$$
--   where the product runs over the zeros $\rho$ of $f$ in the closed disc of radius $r$, each with its multiplicity $m_\rho$. Then $C_f$ is analytic on a neighbourhood of the closed disc $\overline{D}(0,R)$.
--
--   At each removed zero the numerator and denominator vanish to exactly the same order, so the apparent singularity is removable and $C_f$ extends analytically across it; away from the zeros both factors are analytic and the denominator is nonzero. Having produced a *nonvanishing* analytic function on the disc, one can take its analytic logarithm and feed the result to Borel–Carathéodory — this is the pivot of the zero-counting argument.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/StrongPNT.lean#L479-L531

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
import Definitions.Def_PNTA_ZerosInDisc

open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory
open Classical

theorem PNTA.CfAnalytic {r R : ℝ} {f : ℂ → ℂ}
    (r_lt_R : r < R) (R_lt_one : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    AnalyticOnNhd ℂ (Cf r f) (Metric.closedBall (0 : ℂ) R) := by sorry
