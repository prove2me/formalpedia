-- Prove2me | Theorems.Thm_PNTA_ZeroFactorization_local
-- name    : PNTA.ZeroFactorization_local
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-12T06:02:38.385382+00:00
-- url     : https://prove2.me/theorems/d141fb7d-5914-47cf-82a2-ab2e1f3eb12c
-- title:
--   Local factorization $f(z) = (z-\rho)^{m_\rho} h_\rho(z)$ at a zero
-- statement:
--   Every zero of an analytic function factors out with an analytic, nonvanishing cofactor.
--
--   Let $f$ be analytic on a neighbourhood of the closed unit disc with $f(0) \neq 0$, let $R < 1$, and let $\rho$ be a zero of $f$ with $|\rho| \le R$. Then there is a function $h_\rho$, analytic at $\rho$, with $h_\rho(\rho) \neq 0$, such that in a neighbourhood of $\rho$
--   $$f(z) \;=\; (z - \rho)^{m_\rho}\, h_\rho(z),$$
--   where $m_\rho$ is the order of vanishing of $f$ at $\rho$; moreover $h_\rho(\rho)$ is exactly the value returned by the vanishing-cofactor construction.
--
--   The hypothesis $f(0) \neq 0$ rules out the degenerate case of $f$ vanishing identically, which guarantees the order $m_\rho$ is finite. This local factorization is the step that lets the zeros be divided out one at a time to form the zero-free function whose modulus is then estimated.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/StrongPNT.lean#L402-L430

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

theorem PNTA.ZeroFactorization_local {R : ℝ} {f : ℂ → ℂ} {ρ : ℂ}
    (RleOne : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0)
    (hρ : ρ ∈ SetOfZeros R f) :
    ∃ h_ρ : ℂ → ℂ, AnalyticAt ℂ h_ρ ρ ∧ h_ρ ρ ≠ 0 ∧ ZeroFactor f ρ = h_ρ ρ ∧
      f =ᶠ[nhds ρ] fun z ↦ (z - ρ) ^ analyticOrderNatAt f ρ * h_ρ z := by sorry
