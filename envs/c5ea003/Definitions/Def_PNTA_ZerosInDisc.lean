-- Prove2me | Definitions.Def_PNTA_ZerosInDisc
-- name    : PNTA_ZerosInDisc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-12T05:57:46.375493+00:00
-- url     : https://prove2.me/theorems/298dcb3d-c910-4c47-ab06-35a5ac17211a
-- title:
--   Zeros in a disc: $\mathcal{Z}_R(f)$, the vanishing cofactor, and the zero-divided-out function
-- statement:
--   These definitions support the Borel–Carathéodory style analysis of the zeros of an analytic function inside a disc.
--
--   For a radius $R > 0$ and $f : \mathbb{C} \to \mathbb{C}$, the **zero set** is
--   $$\mathcal{Z}_R(f) \;=\; \{\, \rho \in \mathbb{C} \;:\; |\rho| \le R \ \text{ and } \ f(\rho) = 0 \,\}.$$
--
--   The **vanishing cofactor** at a point $z$ is the analytic function $h$ obtained by dividing out the vanishing of $f$ at $z$: if $f$ is analytic at $z$ and vanishes there to finite order $m$, so that $f(w) = (w - z)^m h(w)$ near $z$ with $h(z) \neq 0$, the cofactor evaluates that $h$ at $z$ (and is $0$ in the degenerate cases where $f$ is not analytic at $z$ or vanishes identically near it).
--
--   The **zero-divided-out function** removes every zero in the closed disc of radius $r$:
--   $$C_f(z) \;=\; \frac{f(z)}{\prod_{\rho} (z - \rho)^{m_\rho}},$$
--   the product running over the zeros $\rho \in \mathcal{Z}_r(f)$ with $m_\rho$ the order of vanishing of $f$ at $\rho$, with the cofactor supplying the value at each $\rho$ so that $C_f$ extends analytically across the removed zeros. Finally the **Blaschke-type comparison function** rescales $C_f$ against the disc of radius $R$.
--
--   Together these are the standard apparatus for converting a bound on $|f|$ over a disc into a bound on the *number* of zeros of $f$ in a smaller disc — the mechanism behind zero-density estimates for the zeta function.
--
--   **Formalization Note** The order of vanishing is the analytic order at the point, taken as a natural number; the degenerate branches are given junk values so the definitions are total.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/StrongPNT.lean#L338-L546

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

namespace PNTA

def SetOfZeros (R : ℝ) (f : ℂ → ℂ) : Set ℂ := {ρ : ℂ | ‖ρ‖ ≤ R ∧ f ρ = 0}

noncomputable def ZeroFactor (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if h1 : AnalyticAt ℂ f z then
    if h2 : analyticOrderAt f z ≠ ⊤ then
      (h1.analyticOrderAt_ne_top.mp h2).choose z
    else 0
  else 0

noncomputable def Cf (r : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if finite_zeros_mono : (SetOfZeros r f).Finite then
    if _ : z ∈ SetOfZeros r f then
      ZeroFactor f z / ∏ ρ ∈ (finite_zeros_mono.toFinset \ {z}), (z - ρ) ^ (analyticOrderNatAt f ρ)
    else
      f z / ∏ ρ ∈ (finite_zeros_mono.toFinset), (z - ρ) ^ (analyticOrderNatAt f ρ)
  else 1

noncomputable def BlaschkeB (r R : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if finite_zeros_mono : (SetOfZeros r f).Finite then
    (Cf r f) z * (∏ ρ ∈ finite_zeros_mono.toFinset, (R - z * (conj ρ) / R) ^ (analyticOrderNatAt f ρ))
  else 1

end PNTA


