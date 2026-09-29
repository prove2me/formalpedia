-- Prove2me | Theorems.Thm_x_eps_to_inf
-- name    : x_eps_to_inf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:46:02.555363+00:00
-- url     : https://prove2.me/theorems/68d71fa7-b1ed-4e8b-99a7-b9f16042523a
-- title:
--   $x \exp(-c(\log x)^{B}) \to \infty$ for any exponent $B < 1$
-- statement:
--   Let $c \in \mathbb{R}$ be an arbitrary constant and let $B$ be a real exponent with $B < 1$. Then
--
--   $$x \cdot \exp\!\big( -c\, (\log x)^{B} \big) \;\longrightarrow\; \infty \qquad \text{as } x \to \infty.$$
--
--   The point is that when $B < 1$, the correction factor $\exp(-c(\log x)^B) = \exp$ of a quantity that is $o(\log x)$, so it is subpolynomial: it cannot overcome even a single power of $x$, and the product still tends to infinity. No sign restriction on $c$ is needed.
--
--   This asymptotic is tailored to the de la Vallée Poussin error term of the Prime Number Theorem: the PNT+ medium-strength result gives $\psi(x) = x + O\big(x \exp(-c(\log x)^{B})\big)$ with some $B \in (0,1)$, and this lemma certifies that the main term $x$ genuinely dominates the error --- for instance when converting the asymptotic for $\psi$ into statements such as $\psi(x) \to \infty$ or into the asymptotics for $\pi(x)$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MediumPNT.lean#L3083-L3140

import Mathlib.Algebra.Group.Support
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Chebyshev
import Batteries.Tactic.Lemma
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_EulerMaclaurin_defs
import Definitions.Def_Fourier_defs
import Definitions.Def_MediumPNT_defs
import Definitions.Def_MellinCalculus_defs
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_ZetaBounds_defs

set_option lang.lemmaCmd true

open Set Function Filter Complex Real

open ArithmeticFunction (vonMangoldt)
open scoped Chebyshev

local notation (name := mellintransform2) "𝓜" => mellin

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

open Chebyshev

open ComplexConjugate

open MeasureTheory

-- TODO: add to mathlib
attribute [fun_prop] Continuous.const_cpow

--open scoped ArithmeticFunction in

-- TODO : Move elsewhere (should be in Mathlib!) NOT NEEDED

open Filter Topology

theorem x_eps_to_inf (c : ℝ) {B : ℝ} (B_le : B < 1) : Tendsto
    (fun x ↦ x * Real.exp (-c * (Real.log x) ^ B)) atTop atTop := by sorry
