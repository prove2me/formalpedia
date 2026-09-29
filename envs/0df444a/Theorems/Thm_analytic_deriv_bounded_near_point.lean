-- Prove2me | Theorems.Thm_analytic_deriv_bounded_near_point
-- name    : analytic_deriv_bounded_near_point
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:40:54.957335+00:00
-- url     : https://prove2.me/theorems/e88af29e-725e-4d37-b71f-55723ba90b49
-- title:
--   The derivative of a holomorphic function is bounded near any interior point: $f' = O(1)$ on a punctured neighbourhood
-- statement:
--   Let $f : \mathbb{C} \to \mathbb{C}$, let $U \subseteq \mathbb{C}$ be an open set, let $p \in U$, and suppose $f$ is holomorphic on $U$. Then the derivative of $f$ is bounded near $p$; in Landau notation, along the punctured neighbourhood filter at $p$,
--
--   $$f'(z) \;=\; O(1) \qquad (z \to p,\ z \neq p).$$
--
--   Since holomorphic functions are analytic, $f'$ is itself holomorphic — in particular continuous — on $U$, so it is bounded on a small ball around $p$; the lemma packages this as a big-$O$ statement with respect to the punctured-neighbourhood filter $\mathcal{N}[\neq]\,p$, the form in which such local boundedness is consumed by Mathlib's asymptotic calculus.
--
--   In the PNT+ zeta-bounds development this is used when isolating the pole of $\zeta$ at $s=1$: after subtracting the principal part $A/(s-p)$, the remaining holomorphic piece has locally bounded derivative, which controls error terms in the pole-removal arguments. The statement is fully generic and reusable for any holomorphic function on an open set.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L175-L188

import Batteries.Tactic.Lemma
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_EulerMaclaurin_defs
import Definitions.Def_Fourier_defs
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_ZetaBounds_defs

set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta

-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/

theorem analytic_deriv_bounded_near_point
    (f : ℂ → ℂ) {U : Set ℂ} {p : ℂ} (hU : IsOpen U) (hp : p ∈ U) (hf : HolomorphicOn f U) :
    (deriv f) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by sorry
