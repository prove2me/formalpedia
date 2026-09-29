-- Prove2me | Theorems.Thm_DerivUpperBnd_aux7_nonneg
-- name    : DerivUpperBnd_aux7_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:18:04.520212+00:00
-- url     : https://prove2.me/theorems/2900da69-33fd-4768-be1a-85be10078b66
-- title:
--   Nonnegativity of $x^{-\sigma-1}\log x$ for $x > a \geq 1$
-- statement:
--   Let $a, \sigma \in \mathbb{R}$ with $a \geq 1$, where $\sigma$ is an arbitrary real number. Then for every $x \in (a, \infty)$,
--   $$0 \leq x^{-\sigma-1} \log x.$$
--
--   Indeed, for $x > a \geq 1$ the real power $x^{-\sigma-1}$ is strictly positive (regardless of the sign of the exponent) and $\log x \geq 0$, so the product is nonnegative. Note that no sign condition on $\sigma$ is needed.
--
--   This small positivity lemma lets one replace the integrand by its absolute value (and conversely) in the tail integrals appearing in the PNT+ upper bounds for $\zeta'(s)$, so that comparison and monotone-convergence arguments apply cleanly.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1611-L1615

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

-- Alternative cleaner proof using more direct approach

/- The set should be open so that f'(p) = O(1) for all p ∈ U -/

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation (name := riemannzeta0) "ζ₀" => riemannZeta0

theorem DerivUpperBnd_aux7_nonneg {a σ : ℝ} (ha : 1 ≤ a) :
    ∀ x ∈ Ioi a, 0 ≤ x ^ (-σ - 1) * Real.log x := by sorry
