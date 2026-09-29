-- Prove2me | Theorems.Thm_Zeta_eq_int_derivZeta
-- name    : Zeta_eq_int_derivZeta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:56:11.482473+00:00
-- url     : https://prove2.me/theorems/cce07845-ce49-4f07-acf5-206ae62174f7
-- title:
--   Fundamental theorem of calculus for $\zeta$ along a horizontal segment: $\int_{\sigma_1}^{\sigma_2} \zeta'(\sigma + it)\,d\sigma = \zeta(\sigma_2 + it) - \zeta(\sigma_1 + it)$
-- statement:
--   Let $\sigma_1, \sigma_2, t$ be real numbers with $t \neq 0$. Then integrating the derivative of the Riemann zeta function along the horizontal segment from $\sigma_1 + it$ to $\sigma_2 + it$ recovers the difference of the endpoint values:
--
--   $$\int_{\sigma_1}^{\sigma_2} \zeta'(\sigma + i t)\, d\sigma \;=\; \zeta(\sigma_2 + i t) \;-\; \zeta(\sigma_1 + i t).$$
--
--   The hypothesis $t \neq 0$ keeps the segment away from the pole of $\zeta$ at $s = 1$ (and from the real axis), so $\zeta$ is holomorphic on a neighbourhood of the whole segment and the one-variable fundamental theorem of calculus applies to $\sigma \mapsto \zeta(\sigma + it)$.
--
--   This identity is the bridge between bounds on $\zeta'$ and difference bounds on $\zeta$: combined with the estimate $\|\zeta'(\sigma+it)\| \ll (\log|t|)^2$ in the standard zero-free region, it yields the Lipschitz bound $\|\zeta(\sigma_2+it) - \zeta(\sigma_1+it)\| \ll (\log|t|)^2(\sigma_2 - \sigma_1)$ used in the PNT+ lower-bound and contour-shifting arguments.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L2194-L2217

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
set_option backward.isDefEq.respectTransparency false

theorem Zeta_eq_int_derivZeta {σ₁ σ₂ t : ℝ} (t_ne_zero : t ≠ 0) :
    (∫ σ in σ₁..σ₂, ζ' (σ + t * I)) = ζ (σ₂ + t * I) - ζ (σ₁ + t * I) := by sorry
