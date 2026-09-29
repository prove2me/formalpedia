-- Prove2me | Theorems.Thm_ZetaNear1BndExact
-- name    : ZetaNear1BndExact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:54:17.811379+00:00
-- url     : https://prove2.me/theorems/da193fd1-f550-4bc2-a622-9dd983d60224
-- title:
--   Pole bound on the real axis: $\|\zeta(\sigma)\| \le c/(\sigma-1)$ for $\sigma \in (1,2]$
-- statement:
--   There exists a constant $c > 0$ such that for every real $\sigma \in (1, 2]$,
--   $$\|\zeta(\sigma)\| \;\le\; \frac{c}{\sigma - 1}.$$
--
--   This quantifies, uniformly on the interval $(1, 2]$, the blow-up of the Riemann zeta function at its simple pole $s = 1$: $\zeta(\sigma) = \tfrac{1}{\sigma-1} + O(1)$ as $\sigma \to 1^+$, so a single constant $c$ controls $\zeta(\sigma)(\sigma-1)$ on the whole interval. In the zero-free-region argument this bound feeds the Mertens $3$-$4$-$1$ inequality, where the factor $\zeta(\sigma)^3 \le c^3 (\sigma-1)^{-3}$ is traded against $|\zeta(\sigma+it)|^4$ to produce the lower bound $|\zeta(\sigma+it)| \gg (\sigma-1)^{3/4} (\log|t|)^{-1/4}$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1879-L1923

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

theorem ZetaNear1BndExact :
    ∃ (c : ℝ) (_ : 0 < c), ∀ (σ : ℝ) (_ : σ ∈ Ioc 1 2), ‖ζ σ‖ ≤ c / (σ - 1) := by sorry
