-- Prove2me | Theorems.Thm_ZetaInvBound2
-- name    : ZetaInvBound2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:55:07.814156+00:00
-- url     : https://prove2.me/theorems/0b00d5a6-205a-49e6-a1a7-71a0531e1aef
-- title:
--   Mertens-type inverse bound: $1/\|\zeta(\sigma+it)\| \le C (\sigma-1)^{-3/4} (\log|t|)^{1/4}$ for $1 < \sigma \le 2$
-- statement:
--   There exists a constant $C > 0$ such that for every real $\sigma \in (1, 2]$ and every real $t$ with $|t| > 3$,
--   $$\frac{1}{\|\zeta(\sigma + it)\|} \;\le\; C \, (\sigma - 1)^{-3/4} \, (\log |t|)^{1/4}.$$
--
--   This is the classical consequence of the Mertens $3$-$4$-$1$ inequality $\zeta(\sigma)^3 \, |\zeta(\sigma+it)|^4 \, |\zeta(\sigma+2it)| \ge 1$: using $\zeta(\sigma) \ll (\sigma-1)^{-1}$ and $\zeta(\sigma + 2it) \ll \log|t|$, one solves for $|\zeta(\sigma+it)|$ and obtains the displayed bound to the right of the $1$-line. It is the launching point of the zero-free-region argument: combined with the bound $\|\zeta'\| \ll \log^2|t|$, the estimate is propagated across the $1$-line to a region of width $\asymp \log^{-9}|t|$, producing the lower bound $\|\zeta\| \gg \log^{-7}|t|$ used in the Prime Number Theorem contour argument.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L2101-L2182

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

theorem ZetaInvBound2 :
    ∃ C > 0, ∀ {σ : ℝ} (_ : σ ∈ Ioc 1 2) (t : ℝ) (_ : 3 < |t|),
    1 / ‖ζ (σ + t * I)‖ ≤ C * (σ - 1) ^ (-(3 : ℝ) / 4) * (Real.log |t|) ^ ((1 : ℝ) / 4) := by sorry
