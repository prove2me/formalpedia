-- Prove2me | Theorems.Thm_ZetaDerivUpperBnd
-- name    : ZetaDerivUpperBnd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:51:43.55669+00:00
-- url     : https://prove2.me/theorems/48d87e76-f647-4323-ab89-875a281f0b4c
-- title:
--   Upper bound $\|\zeta'(\sigma + it)\| \le C \log^2 |t|$ in the region $\sigma \ge 1 - A/\log|t|$
-- statement:
--   There exist a constant $A \in (0, \tfrac12]$ and a constant $C > 0$ such that for all real $\sigma$ and $t$ with $|t| > 3$ and
--   $$\sigma \in \left[ 1 - \frac{A}{\log |t|},\; 2 \right],$$
--   the derivative of the Riemann zeta function satisfies
--   $$\bigl\| \zeta'(\sigma + it) \bigr\| \le C \, (\log |t|)^{2}.$$
--
--   This is the classical upper bound for $\zeta'$ just to the left of the $1$-line (see e.g. Titchmarsh, Theory of the Riemann Zeta-Function, Chapter 3). Together with the companion bounds $|\zeta(\sigma+it)| \ll \log|t|$ and the lower bound $|\zeta(\sigma+it)| \gg \log^{-7}|t|$ in the zero-free region, it controls the logarithmic derivative $\zeta'/\zeta$ on the contours used in the Perron/Mellin contour-shifting argument, which is how the Prime Number Theorem with a quantitative error term is extracted.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1804-L1826

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

theorem ZetaDerivUpperBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Icc (1 - A / Real.log |t|) 2),
    ‖ζ' (σ + t * I)‖ ≤ C * Real.log |t| ^ 2 := by sorry
