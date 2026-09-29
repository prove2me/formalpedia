-- Prove2me | Theorems.Thm_ZetaInvBnd
-- name    : ZetaInvBnd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:57:00.924563+00:00
-- url     : https://prove2.me/theorems/2e603ba6-9b8e-481b-b953-a8bfdbf8abbb
-- title:
--   Inverse zeta bound $1/\|\zeta(\sigma+it)\| \le C \log^7 |t|$ in a $\log^{-9}$-neighborhood of the $1$-line
-- statement:
--   There exist a constant $A \in (0, \tfrac12]$ and a constant $C > 0$ such that for all real $\sigma$ and $t$ with $|t| > 3$ and
--   $$\sigma \in \left[\, 1 - \frac{A}{(\log |t|)^{9}},\; 1 + \frac{A}{(\log |t|)^{9}} \,\right),$$
--   the reciprocal of the Riemann zeta function satisfies
--   $$\frac{1}{\|\zeta(\sigma + it)\|} \le C \, (\log |t|)^{7}.$$
--
--   This quantitative non-vanishing statement is the analytic heart of the zero-free region used in this development: within a window of width $A/\log^9|t|$ around the $1$-line, $|\zeta|$ is bounded below by $\log^{-7}|t|$. It combines the $3$-$4$-$1$ (Mertens-inequality) lower bound to the right of the $1$-line with the $\zeta'$ upper bound $\ll \log^2|t|$ to propagate the lower bound slightly to the left. It directly controls $1/\zeta$, and hence $\zeta'/\zeta$, on the pulled-in contours of the Perron argument for the Prime Number Theorem with error term.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L2259-L2335

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

theorem ZetaInvBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ 9) (1 + A / (Real.log |t|) ^ 9)),
    1 / ‖ζ (σ + t * I)‖ ≤ C * (Real.log |t|) ^ (7 : ℝ) := by sorry
