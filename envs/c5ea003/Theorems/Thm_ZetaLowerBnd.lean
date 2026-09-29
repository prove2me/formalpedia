-- Prove2me | Theorems.Thm_ZetaLowerBnd
-- name    : ZetaLowerBnd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:58:41.587087+00:00
-- url     : https://prove2.me/theorems/3c71d99f-3ec4-49bb-a345-7e451021915b
-- title:
--   Zero-free-region lower bound: $\|\zeta(\sigma+it)\| \ge c \log^{-7}|t|$ for $\sigma \in [\,1 - A/\log^9|t|,\, 1)$
-- statement:
--   There exist a constant $A \in (0, \tfrac12]$ and a constant $c > 0$ such that for all real $\sigma$ and $t$ with $|t| > 3$ and
--   $$\sigma \in \left[\, 1 - \frac{A}{(\log |t|)^{9}},\; 1 \right),$$
--   the Riemann zeta function satisfies the lower bound
--   $$\frac{c}{(\log |t|)^{7}} \;\le\; \|\zeta(\sigma + it)\|.$$
--
--   This is the quantitative zero-free region for $\zeta$ to the left of the $1$-line, in the classical de la Vallee Poussin style with explicit logarithmic losses: within a strip of width $A/\log^9|t|$, not only does $\zeta$ not vanish, but $|\zeta|$ is at least $c \log^{-7}|t|$. It is derived from the Mertens-inequality lower bound at $\sigma > 1$ together with the mean-value-theorem propagation using $\|\zeta'\| \ll \log^2|t|$. This bound (equivalently its reciprocal form $1/\|\zeta\| \le C\log^7|t|$) is what allows the Perron contour for $\psi(x)$ to be pushed left of the $1$-line, giving the Prime Number Theorem with an explicit error term.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L2341-L2464

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

theorem ZetaLowerBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (c : ℝ) (_ : 0 < c),
    ∀ (σ : ℝ)
    (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ 9) 1),
    c / (Real.log |t|) ^ (7 : ℝ) ≤ ‖ζ (σ + t * I)‖ := by sorry
