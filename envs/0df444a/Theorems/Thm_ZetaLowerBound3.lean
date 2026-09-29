-- Prove2me | Theorems.Thm_ZetaLowerBound3
-- name    : ZetaLowerBound3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:58:16.611845+00:00
-- url     : https://prove2.me/theorems/2f03edff-9cc1-4502-a829-6d454618e88e
-- title:
--   Mertens-type lower bound $\|\zeta(\sigma+it)\| \ge c (\sigma-1)^{3/4} (\log|t|)^{-1/4}$ for $1 < \sigma \le 2$
-- statement:
--   There exists a constant $c > 0$ such that for every real $\sigma \in (1, 2]$ and every real $t$ with $|t| > 3$,
--   $$c \, \frac{(\sigma - 1)^{3/4}}{(\log |t|)^{1/4}} \;\le\; \|\zeta(\sigma + it)\|.$$
--
--   This is the lower-bound form of the classical $3$-$4$-$1$ (Mertens inequality) estimate to the right of the $1$-line: from $\zeta(\sigma)^3 |\zeta(\sigma+it)|^4 |\zeta(\sigma+2it)| \ge 1$, together with $\zeta(\sigma) \ll (\sigma-1)^{-1}$ and the upper bound $|\zeta(\sigma+2it)| \ll \log|t|$, one extracts the displayed lower bound on $|\zeta(\sigma+it)|$. It is the seed estimate from which the full zero-free region $\sigma \ge 1 - A/\log^9|t|$ with lower bound $\gg \log^{-7}|t|$ is grown by a mean-value/propagation argument using the $\zeta'$ upper bound.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1984-L2065

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

theorem ZetaLowerBound3 :
    ∃ c > 0, ∀ {σ : ℝ} (_ : σ ∈ Ioc 1 2) (t : ℝ) (_ : 3 < |t|),
    c * (σ - 1) ^ ((3 : ℝ) / 4) / (Real.log |t|) ^ ((1 : ℝ) / 4) ≤ ‖ζ (σ + t * I)‖ := by sorry
