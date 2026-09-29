-- Prove2me | Theorems.Thm_ZetaNear1BndFilter
-- name    : ZetaNear1BndFilter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:53:52.532341+00:00
-- url     : https://prove2.me/theorems/0d076460-a149-4ef3-8c48-35df6cf17c28
-- title:
--   Asymptotic pole bound: $\zeta(\sigma) = O\bigl(1/(\sigma-1)\bigr)$ as $\sigma \to 1^{+}$
-- statement:
--   As $\sigma$ tends to $1$ from the right along the real axis, the Riemann zeta function satisfies the big-O estimate
--   $$\zeta(\sigma) \;=\; O\!\left( \frac{1}{\sigma - 1} \right) \qquad (\sigma \to 1^{+}),$$
--   formally: the function $\sigma \mapsto \zeta(\sigma)$ is big-O of $\sigma \mapsto 1/(\sigma - 1)$ with respect to the punctured right-neighborhood filter $\mathcal{N}_{>}(1)$ on $\mathbb{R}$.
--
--   This is the filter-language (asymptotic) form of the statement that $\zeta$ has a simple pole of residue $1$ at $s = 1$; it records only the upper bound $|\zeta(\sigma)| \lesssim (\sigma-1)^{-1}$ near the pole. It is the local input from which the uniform interval version $\|\zeta(\sigma)\| \le c/(\sigma-1)$ on $(1,2]$ is deduced (by compactness away from the pole), which in turn enters the Mertens-inequality lower bounds for $\zeta$ near the $1$-line.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1872-L1877

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

theorem ZetaNear1BndFilter :
    (fun σ : ℝ ↦ ζ σ) =O[𝓝[>](1 : ℝ)] (fun σ ↦ (1 : ℂ) / (σ - 1)) := by sorry
