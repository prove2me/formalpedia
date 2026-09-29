-- Prove2me | Theorems.Thm_DerivZeta0EqDerivZeta
-- name    : DerivZeta0EqDerivZeta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:31:58.217508+00:00
-- url     : https://prove2.me/theorems/5bb4ab8c-1a77-488c-980e-4745d3ad3eea
-- title:
--   The derivative of the truncated zeta representation $\zeta_0$ agrees with $\zeta'$
-- statement:
--   Let $N$ be a positive natural number and let $s \in \mathbb{C}$ with $\operatorname{Re} s > 0$ and $s \neq 1$. Let $\zeta_0(N, \cdot)$ denote the truncated (Euler-Maclaurin) representation of the Riemann zeta function,
--   $$\zeta_0(N, s) = \sum_{n=1}^{N} n^{-s} - \frac{N^{1-s}}{1-s} - \frac{N^{-s}}{2} + s \int_N^\infty \frac{\lfloor x \rfloor + \tfrac{1}{2} - x}{x^{s+1}} \, dx.$$
--   Then the complex derivative of $\zeta_0(N,\cdot)$ at $s$ equals the derivative of the Riemann zeta function:
--   $$\frac{d}{ds}\, \zeta_0(N, s) = \zeta'(s).$$
--
--   Since $\zeta_0(N,\cdot)$ agrees with $\zeta$ on the region $\{\operatorname{Re} s > 0,\ s \neq 1\}$ and both are holomorphic there, their derivatives coincide as well.
--
--   This lemma is the key transfer principle in the PNT+ project's explicit bounds for $\zeta'(s)$ in the critical strip: growth estimates are proved for the concrete, term-by-term differentiable expression $\zeta_0$, and this identity converts them into bounds for $\zeta'$ itself, which then feed the zero-free-region and Perron-contour arguments of the Prime Number Theorem with error term.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1183-L1193

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

theorem DerivZeta0EqDerivZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re)
    (s_ne_one : s ≠ 1) :
    deriv (ζ₀ N) s = ζ' s := by sorry
