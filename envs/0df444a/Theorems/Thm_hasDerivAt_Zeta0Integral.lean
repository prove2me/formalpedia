-- Prove2me | Theorems.Thm_hasDerivAt_Zeta0Integral
-- name    : hasDerivAt_Zeta0Integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:24:25.948411+00:00
-- url     : https://prove2.me/theorems/d40a1355-7a0e-4023-9c37-22712e170349
-- title:
--   Differentiation under the integral sign for the Euler–Maclaurin tail integral of $\zeta_0$
-- statement:
--   Fix a natural number $N > 0$ and a complex number $s$ with $\operatorname{Re} s > 0$. Consider the tail integral appearing in the truncated zeta representation $\zeta_0$,
--
--   $$F(z) \;=\; \int_{N}^{\infty} \Big( \lfloor x \rfloor + \tfrac{1}{2} - x \Big)\, x^{-z-1} \, dx,$$
--
--   where $\lfloor x \rfloor + \tfrac12 - x$ is the (bounded, $1$-periodic-type) sawtooth correction from Euler–Maclaurin summation. Then $F$ is complex differentiable at $s$, and its derivative is obtained by differentiating under the integral sign:
--
--   $$F'(s) \;=\; \int_{N}^{\infty} \Big( \lfloor x \rfloor + \tfrac{1}{2} - x \Big)\, x^{-s-1} \, (-\log x) \, dx.$$
--
--   This is the key analyticity statement for the tail term of $\zeta_0$: it shows the Euler–Maclaurin remainder integral defines a holomorphic function of $s$ on the half-plane $\operatorname{Re} s > 0$, with an explicit derivative. Combined with the finite-sum and pole terms of $\zeta_0$, it yields the analytic continuation of $\zeta$ (and formulas for $\zeta'$) into the critical strip region needed for the zero-free-region and contour estimates of the Prime Number Theorem.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L951-L1040

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
open MeasureTheory

theorem hasDerivAt_Zeta0Integral {N : ℕ} (Npos : 0 < N) {s : ℂ} (hs : s ∈ {s | 0 < s.re}) :
  HasDerivAt (fun z ↦ ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-z - 1))
    (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x)) s := by sorry
