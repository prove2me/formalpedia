-- Prove2me | Theorems.Thm_ZetaSum_aux1_4_prime
-- name    : ZetaSum_aux1_4_prime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:38:49.160859+00:00
-- url     : https://prove2.me/theorems/e79cdd8a-b741-44f0-ab5b-ed73aef08148
-- title:
--   Pointwise norm identity: $\|(\lfloor x\rfloor + \tfrac12 - x)/x^{s+1}\| = |\lfloor x\rfloor + \tfrac12 - x| \, x^{-\mathrm{Re}(s+1)}$ for $x > 0$
-- statement:
--   Let $x$ be a real number with $x > 0$ and let $s \in \mathbb{C}$. Then
--   $$\left\| \frac{\lfloor x \rfloor + \tfrac12 - x}{x^{s+1}} \right\| \;=\; \frac{\bigl\| \lfloor x \rfloor + \tfrac12 - x \bigr\|}{x^{\mathrm{Re}(s+1)}},$$
--   where in the numerator on the left the sawtooth value is regarded as a complex number and $x^{s+1}$ is a complex power of the positive real $x$, while on the right $x^{\mathrm{Re}(s+1)}$ is a real power.
--
--   This is the pointwise form of the standard identity $|x^{w}| = x^{\mathrm{Re}(w)}$ for positive real base $x$ and complex exponent $w$, specialized to the sawtooth integrand of the Euler-Maclaurin remainder. Integrating it over an interval $[a,b] \subset (0,\infty)$ yields the integral version, which converts all complex-norm estimates of the zeta remainder integrals into elementary real calculus.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L659-L663

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

theorem ZetaSum_aux1_4_prime (x : ℝ) (hx : 0 < x) (s : ℂ) :
      ‖(⌊x⌋ + 1 / 2 - (x : ℝ)) / (x : ℂ) ^ (s + 1)‖ =
      ‖⌊x⌋ + 1 / 2 - x‖ / x ^ ((s + 1).re) := by sorry
