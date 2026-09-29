-- Prove2me | Theorems.Thm_ZetaSum_aux1_5
-- name    : ZetaSum_aux1_5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:12:41.749845+00:00
-- url     : https://prove2.me/theorems/3a6094d3-7574-44b7-a297-00eb3cf07d15
-- title:
--   Integral comparison: the sawtooth quotient $|\lfloor x\rfloor + 1/2 - x|/x^{\sigma+1}$ is dominated by $1/x^{\sigma+1}$ on $[a,b]$
-- statement:
--   Let $a, b$ be real numbers with $0 < a < b$, and let $s \in \mathbb{C}$ have positive real part, $\sigma = \operatorname{Re}(s) > 0$. Write $\lfloor x \rfloor$ for the integer floor of $x$, so that $\lfloor x \rfloor + \tfrac{1}{2} - x$ is the centered sawtooth function appearing in Euler--Maclaurin summation. Then the integral of the sawtooth quotient is dominated by the integral of the pure power:
--
--   $$\int_a^b \frac{\left|\lfloor x\rfloor + \tfrac{1}{2} - x\right|}{x^{\sigma+1}}\, dx \;\le\; \int_a^b \frac{1}{x^{\sigma+1}}\, dx.$$
--
--   This monotonicity estimate is the integrated form of the trivial pointwise bound $|\lfloor x\rfloor + \tfrac12 - x| \le \tfrac12 \le 1$. In the PNT+ development it is one of the auxiliary steps used to control the error integral in the Euler--Maclaurin representation of partial sums of $\zeta(s)$, which underlies the explicit upper bounds for $\zeta$ in the zero-free region. It is reusable wherever one needs an $L^1$ bound on a sawtooth-weighted power integrand.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L707-L713

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

theorem ZetaSum_aux1_5 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤
    ∫ (x : ℝ) in a..b, 1 / x ^ (s.re + 1) := by sorry
