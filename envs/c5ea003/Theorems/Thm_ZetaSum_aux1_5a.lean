-- Prove2me | Theorems.Thm_ZetaSum_aux1_5a
-- name    : ZetaSum_aux1_5a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:10:26.961296+00:00
-- url     : https://prove2.me/theorems/49f45081-d1c9-4f4c-9f37-2b695e177282
-- title:
--   Pointwise bound: $|\lfloor x\rfloor + 1/2 - x|/x^{\sigma+1} \le 1/x^{\sigma+1}$ for $x$ in a positive interval
-- statement:
--   Let $a, b$ be real numbers with $0 < a$, let $s \in \mathbb{C}$, and let $x$ be a real number lying in the closed interval $[a, b]$ (so in particular $x > 0$). Writing $\sigma = \operatorname{Re}(s)$ and $\lfloor x \rfloor$ for the floor of $x$, the centered sawtooth quotient satisfies the pointwise bound
--
--   $$\frac{\left|\lfloor x\rfloor + \tfrac{1}{2} - x\right|}{x^{\sigma+1}} \;\le\; \frac{1}{x^{\sigma+1}}.$$
--
--   The content is simply that the centered fractional-part expression $\lfloor x\rfloor + \tfrac12 - x$ has absolute value at most $\tfrac12 \le 1$, combined with positivity of the denominator $x^{\sigma+1}$ for $x > 0$. This is the pointwise ingredient behind the integral comparison used in the Euler--Maclaurin analysis of the Riemann zeta function's partial sums in the PNT+ project.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L671-L675

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

theorem ZetaSum_aux1_5a {a b : ℝ} (apos : 0 < a) {s : ℂ} (x : ℝ)
  (h : x ∈ Icc a b) : |↑⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤ 1 / x ^ (s.re + 1) := by sorry
