-- Prove2me | Theorems.Thm_ZetaSum_aux1_2
-- name    : ZetaSum_aux1_2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:09:00.398433+00:00
-- url     : https://prove2.me/theorems/fa9e7f28-fb98-4c5d-8c56-307cc726e3bc
-- title:
--   Power-integral evaluation: $\int_a^b x^{-(c+1)} dx = (a^{-c} - b^{-c})/c$
-- statement:
--   Let $a, b, c$ be real numbers with $0 < a < b$, and assume $c \ne 0$ and $0 \notin [[a, b]]$ (the interval of integration avoids the origin). Then
--   $$\int_{a}^{b} \frac{1}{x^{c+1}} \, dx \;=\; \frac{a^{-c} - b^{-c}}{c}.$$
--
--   This closed-form evaluation of the elementary power integral (with real exponents, via the fundamental theorem of calculus applied to $x \mapsto -x^{-c}/c$) is the calculus backbone of the sawtooth-tail estimates: bounding $\int_a^b \|(\lfloor x\rfloor + \tfrac12 - x)\, x^{-s-1}\|\,dx$ reduces, after the pointwise bound $|\lfloor x\rfloor + \tfrac12 - x| \le \tfrac12$, to exactly this integral with $c = \mathrm{Re}(s)$. Letting $b \to \infty$ for $c > 0$ gives the $N^{-\sigma}/\sigma$ tail bounds in the truncated zeta representation.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L644-L654

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

theorem ZetaSum_aux1_2 {a b : ℝ} {c : ℝ} (apos : 0 < a) (a_lt_b : a < b)
    (h : c ≠ 0 ∧ 0 ∉ [[a, b]]) :
    ∫ (x : ℝ) in a..b, 1 / x ^ (c+1) = (a ^ (-c) - b ^ (-c)) / c := by sorry
