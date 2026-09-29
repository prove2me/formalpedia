-- Prove2me | Theorems.Thm_ZetaSum_aux1_sub1
-- name    : ZetaSum_aux1_sub1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:41:35.213012+00:00
-- url     : https://prove2.me/theorems/4e50fdfe-a40f-4660-ac55-2f2328b3f342
-- title:
--   Evaluation of $\int_a^b x^{-s}\,dx = \dfrac{b^{1-s} - a^{1-s}}{1-s}$ for $s \neq 1$
-- statement:
--   Let $a, b$ be natural numbers with $0 < a < b$, and let $s \in \mathbb{C}$ with $s \neq 1$. Then the interval integral of the complex power function evaluates in closed form:
--
--   $$\int_a^b \frac{1}{x^{s}}\, dx \;=\; \frac{b^{1-s} - a^{1-s}}{1-s},$$
--
--   where the real variable $x$ is coerced into $\mathbb{C}$ before taking the power, and $a^{1-s}, b^{1-s}$ denote complex powers of the (positive) endpoints.
--
--   This is the fundamental antiderivative computation for $x^{-s}$ on an interval of positive reals, valid for every complex exponent except the logarithmic case $s = 1$. In the PNT+ development it produces the main term $\dfrac{b^{1-s} - a^{1-s}}{1-s}$ of the Euler--Maclaurin formula for $\sum_{a < n \le b} n^{-s}$, which in turn gives the truncated representation of $\zeta(s)$ used to prove the $\log|t|$ upper bounds near the $1$-line.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L574-L582

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

theorem ZetaSum_aux1_sub1 {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (ha : a ∈ Ioo 0 b) :
    (∫ (x : ℝ) in a..b, 1 / (x : ℂ) ^ s) =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) := by sorry
