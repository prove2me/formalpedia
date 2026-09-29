-- Prove2me | Theorems.Thm_ZetaBnd_aux1a
-- name    : ZetaBnd_aux1a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:13:08.802262+00:00
-- url     : https://prove2.me/theorems/416f98cb-c47b-4e88-af8e-f31dd406c28f
-- title:
--   Integral bound for the sawtooth kernel: $\int_a^b \|(\lfloor x\rfloor + \tfrac12 - x) x^{-s-1}\| dx \le (a^{-\mathrm{Re}(s)} - b^{-\mathrm{Re}(s)})/\mathrm{Re}(s)$
-- statement:
--   Let $a, b$ be real numbers with $0 < a < b$, and let $s \in \mathbb{C}$ with $\mathrm{Re}(s) > 0$. Then the $L^1$-norm of the sawtooth kernel over $[a, b]$ satisfies
--   $$\int_{a}^{b} \left\| \frac{\lfloor x \rfloor + \tfrac12 - x}{x^{s+1}} \right\| dx \;\le\; \frac{a^{-\mathrm{Re}(s)} - b^{-\mathrm{Re}(s)}}{\mathrm{Re}(s)}.$$
--
--   The proof idea (not part of the statement) is simply that the sawtooth $\lfloor x \rfloor + \tfrac12 - x$ has absolute value at most $\tfrac12$, and $\int_a^b x^{-\mathrm{Re}(s)-1} dx$ evaluates exactly to the right-hand side up to the factor $\tfrac12$; the stated form keeps a clean closed expression that telescopes when $b \to \infty$. This finite-interval estimate is the quantitative core behind the convergence and bounding of the tail integral $\int_N^\infty (\lfloor x\rfloor + \tfrac12 - x) x^{-s-1}\,dx$ in the Euler-Maclaurin representation of $\zeta$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L715-L723

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

theorem ZetaBnd_aux1a {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
    ∫ x in a..b, ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤
      (a ^ (-s.re) - b ^ (-s.re)) / s.re := by sorry
