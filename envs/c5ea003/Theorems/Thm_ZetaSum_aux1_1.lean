-- Prove2me | Theorems.Thm_ZetaSum_aux1_1
-- name    : ZetaSum_aux1_1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:08:08.451466+00:00
-- url     : https://prove2.me/theorems/e13c44f8-ebad-46a7-a808-47cf314aba40
-- title:
--   Positivity on the interval: $x \in [a, b]$ with $0 < a < b$ implies $x > 0$
-- statement:
--   Let $a, b, x$ be real numbers with $0 < a$ and $a < b$, and suppose $x$ belongs to the unordered closed interval $[[a, b]]$ (the closed interval between $a$ and $b$, i.e. $[\min(a,b), \max(a,b)]$). Then
--   $$x > 0.$$
--
--   A trivial but frequently used positivity lemma: in the Euler-Maclaurin manipulations for the partial zeta sums, one constantly integrates expressions like $(\lfloor x \rfloor + \tfrac12 - x)\, x^{-(s+1)}$ over intervals $[a, b]$ with $0 < a < b$, and every rewriting of $x^{-(s+1)}$ (real-to-complex power comparisons, norm computations, integrability arguments) requires knowing that the variable of integration is strictly positive. This lemma discharges that side condition for the unordered-interval (`uIcc`) formulation used by the interval integral.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L641-L642

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

theorem ZetaSum_aux1_1 {a b x : ℝ} (apos : 0 < a) (a_lt_b : a < b) (hx : x ∈ [[a, b]]) : 0 < x := by sorry
