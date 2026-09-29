-- Prove2me | Theorems.Thm_ZetaSum_aux1_3
-- name    : ZetaSum_aux1_3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:09:58.708731+00:00
-- url     : https://prove2.me/theorems/648b186a-092e-4a7c-9c9e-d0b481682a72
-- title:
--   Sawtooth bound: $\bigl|\lfloor x \rfloor + \tfrac12 - x\bigr| \le \tfrac12$ for all real $x$
-- statement:
--   For every real number $x$,
--   $$\bigl\| \lfloor x \rfloor + \tfrac12 - x \bigr\| \;\le\; \tfrac12.$$
--
--   The function $x \mapsto \lfloor x \rfloor + \tfrac12 - x$ is (the negative of) the first periodized Bernoulli polynomial $B_1(\{x\}) = \{x\} - \tfrac12$, the sawtooth appearing in first-order Euler-Maclaurin summation; since the fractional part $\{x\} = x - \lfloor x \rfloor$ lies in $[0, 1)$, the sawtooth takes values in $(-\tfrac12, \tfrac12]$, hence is bounded in absolute value by $\tfrac12$. This uniform bound is applied under the integral sign every time the Euler-Maclaurin remainder $\int (\lfloor x\rfloor + \tfrac12 - x)\, x^{-s-1} dx$ is estimated in the zeta-bound development.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L656-L657

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

theorem ZetaSum_aux1_3 (x : ℝ) : ‖(⌊x⌋ + 1/2 - x)‖ ≤ 1/2 := by sorry
