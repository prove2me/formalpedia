-- Prove2me | Theorems.Thm_ZetaSum_aux1
-- name    : ZetaSum_aux1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:27:49.380659+00:00
-- url     : https://prove2.me/theorems/ca085bca-4247-4e73-af30-acef23cf8265
-- title:
--   Euler-Maclaurin (first order) for partial zeta sums: exact formula for $\sum_{a < n \le b} n^{-s}$
-- statement:
--   Let $a, b$ be natural numbers with $0 < a < b$, and let $s \in \mathbb{C}$ with $s \ne 1$ and $s \ne 0$. Then the partial Dirichlet sum admits the exact first-order Euler-Maclaurin representation
--   $$\sum_{a < n \le b} \frac{1}{n^{s}} \;=\; \frac{b^{1-s} - a^{1-s}}{1-s} \;+\; \frac{1}{2}\, b^{-s} \;-\; \frac{1}{2}\, a^{-s} \;+\; s \int_{a}^{b} \bigl( \lfloor x \rfloor + \tfrac12 - x \bigr)\, x^{-(s+1)} \, dx,$$
--   where the sum runs over integers $n$ with $a < n \le b$ and $\lfloor x \rfloor + \tfrac12 - x$ is the (shifted) sawtooth function.
--
--   This identity — partial summation against the sawtooth $B_1(\{x\}) = \{x\} - \tfrac12$ — is the exact finite building block behind the analytic continuation of $\zeta$ to $\mathrm{Re}(s) > 0$: letting $b \to \infty$ for $\mathrm{Re}(s) > 1$ and rearranging yields the truncated representation $\zeta_0(N, s)$, whose integral tail converges for all $\mathrm{Re}(s) > 0$. All the explicit upper and lower bounds for $\zeta$ and $\zeta'$ near the $1$-line in this development are read off from this formula and its differentiated version.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L616-L636

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
set_option backward.isDefEq.respectTransparency false

theorem ZetaSum_aux1 {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (s_ne_zero : s ≠ 0) (ha : a ∈ Ioo 0 b) :
    ∑ n ∈ Finset.Ioc a b, 1 / (n : ℂ) ^ s =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) + 1 / 2 * (1 / b ^ (s)) - 1 / 2 * (1 / a ^ s)
      + s * ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by sorry
