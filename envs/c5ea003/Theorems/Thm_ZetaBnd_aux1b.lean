-- Prove2me | Theorems.Thm_ZetaBnd_aux1b
-- name    : ZetaBnd_aux1b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:14:27.844381+00:00
-- url     : https://prove2.me/theorems/fe7713f1-7670-4fa6-aad2-4da32a1da666
-- title:
--   Tail sawtooth integral bound: $\|\int_N^{\infty} (\lfloor x\rfloor + \tfrac12 - x) x^{-(\sigma+it)-1} dx\| \le N^{-\sigma}/\sigma$
-- statement:
--   Let $N \ge 1$ be a natural number and let $\sigma, t$ be real numbers with $\sigma > 0$. Then the improper integral of the sawtooth kernel over $(N, \infty)$ satisfies
--   $$\left\| \int_{N}^{\infty} \frac{\lfloor x \rfloor + \tfrac12 - x}{x^{(\sigma + it) + 1}} \, dx \right\| \;\le\; \frac{N^{-\sigma}}{\sigma}.$$
--
--   This is the tail estimate for the integral remainder in the truncated Euler-Maclaurin representation $\zeta_0(N, s)$ of the Riemann zeta function: since the sawtooth is bounded by $\tfrac12$ and $\int_N^\infty x^{-\sigma-1} dx = N^{-\sigma}/\sigma$, the remainder decays like $N^{-\sigma}$. It supplies the unsigned ingredient for the weighted bound $\|s \int_N^\infty \cdots\| \le 2|t| N^{-\sigma}/\sigma$ used in the $\log|t|$ upper bounds for $\zeta$ near the $1$-line.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L817-L840

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

theorem ZetaBnd_aux1b (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (σpos : 0 < σ) :
    ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ N ^ (-σ) / σ := by sorry
