-- Prove2me | Theorems.Thm_riemannZeta0_apply
-- name    : riemannZeta0_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:31:06.75514+00:00
-- url     : https://prove2.me/theorems/67be4c45-88db-484b-ad9b-e05a75ab65e8
-- title:
--   Euler–Maclaurin formula for the truncated zeta representation $\zeta_0(N, s)$
-- statement:
--   For every natural number $N$ and complex number $s$, the truncated zeta representation $\zeta_0$ (the project's `riemannZeta0`) unfolds to the explicit first-order Euler--Maclaurin expression
--
--   $$\zeta_0(N, s) \;=\; \sum_{n=0}^{N} \frac{1}{n^s} \;+\; \left( \frac{-N^{1-s}}{1-s} \;+\; \frac{-N^{-s}}{2} \;+\; s \int_{N}^{\infty} \left( \lfloor x \rfloor + \tfrac12 - x \right) x^{-(s+1)} \, dx \right).$$
--
--   Here the finite sum runs over $n \in \{0, 1, \dots, N\}$ (the $n = 0$ term vanishing under the convention $0^{-s}$ for $s \ne 0$), the two middle terms are the boundary contributions from the Euler--Maclaurin formula, and the integral over $(N, \infty)$ involves the sawtooth function $\lfloor x \rfloor + \tfrac12 - x$.
--
--   This identity is definitional unfolding: it exposes the concrete formula behind $\zeta_0$, the analytic continuation device used throughout the PNT+ zeta-bounds development. Because the integral converges for $\operatorname{Re}(s) > 0$, the right-hand side extends $\zeta$ beyond the half-plane of absolute convergence, and all the explicit growth bounds on $\zeta$ and $\zeta'$ near the line $\operatorname{Re}(s) = 1$ are proved by estimating each of these four pieces.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L530-L534

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

theorem riemannZeta0_apply (N : ℕ) (s : ℂ) : ζ₀ N s =
    (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
    ((- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) := by sorry
