-- Prove2me | Theorems.Thm_ZetaSum_aux2
-- name    : ZetaSum_aux2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:29:41.30334+00:00
-- url     : https://prove2.me/theorems/f01f8168-69d2-4680-be5b-2423dc15b66f
-- title:
--   Euler--Maclaurin formula for the zeta tail: $\sum_{n > N} n^{-s}$ as main terms plus a sawtooth integral
-- statement:
--   Let $N$ be a positive natural number and let $s \in \mathbb{C}$ with $\operatorname{Re}(s) > 1$. Then the tail of the Dirichlet series for $\zeta(s)$ beyond $N$ admits the Euler--Maclaurin (Abel summation) representation
--
--   $$\sum_{n=0}^{\infty} \frac{1}{(n + N + 1)^{s}} \;=\; \frac{-\,N^{1-s}}{1-s} \;-\; \frac{N^{-s}}{2} \;+\; s \int_{N}^{\infty} \left(\lfloor x\rfloor + \tfrac{1}{2} - x\right) x^{-(s+1)}\, dx,$$
--
--   where the sum on the left runs over all integers exceeding $N$, $\lfloor x\rfloor$ is the floor function, and the integral is over the ray $(N, \infty)$.
--
--   This identity is the analytic heart of the truncated zeta representation: the first two terms are the smooth main term and the half-integer boundary correction, while the sawtooth integral converges absolutely for $\operatorname{Re}(s) > 0$ and hence furnishes the analytic continuation of the tail past the line $\operatorname{Re}(s) = 1$. In the PNT+ project it is the key step in deriving the formula $\zeta(s) = \sum_{n \le N} n^{-s} + \text{main terms} + \text{error integral}$ from which the $O(\log|t|)$ upper bounds on $\zeta$ near the $1$-line are extracted.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L787-L814

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

theorem ZetaSum_aux2 {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 1 < s.re) :
    ∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s =
    (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by sorry
