-- Prove2me | Theorems.Thm_Zeta0EqZeta
-- name    : Zeta0EqZeta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:31:32.766103+00:00
-- url     : https://prove2.me/theorems/1553bad9-293f-4a81-9316-5eb57bb17f90
-- title:
--   The truncated Euler-Maclaurin representation $\zeta_0(N, s)$ equals $\zeta(s)$ for $\mathrm{Re}(s) > 0$
-- statement:
--   Let $N$ be a positive natural number and let $s \in \mathbb{C}$ satisfy $\mathrm{Re}(s) > 0$ and $s \ne 1$. Define the truncated (Euler-Maclaurin) zeta representation
--   $$\zeta_0(N, s) \;=\; \sum_{n=0}^{N} \frac{1}{n^{s}} \;-\; \frac{N^{1-s}}{1-s} \;-\; \frac{N^{-s}}{2} \;+\; s \int_{N}^{\infty} \frac{\lfloor x \rfloor + \tfrac12 - x}{x^{s+1}} \, dx,$$
--   where the $n = 0$ term of the sum vanishes. Then
--   $$\zeta_0(N, s) = \zeta(s),$$
--   the Riemann zeta function.
--
--   This identity is the analytic-continuation workhorse of the zeta-bounds development: the right-hand side of $\zeta_0$ converges and is analytic for $\mathrm{Re}(s) > 0$, $s \ne 1$, so the formula extends $\zeta$ past the abscissa of convergence of its Dirichlet series and simultaneously provides a representation from which explicit upper and lower bounds ($|\zeta| \ll \log|t|$, $|\zeta'| \ll \log^2|t|$, zero-free-region estimates) can be read off. The truncation point $N$ is later chosen as $\lfloor |t| \rfloor$ to optimize the resulting bounds.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1153-L1181

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

theorem Zeta0EqZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    ζ₀ N s = riemannZeta s := by sorry
