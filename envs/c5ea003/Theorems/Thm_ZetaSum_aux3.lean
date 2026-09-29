-- Prove2me | Theorems.Thm_ZetaSum_aux3
-- name    : ZetaSum_aux3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:29:14.207226+00:00
-- url     : https://prove2.me/theorems/9283b56b-769a-4290-94ec-0353acb9c5a7
-- title:
--   Convergence of partial sums $\sum_{N < n \le k} n^{-s}$ to the zeta tail series for $\operatorname{Re}(s) > 1$
-- statement:
--   Let $N$ be a natural number and let $s \in \mathbb{C}$ with $\operatorname{Re}(s) > 1$. Then the finite partial sums over the integer ranges $(N, k]$ converge, as $k \to \infty$, to the tail sum of the Dirichlet series:
--
--   $$\sum_{n = N+1}^{k} \frac{1}{n^{s}} \;\xrightarrow[k \to \infty]{}\; \sum_{n=0}^{\infty} \frac{1}{(n + N + 1)^{s}},$$
--
--   where the right-hand side is the (absolutely convergent) topological sum over all integers exceeding $N$.
--
--   This is the limit-bookkeeping lemma that identifies the finite Abel-summation expressions with the infinite tail series appearing in the Euler--Maclaurin representation of $\zeta(s)$. It lets the PNT+ development pass from identities proved for finite ranges $(N, k]$ to the tail formula $\sum_{n > N} n^{-s} = -N^{1-s}/(1-s) - N^{-s}/2 + s\int_N^\infty(\lfloor x\rfloor + \tfrac12 - x)x^{-(s+1)}dx$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L764-L774

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

theorem ZetaSum_aux3 {N : ℕ} {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun k ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) atTop
    (𝓝 (∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s)) := by sorry
