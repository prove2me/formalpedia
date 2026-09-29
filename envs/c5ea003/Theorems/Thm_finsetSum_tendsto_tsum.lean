-- Prove2me | Theorems.Thm_finsetSum_tendsto_tsum
-- name    : finsetSum_tendsto_tsum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:28:47.204672+00:00
-- url     : https://prove2.me/theorems/2aae6f0e-2aca-44d8-8114-72a712772ba3
-- title:
--   Partial sums $\sum_{n=N}^{k-1} f(n)$ of a summable series converge to the tail sum $\sum_{n \geq N} f(n)$
-- statement:
--   Let $f : \mathbb{N} \to \mathbb{C}$ be summable and let $N \in \mathbb{N}$. Then the finite partial sums over the interval $[N, k)$ converge, as $k \to \infty$, to the sum of the shifted series:
--
--   $$\lim_{k \to \infty} \sum_{n = N}^{k-1} f(n) \;=\; \sum_{n = 0}^{\infty} f(n + N),$$
--
--   where the right-hand side is the (unconditional) sum of the summable sequence $n \mapsto f(n+N)$, i.e. the tail $\sum_{n \geq N} f(n)$ of the original series.
--
--   This is a bookkeeping lemma connecting finite `Finset` partial sums to infinite tail sums. In the truncated zeta representation $\zeta_0$, where $\zeta(s)$ is split into an initial finite sum $\sum_{n < N} n^{-s}$ plus tail terms, this lemma justifies passing between finite truncations and the limiting tail series.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L734-L744

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

theorem finsetSum_tendsto_tsum {N : ℕ} {f : ℕ → ℂ} (hf : Summable f) :
    Tendsto (fun (k : ℕ) ↦ ∑ n ∈ Finset.Ico N k, f n) atTop (𝓝 (∑' (n : ℕ), f (n + N))) := by sorry
