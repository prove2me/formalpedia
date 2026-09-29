-- Prove2me | Theorems.Thm_harmonic_eq_sum_Icc0
-- name    : harmonic_eq_sum_Icc0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:02:31.248279+00:00
-- url     : https://prove2.me/theorems/813a9552-5f20-4862-a2c2-9f4b69b6db9f
-- title:
--   The sum $\sum_{i=0}^{N} i^{-1}$ equals the harmonic number $H_N$
-- statement:
--   For every natural number $N$,
--
--   $$\sum_{i = 0}^{N} \frac{1}{i} \;=\; H_N,$$
--
--   where $H_N = \sum_{i=1}^{N} 1/i$ is the $N$-th harmonic number (a rational number, here coerced to $\mathbb{R}$), and the term $i = 0$ contributes nothing by the standard convention $0^{-1} = 0$ in Lean's real-number division.
--
--   The content is purely a re-indexing: the sum over the closed interval $\{0, 1, \dots, N\}$ coincides with the usual harmonic number because the spurious $i = 0$ term vanishes. This lets estimates phrased over $\sum_{i \in [0,N]} i^{-1}$ — as naturally arise from Euler–Maclaurin-style manipulations in the zeta bounds — be rewritten in terms of the library's harmonic number $H_N$ and its known asymptotics $H_N = \log N + \gamma + O(1/N)$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1447-L1449

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

theorem harmonic_eq_sum_Icc0 (N : ℕ) : ∑ i ∈ Finset.Icc 0 N, (i : ℝ)⁻¹ = (harmonic N : ℝ) := by sorry
