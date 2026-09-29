-- Prove2me | Theorems.Thm_harmonic_eq_sum_Icc0_aux
-- name    : harmonic_eq_sum_Icc0_aux
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:02:02.612607+00:00
-- url     : https://prove2.me/theorems/07b15866-5b97-4b56-a56e-315187c9d2ad
-- title:
--   Dropping the vanishing $i = 0$ term: $\sum_{i=0}^{N} i^{-1} = \sum_{i=1}^{N} i^{-1}$
-- statement:
--   For every natural number $N$,
--
--   $$\sum_{i = 0}^{N} \frac{1}{i} \;=\; \sum_{i = 1}^{N} \frac{1}{i},$$
--
--   where the sums are over the integer intervals $\{0, \dots, N\}$ and $\{1, \dots, N\}$ respectively, and the $i = 0$ term is $0$ by the convention $0^{-1} = 0$ for real division in Lean.
--
--   This is the auxiliary re-indexing step behind the identification of $\sum_{i \in [0,N]} i^{-1}$ with the harmonic number $H_N$: it isolates exactly the observation that the boundary term at $i = 0$ vanishes, so interval sums starting at $0$ or at $1$ agree.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1440-L1445

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

theorem harmonic_eq_sum_Icc0_aux (N : ℕ) :
    ∑ i ∈ Finset.Icc 0 N, (i : ℝ)⁻¹ = ∑ i ∈ Finset.Icc 1 N, (i : ℝ)⁻¹ := by sorry
