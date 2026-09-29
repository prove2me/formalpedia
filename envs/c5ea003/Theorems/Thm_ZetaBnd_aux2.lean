-- Prove2me | Theorems.Thm_ZetaBnd_aux2
-- name    : ZetaBnd_aux2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:01:03.556717+00:00
-- url     : https://prove2.me/theorems/7a920271-edf2-48de-8c95-c980333acd8c
-- title:
--   Term bound $\|n^{-(\sigma+it)}\| \le e^A / n$ for $n \le |t|$ near the $1$-line
-- statement:
--   Let $n$ be a natural number and $t, A, \sigma$ real numbers with $A > 0$, $\sigma > 0$, and $n \le |t|$. Assume $\sigma$ lies in the region
--   $$\sigma \ge 1 - \frac{A}{\log |t|}.$$
--   Then the $n$-th term of the Dirichlet series for $\zeta$ at $s = \sigma + it$ satisfies
--   $$\bigl\| n^{-(\sigma + it)} \bigr\| \le \frac{e^{A}}{n}.$$
--
--   Since $\|n^{-(\sigma+it)}\| = n^{-\sigma} = n^{-1} \cdot n^{1-\sigma}$, the point is that for $n \le |t|$ the excess factor obeys $n^{1-\sigma} \le |t|^{A/\log|t|} = e^A$. Summing this bound over $n \le \lfloor |t| \rfloor$ produces the harmonic sum that yields $|\zeta(\sigma + it)| = O(\log|t|)$ in the region $\sigma \ge 1 - A/\log|t|$; it is the per-term engine of that classical estimate.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1217-L1247

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

theorem ZetaBnd_aux2 {n : ℕ} {t A σ : ℝ} (Apos : 0 < A) (σpos : 0 < σ) (n_le_t : n ≤ |t|)
    (σ_ge : (1 : ℝ) - A / Real.log |t| ≤ σ) :
    ‖(n : ℂ) ^ (-(σ + t * I))‖ ≤ (n : ℝ)⁻¹ * Real.exp A := by sorry
