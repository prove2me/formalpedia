-- Prove2me | Theorems.Thm_Tendsto_nhdsWithin_punctured_add
-- name    : Tendsto_nhdsWithin_punctured_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:53:03.446045+00:00
-- url     : https://prove2.me/theorems/ebc86921-06c1-472d-a5e1-0dbe8fc825c9
-- title:
--   Translation maps the right-punctured neighborhood filter: $y \mapsto y + a$ sends $\mathcal{N}_{>x}$ to $\mathcal{N}_{>x+a}$
-- statement:
--   Let $a$ and $x$ be real numbers. Consider the filter $\mathcal{N}_{>x}$ of right-punctured neighborhoods of $x$ — the neighborhood filter of $x$ within the open ray $(x, \infty)$, describing approach to $x$ strictly from the right.
--
--   Then translation by $a$ carries this filter to the corresponding filter at $x + a$:
--
--   $$\lim_{\substack{y \to x \\ y > x}} (y + a) \;=\; x + a \quad\text{within } (x + a, \infty),$$
--
--   i.e. the map $y \mapsto y + a$ tends to $\mathcal{N}_{>(x+a)}$ along $\mathcal{N}_{>x}$.
--
--   This is a small topological lemma about one-sided limits under translation. In the PNT+ zeta-bounds development it is used when manipulating one-sided limits that arise from integral representations and boundary evaluations of $\zeta$-related integrals, where substitutions shift the base point of a limit from the right.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1854-L1856

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

theorem Tendsto_nhdsWithin_punctured_add (a x : ℝ) :
    Tendsto (fun y ↦ y + a) (𝓝[>] x) (𝓝[>] (x + a)) := by sorry
