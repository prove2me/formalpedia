-- Prove2me | Theorems.Thm_isPathConnected_aux
-- name    : isPathConnected_aux
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:30:37.628076+00:00
-- url     : https://prove2.me/theorems/ce1e3302-233a-415b-a72c-af00963d6bc1
-- title:
--   Path-connectedness of the punctured half-plane $\{ z : z \neq 1,\ \operatorname{Re} z > 0 \}$
-- statement:
--   The set
--
--   $$\{\, z \in \mathbb{C} \;:\; z \neq 1 \ \text{and} \ \operatorname{Re} z > 0 \,\}$$
--
--   is path-connected: any two of its points can be joined by a continuous path staying inside the set.
--
--   Geometrically, this is the open right half-plane with the single point $z = 1$ removed; removing one point from a two-dimensional connected open set does not disconnect it, and explicit paths (going around the puncture) witness this.
--
--   Together with openness, path-connectedness makes this punctured half-plane a connected domain in the sense required by the identity theorem for holomorphic functions. This is how the equality $\zeta = \zeta_0$, established initially on the sub-region $\operatorname{Re} s > 1$, is propagated to the whole punctured half-plane $\operatorname{Re} s > 0$, $s \neq 1$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1098-L1151

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

theorem isPathConnected_aux : IsPathConnected {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by sorry
