-- Prove2me | Theorems.Thm_riemannZeta_isBigO_near_one_horizontal
-- name    : riemannZeta_isBigO_near_one_horizontal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:53:28.095898+00:00
-- url     : https://prove2.me/theorems/9637dcc9-a967-4781-9646-5924020455b1
-- title:
--   Growth of $\zeta$ approaching $s=1$ horizontally: $\zeta(1+x) = O(1/x)$ as $x \to 0^+$
-- statement:
--   Approaching the pole of the Riemann zeta function along the real axis from the right, $\zeta$ grows no faster than the reciprocal of the distance to the pole: as the real parameter $x \to 0^+$ (the filter of right-neighborhoods of $0$),
--
--   $$\zeta(1+x) \;=\; O\!\left( \frac{1}{x} \right).$$
--
--   Here $x$ ranges over positive reals and $1 + x$ is the corresponding point on the real axis just to the right of $s = 1$.
--
--   This horizontal growth bound is exactly the rate dictated by the simple pole of residue $1$ at $s = 1$. In the classical $3$-$4$-$1$ argument for the zero-free region, it quantifies the blow-up of the factor $\zeta(1+x)^3$ as $x \to 0^+$; the interplay between this $O(x^{-3})$ growth and the vanishing of $\zeta(1+x+iy)^4$ at a hypothetical zero $1 + iy$ is what forces $\zeta(1+iy) \ne 0$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1858-L1869

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

theorem riemannZeta_isBigO_near_one_horizontal :
    (fun x : ℝ ↦ ζ (1 + x)) =O[𝓝[>] 0] (fun x ↦ (1 : ℂ) / x) := by sorry
