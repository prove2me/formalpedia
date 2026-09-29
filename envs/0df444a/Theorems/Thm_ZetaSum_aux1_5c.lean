-- Prove2me | Theorems.Thm_ZetaSum_aux1_5c
-- name    : ZetaSum_aux1_5c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:11:48.732629+00:00
-- url     : https://prove2.me/theorems/26206e65-5ff7-4291-b5b8-df46a0dce4e0
-- title:
--   Measurability of the sawtooth quotient $u \mapsto |\lfloor u\rfloor + 1/2 - u|/u^{\sigma+1}$
-- statement:
--   Let $a, b$ be real numbers and $s \in \mathbb{C}$, and write $\sigma = \operatorname{Re}(s)$. Consider the real-valued function
--
--   $$g(u) \;=\; \frac{\left|\lfloor u\rfloor + \tfrac{1}{2} - u\right|}{u^{\sigma+1}},$$
--
--   where $\lfloor u \rfloor$ is the floor of $u$. Then $g$ is almost-everywhere strongly measurable with respect to Lebesgue measure restricted to the interval between $a$ and $b$.
--
--   The floor function is piecewise constant (hence Borel measurable) and the power denominator is continuous away from $0$, so the quotient is measurable; the lemma records this in the precise measure-theoretic form (a.e. strong measurability on the restricted measure) demanded by Mathlib's integrability API. It is a plumbing step for establishing interval integrability of the sawtooth quotient in the zeta-bound estimates of the PNT+ project.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L689-L695

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
open MeasureTheory

theorem ZetaSum_aux1_5c {a b : ℝ} {s : ℂ} :
    let g : ℝ → ℝ := fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1);
    AEStronglyMeasurable g
      (Measure.restrict volume (Ι a b)) := by sorry
