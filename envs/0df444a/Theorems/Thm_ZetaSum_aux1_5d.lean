-- Prove2me | Theorems.Thm_ZetaSum_aux1_5d
-- name    : ZetaSum_aux1_5d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:12:15.847176+00:00
-- url     : https://prove2.me/theorems/3b22c08f-ae6f-4465-a3e2-9958fc7a7346
-- title:
--   Interval integrability of the sawtooth quotient $|\lfloor u\rfloor + 1/2 - u|/u^{\sigma+1}$ on $[a,b]$
-- statement:
--   Let $a, b$ be real numbers with $0 < a < b$, and let $s \in \mathbb{C}$ have positive real part $\sigma = \operatorname{Re}(s) > 0$. Then the function
--
--   $$u \;\longmapsto\; \frac{\left|\lfloor u\rfloor + \tfrac{1}{2} - u\right|}{u^{\sigma+1}}$$
--
--   is interval-integrable (with respect to Lebesgue measure) on the interval from $a$ to $b$, where $\lfloor u \rfloor$ denotes the floor of $u$.
--
--   This combines the measurability of the sawtooth quotient with its domination by the integrable majorant $1/u^{\sigma+1}$ on an interval bounded away from the origin. It licenses the Euler--Maclaurin error integral $\int (\lfloor x\rfloor + \tfrac12 - x)\, x^{-(s+1)}\, dx$ that appears in the truncated representation of $\zeta(s)$, the workhorse of the explicit zeta upper bounds in the PNT+ project.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L697-L705

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

theorem ZetaSum_aux1_5d {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  IntervalIntegrable (fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1)) MeasureTheory.volume a b := by sorry
